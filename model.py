icp_value = 5
class Icp(float):
    current_value = icp_value
    def __init__(self,value):
        self.value = value
    def __add__(self, o):
        return Icp(self.value + o.value)
    def __sub__(self, o):
        return Icp(self.value - o.value)
    def print(self):
        print(f'{self.value} ICP = {self.to_eusd} eUSD')
    @property
    def to_eusd(self):
        return self.value*Icp.current_value
class Protocol:
    def __init__(self,current_collateral:Icp, issued_eusd:float=0,fee_available:Icp=Icp(0),base_fee:float=0):
        self.current_collateral = current_collateral
        self.issued_eusd = issued_eusd
        self.fee_available  = fee_available
        self.base_fee=base_fee
        self.supporters = {}
    @property
    def current_price(self):
        return Icp.current_value
    @property
    def current_collateral_value(self):
        return self.current_collateral.to_eusd
    @property
    def collateral_ratio(self):
        return self.current_collateral_value/self.issued_eusd if self.issued_eusd else None

    @property
    def is_over_collateralized(self):
        return self.collateral_ratio>1

    @property
    def percentage_fee(self):
        if self.collateral_ratio<80:
            return 0.025
        if self.collateral_ratio>120:
            return 0
        return 2.5*(120-self.collateral_ratio)/40
    def calculate_fee(self,input_amount:Icp)->Icp:
        return Icp(input_amount*self.percentage_fee+self.base_fee) if isinstance(input_amount,Icp) else Icp(Icp(input_amount/Icp.current_value)*self.percentage_fee+self.base_fee)

    def burnt(self,amount_eusd):
        if amount_eusd<=self.issued_eusd:
            self.issued_eusd-=amount_eusd
    def mint(self,amount_eusd):
        self.issued_eusd+=amount_eusd


class Levrager:
    def __init__(self,protocol:Protocol,levrager_assets:Icp,stability_assets:Icp):
        self.protocol = protocol
        self.levrager_assets = levrager_assets
        self.stability_assets = stability_assets
        self.initial_price = Icp.current_value
        self.protocol.fee_available+= self.protocol(levrager_assets)
        self.liquidation_price = self.initial_price*self.stability_assets/(self.stability_assets+self.levrager_assets)

    @property
    def roi(self):
        return self.levrager_assets + self.stability_assets*(1-(self.initial_price/self.protocol.current_price))
    @property
    def to_liquidate(self):
        return self.protocol.current_price<self.liquidation_price
    
    def __cash_out(self): 
        return self.protocol.current_collateral - self.stability_assets*(1-(self.initial_price/self.protocol.current_price))
    def close_position(self):
        if self.to_liquidate:
            self.protocol.current_collateral+=self.levrager_assets
        else:
            self.__cash_out()
    

class CollateralSupporter:
    def __init__(self,protocol:Protocol,elp_stacked,elp_yield,dissolve_delay,age_bonus):
        self.protocol = protocol
        self.elp_stacked=elp_stacked
        self.elp_yield=elp_yield
        self.dissolve_delay=dissolve_delay
        self.age_bonus=age_bonus
        self.spend_icp=0
        self.spend_dollars = 0
        self.reward_from_protocol = 0
    @property
    def voting_power(self):
        return (self.elp_stacked+self.elp_yield)*self.dissolve_delay*self.age_bonus

    def provide_liquidity(self,amount:Icp):
        if amount>0:
            self.protocol.current_collateral += amount
            if self not in self.protocol.supporters:
                self.protocol.supporters.add(self)

       


class StableSeeker:
    def __init__(self,protocol:Protocol,icp:Icp=Icp(0)):
        self.protocol = protocol
        self.icp_spend = 0
        self.current_eusd = 0
        self.current_icp = icp
        self.dollars_spend = icp.to_eusd

    def add_icp_to_wallet(self,icp:Icp):
        self.current_icp+=icp
        self.icp_spend+=icp
        self.dollars_spend+= icp.to_eusd

    def depose_icp_to_protocol(self,amount:Icp):
        if amount>self.current_icp:
            self.add_icp_to_wallet(amount-self.current_icp)
        self.current_icp-= amount
        self.protocol.current_collateral+=amount
        fee = self.protocol.calculate_fee(amount)
        self.protocol.fee_available+=fee 
        self.current_eusd += amount.to_eusd-fee.to_eusd
        self.protocol.mint(self.current_eusd) 

        
    def withdraw_icp_from_protocol(self,amount:float):
        
        if amount<=self.current_eusd:
            self.current_eusd-=amount
            self.protocol.current_collateral-=Icp(amount/Icp.current_value)
            fee = self.protocol.calculate_fee(amount)
            self.protocol.fee_available+=fee
            self.current_icp+=Icp((amount-fee)/Icp.current_value)  
            self.protocol.burnt(amount)
        else:
            raise ValueError('Cannot whithdraw more than what you have in your wallet')

