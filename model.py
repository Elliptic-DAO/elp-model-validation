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
    def __init__(self,current_collateral:Icp, eusd_circulating:float=0,fee_available:Icp=Icp(0),base_fee:float=0):
        self.current_collateral = current_collateral
        self.eusd_circulating = eusd_circulating
        self.fee_available  = fee_available
        self.base_fee=base_fee
        self.collateral_open_for_position = current_collateral
        self.levragers = []
        self.supporters = {}
        self.transactions = []

    @property
    def current_collateral_value(self):
        return self.current_collateral.to_eusd
    @property
    def collateral_ratio(self):
        return self.current_collateral_value/self.eusd_circulating if self.eusd_circulating else None

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
    @property
    def collateral_open_for_position(self):
        return self.current_collateral-sum([i['stability_assets'] for i in self.levragers ])
    
    def close_position(self):
        while not self.is_over_collateralized and self.levragers:
            self.levragers.remove(self.levragers.pop(0))

    @property
    def current_price(self):
        return Icp.current_value
    
    def calculate_fee(self,input_amount:Icp)->Icp:
        return Icp(input_amount*self.percentage_fee+self.base_fee) if isinstance(input_amount,Icp) else Icp(Icp(input_amount/Icp.current_value)*self.percentage_fee+self.base_fee)
    
    def burnt(self,amount_eusd):
        if amount_eusd<=self.eusd_circulating:
            self.eusd_circulating-=amount_eusd
        else:
            self.eusd_circulating = 0
    def mint(self,amount_eusd):
        self.eusd_circulating+=amount_eusd
    

class Levrager:
    def __init__(self,protocol:Protocol,levrager_assets:Icp,stability_assets:Icp):
        self.protocol = protocol
        self.levrager_assets = levrager_assets
        self.stability_assets = stability_assets
        self.current_icp = levrager_assets
        self.position_open = False

    @property
    def roi(self):
        return self.levrager_assets + self.stability_assets*(1-(self.initial_price/self.protocol.current_price))
    @property
    def to_liquidate(self):
        return self.protocol.current_price<self.liquidation_price
    
    
    def open_position(self,stability_assets):
        if not self.position_open:
            self.stability_assets = stability_assets
            if self.protocol.collateral_open_for_position >= self.stability_assets:
                self.initial_price = Icp.current_value
                self.liquidation_price = self.initial_price*self.stability_assets/(self.stability_assets+self.levrager_assets)
                self.levrage = (self.levrager_assets+self.stability_assets)/self.levrager_assets
                self.protocol.levragers.append({'user':self,'liquidation_price':self.liquidation_price,'leverage':self.levrage,'stability_assets':self.stability_assets})
                self.protocol.current_collateral+=self.levrager_assets
                self.position_open = True
                self.current_icp = 0
            else:
                raise ValueError(f"You can't open this position cause {self.protocol.current_collateral} icp are currently available for leverage")
            
    def close_position(self):
        if self.position_open:
            if not self.to_liquidate:
                self.protocol.current_collateral-= self.roi
                fee = self.protocol.calculate_fee(self.roi)
                self.protocol.fee_available+=fee
                self.current_icp += self.roi-fee
                self.levrager_assets = self.current_icp
                self.position_open = False
        else:
            raise ValueError('No open position')
    

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
        self.transactions = dict()
    @property
    def voting_power(self):
        return (self.elp_stacked+self.elp_yield)*self.dissolve_delay*self.age_bonus

    def provide_liquidity(self,amount:Icp):
        if amount>0:
            self.protocol.current_collateral += amount
            if self not in self.protocol.supporters:
                self.protocol.supporters.add(self)
            self.transactions[f'provide_liq_{len(self.transactions)+1}'] = amount
            self.protocol.transactions.append({'action':"support","user":self.__hash__(),'amount':{'icp':amount,'eusd':amount.to_eusd},'collateral':self.protocol.current_collateral,'icp_value':Icp.current_value,'collateral_ration':self.protocol.collateral_ratio})

       


class StableSeeker:
    def __init__(self,protocol:Protocol,icp:Icp=Icp(0)):
        self.protocol = protocol
        self.icp_spend = 0
        self.current_eusd = 0
        self.current_icp = icp
        self.dollars_spend = icp.to_eusd
        self.transactions = {"add_to_wallet":[],"depose_icp":[],"withdraw_icp":[]}

    def add_icp_to_wallet(self,icp:Icp):
        self.current_icp+=icp
        self.dollars_spend+= icp.to_eusd
        self.transactions["add_to_wallet"].append({f'{len(self.transactions["add_to_wallet"])+1}':{'icp':icp,'eUSD':icp.to_eusd,'icp_value':Icp.current_value}})

    def depose_icp_to_protocol(self,amount:Icp):
        if amount>self.current_icp:
            self.add_icp_to_wallet(amount-self.current_icp)
        
        self.icp_spend+=amount
        self.current_icp-= amount
        self.protocol.current_collateral+=amount
        fee = self.protocol.calculate_fee(amount)
        self.protocol.fee_available+=fee 
        self.current_eusd += amount.to_eusd-fee.to_eusd
        self.protocol.mint(amount.to_eusd-fee.to_eusd) 
        self.transactions["depose_icp"].append({f'{len(self.transactions["depose_icp"])+1}':{'icp':amount,'eUSD':amount.to_eusd,'icp_value':Icp.current_value}})
        self.protocol.transactions.append({'action':"depose","user":self.__hash__(),'amount':{'icp':amount,'eusd':amount.to_eusd},'fee':fee,'collateral':self.protocol.current_collateral,'icp_value':Icp.current_value,'collateral_ration':self.protocol.collateral_ratio})

        
    def withdraw_icp_from_protocol(self,amount:float):
        
        if amount<=self.current_eusd:
            self.current_eusd-=amount
            self.protocol.current_collateral-=Icp(amount/Icp.current_value)
            fee = self.protocol.calculate_fee(amount)
            self.protocol.fee_available+=fee
            self.current_icp+=Icp((amount-fee)/Icp.current_value)  
            self.protocol.burnt(amount)
            self.transactions["withdraw_icp"].append({f'{len(self.transactions["withdraw_icp"])+1}':{'icp':Icp(amount/Icp.current_value),'eUSD':amount,'icp_value':Icp.current_value}})
            self.protocol.transactions.append({'action':"withdraw","user_id":self.__hash__(),'amount':{'icp':Icp(amount/Icp.current_value),'eUSD':amount},'fee':fee,'collateral':self.protocol.current_collateral,'icp_value':Icp.current_value,'collateral_ration':self.protocol.collateral_ratio})
        else:
            raise ValueError('Cannot whithdraw more than what you have in your wallet')

