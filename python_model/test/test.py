from python_model.model import StableSeeker,Protocol,Icp
import unittest
class ElliptictTest(unittest.TestCase):
    def setUp(self) -> None:
        super().setUp()
        self.protocol = Protocol(Icp(30),100,base_fee=0)
         
    def test_collateral_ratio(self):
        assert(self.protocol.is_over_collateralized)
    def test_mint_burnt(self):
        self.protocol.mint(20)
        assert(self.protocol.issued_eusd==120)
        self.protocol.burnt(20)
        assert(self.protocol.issued_eusd==100)
    def test_current_value(self):
        Icp.current_value = 2
        assert(self.protocol.current_collateral_value==60)

    def test_add_stable_protocol(self): 
        stable1 = StableSeeker(self.protocol,Icp(20))
        stable2 = StableSeeker(self.protocol,Icp(20))
        stable1.depose_icp_to_protocol(Icp(20))
        stable2.depose_icp_to_protocol(Icp(20))
        assert(self.protocol.current_collateral==70)
        fee = self.protocol.calculate_fee(Icp(20))
        assert(stable1.current_eusd==100-fee.to_eusd)
        Icp.current_value = 10
        stable1.withdraw_icp_from_protocol(stable1.current_eusd)
        stable2.withdraw_icp_from_protocol(stable2.current_eusd)
        assert(self.protocol.current_collateral==50.5)
        print(self.protocol.collateral_ratio)
        
        

