from model import StableSeeker,Protocol,Icp
import unittest
class ElliptictTest(unittest.TestCase):
    protocol = Protocol(Icp(30),100,base_fee=2)
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
        stable1 = StableSeeker(self.protocol,Icp.current_value,Icp(20))
        stable2 = StableSeeker(self.protocol,Icp.current_value,Icp(20))
        assert(self.protocol.current_collateral==70)
        assert(stable1.user_collateral_eusd==100)
        Icp.current_value = 10
        assert(stable1.ratio==2)
        stable1.withdraw(stable1.user_collateral_eusd)
        stable2.withdraw(stable2.user_collateral_eusd)
        assert(self.protocol.current_collateral==50)
        print(self.protocol.collateral_ratio)
        
        

