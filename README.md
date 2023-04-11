# elp-model-validation

This is a Python implementation of the Elliptic protocol described in the whitpaper. The model uses the following classes:

- Icp: represents the ICP with a variable exchange rate to eUSD.
- Protocol: represents the protocol that issues eUSD stablecoins backed by ICP collateral.
- Levrager: represents a user of the protocol who takes a leveraged position using ICP collateral.
- CollateralSupporter: represents a user of the protocol who provides ICP collateral to the protocol in exchange for fee and a voting power.
- StableSeeker: represents a user of the protocol who wants to obtain eUSD stablecoins by depositing ICP collateral.

## Usage
To use this model, you can create instances of the Protocol, Levrager, CollateralSupporter, and StableSeeker classes, and call their methods to perform operations such as 
minting eUSD stablecoins, taking a leveraged position, providing collateral, and withdrawing collateral.

For example, you can create a Protocol instance with an initial amount of ICP collateral and issue eUSD stablecoins:<br />
``` python
icp_value = 5 
protocol.mint(1000)
initial_collateral = Icp(100)
protocol = Protocol(current_collateral=initial_collateral)
```
You can also create a StableSeeker instance to deposit ICP collateral and obtain eUSD stablecoins:
```python user_collateral = Icp(10)
stable_seeker = StableSeeker(protocol=protocol, initial_price=icp_value, user_collateral=user_collateral)
stable_seeker.withdraw(50) #input eUSD
```
note that create a StableSeeker instance automatically add `current_collateral` to the protocol
