---- MODULE model ----
EXTENDS TLC, Sequences, Integers, FiniteSets, FiniteSetsExt, SequencesExt, Functions


add_liquidity(provider_id, amount) == [ 
    type |-> "provide ", provider_id |-> provider_id,amount |-> amount
]

(* --algorithm TestProtocol { 

(* declaration of global variables *)
variables 
    current_collateral = 500;
    circulating_supply = 1000;
    icp_value = 5;
    fee_available = 0;
    base_fee = 0;
    levragers_id = {};
    supporters_id = {};
    swapper_id = {};
    positions = {};
    levrager_stability_assets = 0;
    supporters = <<>>;
macro all_provider(provider_id,amount) {
    supporters := Append(supporters,add_liquidity(provider_id, amount));
}

(* process template *)
process (ICP = 1) 
    variable p = 0;
{
    Update_Positions_Start:
        while (TRUE) {
            with (icp \in 1..5)
                if (icp_value-icp>0)
                    icp_value:=icp_value-icp;
                else 
                    icp_value:=icp_value+icp;
                    current_collateral := current_collateral+p;
                p := p+1;
                positions := positions \union {Cardinality(positions)};
        }
}
process (providers = 2)
{
    Provide_Liquidity:
        while (current_collateral<520) {
            all_provider(1,2);
            current_collateral := current_collateral+2;
}
}} *)
\* BEGIN TRANSLATION (chksum(pcal) = "9a6a07fb" /\ chksum(tla) = "91cd4718")
VARIABLES current_collateral, circulating_supply, icp_value, fee_available, 
          base_fee, levragers_id, supporters_id, swapper_id, positions, 
          levrager_stability_assets, supporters, pc, p

vars == << current_collateral, circulating_supply, icp_value, fee_available, 
           base_fee, levragers_id, supporters_id, swapper_id, positions, 
           levrager_stability_assets, supporters, pc, p >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ current_collateral = 500
        /\ circulating_supply = 1000
        /\ icp_value = 5
        /\ fee_available = 0
        /\ base_fee = 0
        /\ levragers_id = {}
        /\ supporters_id = {}
        /\ swapper_id = {}
        /\ positions = {}
        /\ levrager_stability_assets = 0
        /\ supporters = <<>>
        (* Process ICP *)
        /\ p = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "Update_Positions_Start"
                                        [] self = 2 -> "Provide_Liquidity"]

Update_Positions_Start == /\ pc[1] = "Update_Positions_Start"
                          /\ \E icp \in 1..5:
                               IF icp_value-icp>0
                                  THEN /\ icp_value' = icp_value-icp
                                  ELSE /\ icp_value' = icp_value+icp
                          /\ current_collateral' = current_collateral+p
                          /\ p' = p+1
                          /\ positions' = (positions \union {Cardinality(positions)})
                          /\ pc' = [pc EXCEPT ![1] = "Update_Positions_Start"]
                          /\ UNCHANGED << circulating_supply, fee_available, 
                                          base_fee, levragers_id, 
                                          supporters_id, swapper_id, 
                                          levrager_stability_assets, 
                                          supporters >>

ICP == Update_Positions_Start

Provide_Liquidity == /\ pc[2] = "Provide_Liquidity"
                     /\ IF current_collateral<520
                           THEN /\ supporters' = Append(supporters,add_liquidity(1, 2))
                                /\ current_collateral' = current_collateral+2
                                /\ pc' = [pc EXCEPT ![2] = "Provide_Liquidity"]
                           ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
                                /\ UNCHANGED << current_collateral, supporters >>
                     /\ UNCHANGED << circulating_supply, icp_value, 
                                     fee_available, base_fee, levragers_id, 
                                     supporters_id, swapper_id, positions, 
                                     levrager_stability_assets, p >>

providers == Provide_Liquidity

Next == ICP \/ providers

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
Inv_Positions == current_collateral <550
Inv_Positions1 == Len(supporters)<5
====
