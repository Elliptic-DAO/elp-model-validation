---- MODULE squares ----
EXTENDS Naturals, Reals, TLC,Sequences,FiniteSets

(* --algorithm TestProtocol { 

(* declaration of global variables *)
variables 
    current_collateral = 500;
    circulating_supply = 1000;
    icp_value = 5;
    fee_available = 0;
    base_fee = 0;
    stability_asset_price = 10;
    levrager_assets = {};
    levrager_stability_assets = 0;
    positions = {};
    supporters = {};

(* process template *)
process (Update_Positions = 1) 
    variable p = 0;
{
    Update_Positions_Start:
        while (Cardinality(positions)<10) {
                p := p+1;
                positions := positions \union {Cardinality(positions)};
        }
}
process (Update_Position = 2) 
    variable p = 0;
{
    Update_Position_Start:
        while (Cardinality(positions)>5) {
                p := p+1;
                supporters := supporters \union {Cardinality(supporters)};
        }
}
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "8428c716" /\ chksum(tla) = "ee04da74")
\* Process variable p of process Update_Positions at line 21 col 14 changed to p_
VARIABLES current_collateral, circulating_supply, icp_value, fee_available, 
          base_fee, stability_asset_price, levrager_assets, 
          levrager_stability_assets, positions, supporters, pc, p_, p

vars == << current_collateral, circulating_supply, icp_value, fee_available, 
           base_fee, stability_asset_price, levrager_assets, 
           levrager_stability_assets, positions, supporters, pc, p_, p >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ current_collateral = 500
        /\ circulating_supply = 1000
        /\ icp_value = 5
        /\ fee_available = 0
        /\ base_fee = 0
        /\ stability_asset_price = 10
        /\ levrager_assets = {}
        /\ levrager_stability_assets = 0
        /\ positions = {}
        /\ supporters = {}
        (* Process Update_Positions *)
        /\ p_ = 0
        (* Process Update_Position *)
        /\ p = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "Update_Positions_Start"
                                        [] self = 2 -> "Update_Position_Start"]

Update_Positions_Start == /\ pc[1] = "Update_Positions_Start"
                          /\ IF Cardinality(positions)<10
                                THEN /\ p_' = p_+1
                                     /\ positions' = (positions \union {Cardinality(positions)})
                                     /\ pc' = [pc EXCEPT ![1] = "Update_Positions_Start"]
                                ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                                     /\ UNCHANGED << positions, p_ >>
                          /\ UNCHANGED << current_collateral, 
                                          circulating_supply, icp_value, 
                                          fee_available, base_fee, 
                                          stability_asset_price, 
                                          levrager_assets, 
                                          levrager_stability_assets, 
                                          supporters, p >>

Update_Positions == Update_Positions_Start

Update_Position_Start == /\ pc[2] = "Update_Position_Start"
                         /\ IF Cardinality(positions)>5
                               THEN /\ p' = p+1
                                    /\ supporters' = (supporters \union {Cardinality(supporters)})
                                    /\ pc' = [pc EXCEPT ![2] = "Update_Position_Start"]
                               ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
                                    /\ UNCHANGED << supporters, p >>
                         /\ UNCHANGED << current_collateral, 
                                         circulating_supply, icp_value, 
                                         fee_available, base_fee, 
                                         stability_asset_price, 
                                         levrager_assets, 
                                         levrager_stability_assets, positions, 
                                         p_ >>

Update_Position == Update_Position_Start

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Update_Positions \/ Update_Position
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
Inv_Positions == Cardinality(supporters)<10 
====
