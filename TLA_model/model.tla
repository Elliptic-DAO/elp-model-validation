---- MODULE model ----
EXTENDS TLC, Sequences, Reals, Integers, FiniteSets, FiniteSetsExt, SequencesExt, Functions


add_liquidity(provider_id, amount) == [ 
    type |-> "provide ", provider_id |-> provider_id,amount |-> amount
]
add_swapper(swapper_id, amount,withdraw) == [ 
    type |-> withdraw, swapper_id |-> swapper_id,amount_eusd |-> amount
]
add_leverager(leverager_id, lev_collateral,position_assets,icp_value) == [
    leverager_id|->leverager_id, lev_collateral |->lev_collateral, leverage|-> (lev_collateral+position_assets) \div lev_collateral, liquidation_price |->  (position_assets*icp_value) \div (lev_collateral+position_assets)
]
comp_collateral_ratio(cr_value,eusd) == (cr_value*100) \div eusd
(* --algorithm TestProtocol { 

(* declaration of global variables *)
variables 
    current_collateral = 800;
    open_to_position = 800;
    icp_value = 5;
    eusd_circulating = 3000;
    fee_available = 0;
    base_fee = 0;

    supporters_id = {1,2,3,4};
    swapper_id = {1,2,3,4};
    leverager_id = {1,2,3,4};

    last_id = 0;

    
    swapper  = <<>>;
    leveragers = <<>>;
    swap = {1,2,3,4};
    withdraw = {};
    supporters = {};
    change = FALSE;
    collateral_ratio = comp_collateral_ratio(current_collateral*icp_value,eusd_circulating);

macro all_provider(provider_id,amount) {
    supporters := supporters \union {add_liquidity(provider_id, amount)};
}
macro all_swap(swapper_id,amount,withdraw){
    swapper := Append(swapper,add_swapper(swapper_id,amount,withdraw))
}
macro burn(amount){
    eusd_circulating := eusd_circulating-amount
}
macro mint(amount){
    eusd_circulating := eusd_circulating + amount
}
macro compute_cr(){
    collateral_ratio:= comp_collateral_ratio(current_collateral*icp_value,eusd_circulating)
}
(* process template *)
process (ICP = 1) 
{
    Update_Positions_Start:
        while (TRUE) {
            with (icp \in 1..5)
                if (icp_value-icp>0)
                    icp_value:=icp_value-icp;
                else 
                    icp_value:=icp_value+icp;
            compute_cr();}
}
process (PROV = 2)
{
    Provide_Liquidity:
        
        while (TRUE) {
            with(s_id \in supporters_id \ {last_id}){
                all_provider(s_id,2);
                last_id:=s_id;
                current_collateral := current_collateral+2;
                open_to_position := open_to_position+2;
                icp_value := icp_value + s_id; 
                compute_cr();}

                }

}
process(SWAP = 4){
    Swapper_process:
        while(TRUE){
            with(s_id \in swapper_id, amount \in 1..5){
                if (s_id \notin withdraw ){
                    all_swap(s_id,amount,"swap");
                    current_collateral := current_collateral + amount;
                    mint(amount*icp_value);
                    withdraw := withdraw \union {s_id};
                    compute_cr();
                }
                else{
                    all_swap(s_id,amount,"withdraw");
                    current_collateral := current_collateral - amount;
                    burn(amount*icp_value);
                    swap := swap \union {s_id};
                    compute_cr();
                }
                     
            }
        }
}

process(LEV = 5)
{
    leverager_process:
        while(TRUE){
            with(l_id \in leverager_id, lev_collateral \in 1..5, position_assets \in 1..15){
                current_collateral := current_collateral + lev_collateral;
                compute_cr();
                open_to_position := open_to_position - position_assets;
                leveragers := Append(leveragers,add_leverager(l_id,lev_collateral,position_assets,icp_value));
                
            }
        }
}

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "3c41b312" /\ chksum(tla) = "ef16c10f")
VARIABLES current_collateral, open_to_position, icp_value, eusd_circulating, 
          fee_available, base_fee, supporters_id, swapper_id, leverager_id, 
          last_id, swapper, leveragers, swap, withdraw, supporters, change, 
          collateral_ratio

vars == << current_collateral, open_to_position, icp_value, eusd_circulating, 
           fee_available, base_fee, supporters_id, swapper_id, leverager_id, 
           last_id, swapper, leveragers, swap, withdraw, supporters, change, 
           collateral_ratio >>

ProcSet == {1} \cup {2} \cup {4} \cup {5}

Init == (* Global variables *)
        /\ current_collateral = 800
        /\ open_to_position = 800
        /\ icp_value = 5
        /\ eusd_circulating = 3000
        /\ fee_available = 0
        /\ base_fee = 0
        /\ supporters_id = {1,2,3,4}
        /\ swapper_id = {1,2,3,4}
        /\ leverager_id = {1,2,3,4}
        /\ last_id = 0
        /\ swapper = <<>>
        /\ leveragers = <<>>
        /\ swap = {1,2,3,4}
        /\ withdraw = {}
        /\ supporters = {}
        /\ change = FALSE
        /\ collateral_ratio = comp_collateral_ratio(current_collateral*icp_value,eusd_circulating)

ICP == /\ \E icp \in 1..5:
            IF icp_value-icp>0
               THEN /\ icp_value' = icp_value-icp
               ELSE /\ icp_value' = icp_value+icp
       /\ collateral_ratio' = comp_collateral_ratio(current_collateral*icp_value',eusd_circulating)
       /\ UNCHANGED << current_collateral, open_to_position, eusd_circulating, 
                       fee_available, base_fee, supporters_id, swapper_id, 
                       leverager_id, last_id, swapper, leveragers, swap, 
                       withdraw, supporters, change >>

PROV == /\ \E s_id \in supporters_id \ {last_id}:
             /\ supporters' = (supporters \union {add_liquidity(s_id, 2)})
             /\ last_id' = s_id
             /\ current_collateral' = current_collateral+2
             /\ open_to_position' = open_to_position+2
             /\ icp_value' = icp_value + s_id
             /\ collateral_ratio' = comp_collateral_ratio(current_collateral'*icp_value',eusd_circulating)
        /\ UNCHANGED << eusd_circulating, fee_available, base_fee, 
                        supporters_id, swapper_id, leverager_id, swapper, 
                        leveragers, swap, withdraw, change >>

SWAP == /\ \E s_id \in swapper_id:
             \E amount \in 1..5:
               IF s_id \notin withdraw
                  THEN /\ swapper' = Append(swapper,add_swapper(s_id,amount,"swap"))
                       /\ current_collateral' = current_collateral + amount
                       /\ eusd_circulating' = eusd_circulating + (amount*icp_value)
                       /\ withdraw' = (withdraw \union {s_id})
                       /\ collateral_ratio' = comp_collateral_ratio(current_collateral'*icp_value,eusd_circulating')
                       /\ swap' = swap
                  ELSE /\ swapper' = Append(swapper,add_swapper(s_id,amount,"withdraw"))
                       /\ current_collateral' = current_collateral - amount
                       /\ eusd_circulating' = eusd_circulating-(amount*icp_value)
                       /\ swap' = (swap \union {s_id})
                       /\ collateral_ratio' = comp_collateral_ratio(current_collateral'*icp_value,eusd_circulating')
                       /\ UNCHANGED withdraw
        /\ UNCHANGED << open_to_position, icp_value, fee_available, base_fee, 
                        supporters_id, swapper_id, leverager_id, last_id, 
                        leveragers, supporters, change >>

LEV == /\ \E l_id \in leverager_id:
            \E lev_collateral \in 1..5:
              \E position_assets \in 1..15:
                /\ current_collateral' = current_collateral + lev_collateral
                /\ collateral_ratio' = comp_collateral_ratio(current_collateral'*icp_value,eusd_circulating)
                /\ open_to_position' = open_to_position - position_assets
                /\ leveragers' = Append(leveragers,add_leverager(l_id,lev_collateral,position_assets,icp_value))
       /\ UNCHANGED << icp_value, eusd_circulating, fee_available, base_fee, 
                       supporters_id, swapper_id, leverager_id, last_id, 
                       swapper, swap, withdraw, supporters, change >>

Next == ICP \/ PROV \/ SWAP \/ LEV

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

\* END TRANSLATION 
Inv_Positions == {s.provider_id: s \in supporters} /= {1}
Inv_Positions1 == Len(leveragers) < 3

====
