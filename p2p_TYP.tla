------------------------------ MODULE p2p_TYP ------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANT BALANCE, AMOUNT, Auctions, 
Buyers, Sellers,
EnergyOfferAmounts, EnergyOfferPrices,
EnergyBidAmounts, EnergyBidPrices


\*EnergyOfferAmounts == 0, EnergyOfferPrices = 0,
\*EnergyBidAmounts = 0, EnergyBidPrices = 0

\* single bid, multiple offer, offerers

Prosumers == Buyers \cup Sellers
ListedAmount == 1
ListedPrice == 2
PeriodicOfferList == <<EnergyOfferAmounts, EnergyOfferPrices>>
PeriodicBidList == <<EnergyBidAmounts, EnergyBidPrices>>
(* PeriodicOfferList[ListedAmounts][2] -- EnergyOffers at 2nd hour
   PeriodicOfferList[ListedPrices][3] -- EnergyPrices at 3rd hour
*)


(*--algorithm p2p_TYP
variables
  attack = 0, \*how many attack we do we want to model
  bankBalance = BALANCE,
  registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]];


(* Invariant Proposals
(1) Prevent Attacks
(2) Consistent Transaction??
*)
define
  SafeWithdrawal == 
      \/ (bankBalance=BALANCE-AMOUNT)
end define;


macro registerAccount(pro)
begin
     registry[pro] := [valid |-> TRUE, reputation |-> 0];
end macro

macro validateAccount(pro)
begin
      registry[pro].reputation := registry[pro].reputation + 1;
end macro

begin
  register_buyer:
    registerAccount(Prosumers);
  validate_seller:
    validateAccount(Prosumers);



end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e9facd5a" /\ chksum(tla) = "fef4536f")
VARIABLES attack, bankBalance, registry, pc

(* define statement *)
SafeWithdrawal ==
    \/ (bankBalance=BALANCE-AMOUNT)


vars == << attack, bankBalance, registry, pc >>

Init == (* Global variables *)
        /\ attack = 0
        /\ bankBalance = BALANCE
        /\ registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]]
        /\ pc = "register_buyer"

register_buyer == /\ pc = "register_buyer"
                  /\ registry' = [registry EXCEPT ![Prosumers] = [valid |-> TRUE, reputation |-> 0]]
                  /\ pc' = "validate_seller"
                  /\ UNCHANGED << attack, bankBalance >>

validate_seller == /\ pc = "validate_seller"
                   /\ registry' = [registry EXCEPT ![Prosumers].reputation = registry[Prosumers].reputation + 1]
                   /\ pc' = "Done"
                   /\ UNCHANGED << attack, bankBalance >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == register_buyer \/ validate_seller
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Nov 22 10:34:37 GMT 2023 by naufa
\* Created Thu Nov 16 09:31:42 GMT 2023 by naufa
