------------------------------ MODULE p2p_TYP ------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANT BALANCE, AMOUNT, 
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
  registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]], 
  periodicEnergyBids = [b \in Buyers |-> PeriodicBidList],
  
  bid = 0, \* For usage with registerMarketSellOrder
  validBuyers, test = 0,
  price = 0;

(* Invariant Proposals
(1) Prevent Attacks
(2) Consistent Transaction
*)
define
  SafeWithdrawal == 
      \/ (bankBalance=BALANCE-AMOUNT)
      
\*  ValidateBuyer(registry) == \A buyers \in registry: registry[buyers] = [TRUE, 1]
      
end define;

macro getEnergyBid(validBuyers, h, bid, price)
begin
     with x \in validBuyers do
        test := test + x;
        bid := periodicEnergyBids[x][1][2];
        price := periodicEnergyBids[x][2][2];
        print <<"Bid:",bid,"Price:",price,"Buyers:", test>>;
    end with;
end macro;

macro ValidateBuyer(Buyers, registry)
begin

   validBuyers := {p \in Buyers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
end macro;

macro registerMarketBuyOrder (Buyers, registry) 
begin
    \* validate the registry again to see if there is non-validated buyers
    ValidateBuyer(Buyers,registry);
\*    validBuyers := registry \in {Buyers \in {registry -> [valid == TRUE, reputation > 0]}};
  getEnergyBid (validBuyers, 2, bid, price);
  print <<"Bid:",bid,"Price:",price>>;
end macro;

\* macro that registers prosumers -- maps it to registry
macro registerAccount(Buyers)
begin
    registry := [x \in Buyers |-> [valid |-> FALSE, reputation |-> 0]];
end macro

macro validateAccount(Buyers)
begin
      registry := [x \in Buyers |-> [valid |-> TRUE, reputation |-> registry[x].reputation + 1]];
end macro

begin
  register_buyer:
     registerAccount(Buyers); \*register buyers
  validate_buyer: 
    validateAccount(Buyers);   \*validate buyers
  buy_energy:
    registerMarketBuyOrder(Buyers, registry);
  doPrintSell:
   
\*    test := \A buyers \in validBuyers:
\*        bid := periodicEnergyBids[buyers][1][2];
\*        price := periodicEnergyBids[buyers][2][3];
\*        print <<"Bid:",bid,"Price:",price,"Buyers:", test>>;
    



end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "11aadac9" /\ chksum(tla) = "11682673")
CONSTANT defaultInitValue
VARIABLES attack, bankBalance, registry, periodicEnergyBids, bid, validBuyers, 
          test, price, pc

(* define statement *)
SafeWithdrawal ==
    \/ (bankBalance=BALANCE-AMOUNT)


vars == << attack, bankBalance, registry, periodicEnergyBids, bid, 
           validBuyers, test, price, pc >>

Init == (* Global variables *)
        /\ attack = 0
        /\ bankBalance = BALANCE
        /\ registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]]
        /\ periodicEnergyBids = [b \in Buyers |-> PeriodicBidList]
        /\ bid = 0
        /\ validBuyers = defaultInitValue
        /\ test = 0
        /\ price = 0
        /\ pc = "register_buyer"

register_buyer == /\ pc = "register_buyer"
                  /\ registry' = [x \in Buyers |-> [valid |-> FALSE, reputation |-> 0]]
                  /\ pc' = "validate_buyer"
                  /\ UNCHANGED << attack, bankBalance, periodicEnergyBids, bid, 
                                  validBuyers, test, price >>

validate_buyer == /\ pc = "validate_buyer"
                  /\ registry' = [x \in Buyers |-> [valid |-> TRUE, reputation |-> registry[x].reputation + 1]]
                  /\ pc' = "buy_energy"
                  /\ UNCHANGED << attack, bankBalance, periodicEnergyBids, bid, 
                                  validBuyers, test, price >>

buy_energy == /\ pc = "buy_energy"
              /\ validBuyers' = {p \in Buyers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
              /\ PrintT(<<"Bid:",bid,"Price:",price>>)
              /\ pc' = "doPrintSell"
              /\ UNCHANGED << attack, bankBalance, registry, 
                              periodicEnergyBids, bid, test, price >>

doPrintSell == /\ pc = "doPrintSell"
               /\ \E x \in validBuyers:
                    /\ test' = test + x
                    /\ bid' = periodicEnergyBids[x][1][2]
                    /\ price' = periodicEnergyBids[x][2][2]
                    /\ PrintT(<<"Bid:",bid',"Price:",price',"Buyers:", test'>>)
               /\ pc' = "Done"
               /\ UNCHANGED << attack, bankBalance, registry, 
                               periodicEnergyBids, validBuyers >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == register_buyer \/ validate_buyer \/ buy_energy \/ doPrintSell
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

\*

=============================================================================
\* Modification History
\* Last modified Thu Dec 14 10:39:51 GMT 2023 by naufa
\* Created Thu Nov 16 09:31:42 GMT 2023 by naufa
