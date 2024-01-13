--------------------------- MODULE p2p_TYP_conc1 ---------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANT BALANCE, AMOUNT, 
Buyers, Sellers,
EnergyOfferAmounts, EnergyOfferPrices,
EnergyBidAmounts, EnergyBidPrices,
EnergyBidAmountsSorted, EnergyBidPricesSorted, ReputationLimit


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
  periodicEnergyOffers = [s \in Sellers |-> PeriodicOfferList],
  
\*  bid = 0, offer = 0; \* For usage with registerMarketSellOrder
  validBuyers = {}, validSellers = {},
  test = 0, \*price= 0,
  clearingPrice = 0;

(* Invariant Proposals
(1) Prevent Attacks
(2) Consistent Transaction
*)
define
  SafeWithdrawal == 
      \/ (bankBalance > 0)
  (*Ensures that all sellers & buyers participating     are validated before market session ends*)
  BuyersValidated ==  
    \/ \A x \in validBuyers : x \in Buyers
  SellersValidated ==
   \/ \A x \in validSellers : x \in Sellers
end define;

macro matchingEnergy(periodicEnergyBids)
begin
    print <<"Dah Masuk Boi", validBuyers>>;
    \*hard code the sorting in descending order of the periodicEnergyBids
    periodicEnergyBids := [b \in validBuyers |-> <<EnergyBidAmountsSorted, EnergyBidPricesSorted>>];
  
    clearingPrice := 2; \*energy price determined 
end macro

macro getEnergyOffer(validSellers, h, bid, price)
begin
     with x \in validSellers do
        bid := periodicEnergyOffers[x][1][h];
        price := periodicEnergyOffers[x][2][h];
        print <<"Offers:",bid,"Price:",price,"Sellers:", x>>;
    end with;
end macro;

macro getEnergyBid(validBuyers, h, bid, price)
begin
     with x \in validBuyers do 
        bid := periodicEnergyBids[x][1][h];
        price := periodicEnergyBids[x][2][h];
        print <<"Bid:",bid,"Price:",price,"Buyers:", x>>;
    end with;
end macro;

(*----SELLERS/OFFERS SECTION------*)

macro ValidateSellers(Sellers, registry)
begin
   validSellers := {p \in Sellers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
end macro;

macro ValidateBuyer(Buyers, registry)
begin
   validBuyers := {p \in Buyers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
end macro;

procedure matching()
begin
 matching:
    \*add await that waits until all elements in validBuyers is present similar to the one in Buyers
    await validBuyers = {1,2,3};
    matchingEnergy(periodicEnergyBids);
    
 returnMatch:
  return;
end procedure;

procedure settlement()
begin
  settlement:
    await validBuyers = {4,5,6};
    bankBalance := BALANCE - AMOUNT;
    
    returnSettlement:
    return; 
end procedure;


procedure registerMarketSellOrder (pro) 
variables offer = 0;
          price = 0;
begin
    sellOrder:
    if registry[pro].reputation > ReputationLimit then
    \* validate the registry again to see if there is non-validated buyers
    ValidateSellers(Sellers,registry);
    await validSellers /= {};
    getEnergyOffer(validSellers, 2, offer, price);
    end if;
    
    FinishSellOrder:
    return;
end procedure;

\*procedure registerSellers(Seq3)
\*begin
\*    register_seller:
\*    registry := [p \in Prosumers |-> IF p \in Seq3 THEN [valid |-> FALSE, reputation |-> 0] ELSE p];
\*    return_seller:
\*    return;
\*end procedure;


(*----BUYERS/BIDDING SECTION------*)

procedure registerMarketBuyOrder (pro)
variables bid = 0; price = 0;

begin
  BuyOrder:
  if registry[pro].reputation > ReputationLimit then
    \* validate the registry again to see if there is non-validated buyers
    ValidateBuyer(Buyers,registry);
\*    validBuyers := registry \in {Buyers \in {registry -> [valid == TRUE, reputation > 0]}};
    await validBuyers /= {};
    getEnergyBid (validBuyers, 2, bid, price);
   end if;
    
  FinishBuyOrder:
  return;
end procedure;

procedure validateAccount(Sequence)
begin
      
      ValidateProsumer:
      registry[pro].reputation := registry[pro].reputation + 1;
\*      await Sequence /= <<>>;
\*      registry := [x \in Prosumers |-> IF x \in Sequence THEN [valid |-> TRUE, reputation |-> registry[x].reputation + 1] ELSE x];
      FinishValidate:
      return;
end procedure;

\* macro that registers prosumers -- maps it to registry
procedure registerAccount(pro)

begin
    RegisterProsumer:
    registry[pro] := [valid |-> TRUE, reputation |-> 0];
\*    registry := [p \in Prosumers |-> IF p \in Seq1 THEN [valid |-> FALSE, reputation |-> 0] ELSE p];
    FinishRegisterProsumer:
    return;
end procedure;

process buyer \in Buyers
variables
  other = CHOOSE x \in Prosumers: x /= self;
begin
  register_buyer:
     call registerAccount(self); \*register buyers
  validate_buyer: 
    call validateAccount(other);   \*validate buyers
  buy_energy:
    call registerMarketBuyOrder(self);
  matching1:
    call matching();
  settlement1:
    call settlement();
    
 end process;
 
process seller \in Sellers
variables
  other = CHOOSE x \in Prosumers: x /= self;
begin 
  register_seller:
    call registerAccount(self);
  validate:
    call validateAccount(other);
\*  validate_seller:
\*    call ValidateSellers(Sellers, registry);
  sell_energy:
    call registerMarketSellOrder(self);
  matching2:
    call matching();
  settlement2:
    call settlement();
 end process;


end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "b3bd9928" /\ chksum(tla) = "aa3d3425")
\* Label matching of procedure matching at line 95 col 5 changed to matching_
\* Label settlement of procedure settlement at line 105 col 5 changed to settlement_
\* Process variable other of process buyer at line 181 col 3 changed to other_
\* Procedure variable price of procedure registerMarketSellOrder at line 115 col 11 changed to price_
\* Parameter pro of procedure registerMarketSellOrder at line 113 col 36 changed to pro_
\* Parameter pro of procedure registerMarketBuyOrder at line 140 col 35 changed to pro_r
CONSTANT defaultInitValue
VARIABLES attack, bankBalance, registry, periodicEnergyBids, 
          periodicEnergyOffers, validBuyers, validSellers, test, 
          clearingPrice, pc, stack

(* define statement *)
SafeWithdrawal ==
    \/ (bankBalance > 0)

BuyersValidated ==
  \/ \A x \in validBuyers : x \in Buyers
SellersValidated ==
 \/ \A x \in validSellers : x \in Sellers

VARIABLES pro_, offer, price_, pro_r, bid, price, Sequence, pro, other_, 
          other

vars == << attack, bankBalance, registry, periodicEnergyBids, 
           periodicEnergyOffers, validBuyers, validSellers, test, 
           clearingPrice, pc, stack, pro_, offer, price_, pro_r, bid, price, 
           Sequence, pro, other_, other >>

ProcSet == (Buyers) \cup (Sellers)

Init == (* Global variables *)
        /\ attack = 0
        /\ bankBalance = BALANCE
        /\ registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]]
        /\ periodicEnergyBids = [b \in Buyers |-> PeriodicBidList]
        /\ periodicEnergyOffers = [s \in Sellers |-> PeriodicOfferList]
        /\ validBuyers = {}
        /\ validSellers = {}
        /\ test = 0
        /\ clearingPrice = 0
        (* Procedure registerMarketSellOrder *)
        /\ pro_ = [ self \in ProcSet |-> defaultInitValue]
        /\ offer = [ self \in ProcSet |-> 0]
        /\ price_ = [ self \in ProcSet |-> 0]
        (* Procedure registerMarketBuyOrder *)
        /\ pro_r = [ self \in ProcSet |-> defaultInitValue]
        /\ bid = [ self \in ProcSet |-> 0]
        /\ price = [ self \in ProcSet |-> 0]
        (* Procedure validateAccount *)
        /\ Sequence = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure registerAccount *)
        /\ pro = [ self \in ProcSet |-> defaultInitValue]
        (* Process buyer *)
        /\ other_ = [self \in Buyers |-> CHOOSE x \in Prosumers: x /= self]
        (* Process seller *)
        /\ other = [self \in Sellers |-> CHOOSE x \in Prosumers: x /= self]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Buyers -> "register_buyer"
                                        [] self \in Sellers -> "register_seller"]

matching_(self) == /\ pc[self] = "matching_"
                   /\ validBuyers = {1,2,3}
                   /\ PrintT(<<"Dah Masuk Boi", validBuyers>>)
                   /\ periodicEnergyBids' = [b \in validBuyers |-> <<EnergyBidAmountsSorted, EnergyBidPricesSorted>>]
                   /\ clearingPrice' = 2
                   /\ pc' = [pc EXCEPT ![self] = "returnMatch"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyOffers, validBuyers, 
                                   validSellers, test, stack, pro_, offer, 
                                   price_, pro_r, bid, price, Sequence, pro, 
                                   other_, other >>

returnMatch(self) == /\ pc[self] = "returnMatch"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, test, 
                                     clearingPrice, pro_, offer, price_, pro_r, 
                                     bid, price, Sequence, pro, other_, other >>

matching(self) == matching_(self) \/ returnMatch(self)

settlement_(self) == /\ pc[self] = "settlement_"
                     /\ validBuyers = {4,5,6}
                     /\ bankBalance' = BALANCE - AMOUNT
                     /\ pc' = [pc EXCEPT ![self] = "returnSettlement"]
                     /\ UNCHANGED << attack, registry, periodicEnergyBids, 
                                     periodicEnergyOffers, validBuyers, 
                                     validSellers, test, clearingPrice, stack, 
                                     pro_, offer, price_, pro_r, bid, price, 
                                     Sequence, pro, other_, other >>

returnSettlement(self) == /\ pc[self] = "returnSettlement"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << attack, bankBalance, registry, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validSellers, test, clearingPrice, 
                                          pro_, offer, price_, pro_r, bid, 
                                          price, Sequence, pro, other_, other >>

settlement(self) == settlement_(self) \/ returnSettlement(self)

sellOrder(self) == /\ pc[self] = "sellOrder"
                   /\ IF registry[pro_[self]].reputation > ReputationLimit
                         THEN /\ validSellers' = {p \in Sellers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
                              /\ validSellers' /= {}
                              /\ \E x \in validSellers':
                                   /\ offer' = [offer EXCEPT ![self] = periodicEnergyOffers[x][1][2]]
                                   /\ price_' = [price_ EXCEPT ![self] = periodicEnergyOffers[x][2][2]]
                                   /\ PrintT(<<"Offers:",offer'[self],"Price:",price_'[self],"Sellers:", x>>)
                         ELSE /\ TRUE
                              /\ UNCHANGED << validSellers, offer, price_ >>
                   /\ pc' = [pc EXCEPT ![self] = "FinishSellOrder"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, test, clearingPrice, stack, 
                                   pro_, pro_r, bid, price, Sequence, pro, 
                                   other_, other >>

FinishSellOrder(self) == /\ pc[self] = "FinishSellOrder"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ offer' = [offer EXCEPT ![self] = Head(stack[self]).offer]
                         /\ price_' = [price_ EXCEPT ![self] = Head(stack[self]).price_]
                         /\ pro_' = [pro_ EXCEPT ![self] = Head(stack[self]).pro_]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << attack, bankBalance, registry, 
                                         periodicEnergyBids, 
                                         periodicEnergyOffers, validBuyers, 
                                         validSellers, test, clearingPrice, 
                                         pro_r, bid, price, Sequence, pro, 
                                         other_, other >>

registerMarketSellOrder(self) == sellOrder(self) \/ FinishSellOrder(self)

BuyOrder(self) == /\ pc[self] = "BuyOrder"
                  /\ IF registry[pro_r[self]].reputation > ReputationLimit
                        THEN /\ validBuyers' = {p \in Buyers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
                             /\ validBuyers' /= {}
                             /\ \E x \in validBuyers':
                                  /\ bid' = [bid EXCEPT ![self] = periodicEnergyBids[x][1][2]]
                                  /\ price' = [price EXCEPT ![self] = periodicEnergyBids[x][2][2]]
                                  /\ PrintT(<<"Bid:",bid'[self],"Price:",price'[self],"Buyers:", x>>)
                        ELSE /\ TRUE
                             /\ UNCHANGED << validBuyers, bid, price >>
                  /\ pc' = [pc EXCEPT ![self] = "FinishBuyOrder"]
                  /\ UNCHANGED << attack, bankBalance, registry, 
                                  periodicEnergyBids, periodicEnergyOffers, 
                                  validSellers, test, clearingPrice, stack, 
                                  pro_, offer, price_, pro_r, Sequence, pro, 
                                  other_, other >>

FinishBuyOrder(self) == /\ pc[self] = "FinishBuyOrder"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ bid' = [bid EXCEPT ![self] = Head(stack[self]).bid]
                        /\ price' = [price EXCEPT ![self] = Head(stack[self]).price]
                        /\ pro_r' = [pro_r EXCEPT ![self] = Head(stack[self]).pro_r]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << attack, bankBalance, registry, 
                                        periodicEnergyBids, 
                                        periodicEnergyOffers, validBuyers, 
                                        validSellers, test, clearingPrice, 
                                        pro_, offer, price_, Sequence, pro, 
                                        other_, other >>

registerMarketBuyOrder(self) == BuyOrder(self) \/ FinishBuyOrder(self)

ValidateProsumer(self) == /\ pc[self] = "ValidateProsumer"
                          /\ registry' = [registry EXCEPT ![pro[self]].reputation = registry[pro[self]].reputation + 1]
                          /\ pc' = [pc EXCEPT ![self] = "FinishValidate"]
                          /\ UNCHANGED << attack, bankBalance, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validSellers, test, clearingPrice, 
                                          stack, pro_, offer, price_, pro_r, 
                                          bid, price, Sequence, pro, other_, 
                                          other >>

FinishValidate(self) == /\ pc[self] = "FinishValidate"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ Sequence' = [Sequence EXCEPT ![self] = Head(stack[self]).Sequence]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << attack, bankBalance, registry, 
                                        periodicEnergyBids, 
                                        periodicEnergyOffers, validBuyers, 
                                        validSellers, test, clearingPrice, 
                                        pro_, offer, price_, pro_r, bid, price, 
                                        pro, other_, other >>

validateAccount(self) == ValidateProsumer(self) \/ FinishValidate(self)

RegisterProsumer(self) == /\ pc[self] = "RegisterProsumer"
                          /\ registry' = [registry EXCEPT ![pro[self]] = [valid |-> TRUE, reputation |-> 0]]
                          /\ pc' = [pc EXCEPT ![self] = "FinishRegisterProsumer"]
                          /\ UNCHANGED << attack, bankBalance, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validSellers, test, clearingPrice, 
                                          stack, pro_, offer, price_, pro_r, 
                                          bid, price, Sequence, pro, other_, 
                                          other >>

FinishRegisterProsumer(self) == /\ pc[self] = "FinishRegisterProsumer"
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ pro' = [pro EXCEPT ![self] = Head(stack[self]).pro]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << attack, bankBalance, registry, 
                                                periodicEnergyBids, 
                                                periodicEnergyOffers, 
                                                validBuyers, validSellers, 
                                                test, clearingPrice, pro_, 
                                                offer, price_, pro_r, bid, 
                                                price, Sequence, other_, other >>

registerAccount(self) == RegisterProsumer(self)
                            \/ FinishRegisterProsumer(self)

register_buyer(self) == /\ pc[self] = "register_buyer"
                        /\ /\ pro' = [pro EXCEPT ![self] = self]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "registerAccount",
                                                                    pc        |->  "validate_buyer",
                                                                    pro       |->  pro[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "RegisterProsumer"]
                        /\ UNCHANGED << attack, bankBalance, registry, 
                                        periodicEnergyBids, 
                                        periodicEnergyOffers, validBuyers, 
                                        validSellers, test, clearingPrice, 
                                        pro_, offer, price_, pro_r, bid, price, 
                                        Sequence, other_, other >>

validate_buyer(self) == /\ pc[self] = "validate_buyer"
                        /\ /\ Sequence' = [Sequence EXCEPT ![self] = other_[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "validateAccount",
                                                                    pc        |->  "buy_energy",
                                                                    Sequence  |->  Sequence[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "ValidateProsumer"]
                        /\ UNCHANGED << attack, bankBalance, registry, 
                                        periodicEnergyBids, 
                                        periodicEnergyOffers, validBuyers, 
                                        validSellers, test, clearingPrice, 
                                        pro_, offer, price_, pro_r, bid, price, 
                                        pro, other_, other >>

buy_energy(self) == /\ pc[self] = "buy_energy"
                    /\ /\ pro_r' = [pro_r EXCEPT ![self] = self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "registerMarketBuyOrder",
                                                                pc        |->  "matching1",
                                                                bid       |->  bid[self],
                                                                price     |->  price[self],
                                                                pro_r     |->  pro_r[self] ] >>
                                                            \o stack[self]]
                    /\ bid' = [bid EXCEPT ![self] = 0]
                    /\ price' = [price EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "BuyOrder"]
                    /\ UNCHANGED << attack, bankBalance, registry, 
                                    periodicEnergyBids, periodicEnergyOffers, 
                                    validBuyers, validSellers, test, 
                                    clearingPrice, pro_, offer, price_, 
                                    Sequence, pro, other_, other >>

matching1(self) == /\ pc[self] = "matching1"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "matching",
                                                            pc        |->  "settlement1" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "matching_"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, test, 
                                   clearingPrice, pro_, offer, price_, pro_r, 
                                   bid, price, Sequence, pro, other_, other >>

settlement1(self) == /\ pc[self] = "settlement1"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "settlement",
                                                              pc        |->  "Done" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "settlement_"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, test, 
                                     clearingPrice, pro_, offer, price_, pro_r, 
                                     bid, price, Sequence, pro, other_, other >>

buyer(self) == register_buyer(self) \/ validate_buyer(self)
                  \/ buy_energy(self) \/ matching1(self)
                  \/ settlement1(self)

register_seller(self) == /\ pc[self] = "register_seller"
                         /\ /\ pro' = [pro EXCEPT ![self] = self]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "registerAccount",
                                                                     pc        |->  "validate",
                                                                     pro       |->  pro[self] ] >>
                                                                 \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "RegisterProsumer"]
                         /\ UNCHANGED << attack, bankBalance, registry, 
                                         periodicEnergyBids, 
                                         periodicEnergyOffers, validBuyers, 
                                         validSellers, test, clearingPrice, 
                                         pro_, offer, price_, pro_r, bid, 
                                         price, Sequence, other_, other >>

validate(self) == /\ pc[self] = "validate"
                  /\ /\ Sequence' = [Sequence EXCEPT ![self] = other[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "validateAccount",
                                                              pc        |->  "sell_energy",
                                                              Sequence  |->  Sequence[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "ValidateProsumer"]
                  /\ UNCHANGED << attack, bankBalance, registry, 
                                  periodicEnergyBids, periodicEnergyOffers, 
                                  validBuyers, validSellers, test, 
                                  clearingPrice, pro_, offer, price_, pro_r, 
                                  bid, price, pro, other_, other >>

sell_energy(self) == /\ pc[self] = "sell_energy"
                     /\ /\ pro_' = [pro_ EXCEPT ![self] = self]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "registerMarketSellOrder",
                                                                 pc        |->  "matching2",
                                                                 offer     |->  offer[self],
                                                                 price_    |->  price_[self],
                                                                 pro_      |->  pro_[self] ] >>
                                                             \o stack[self]]
                     /\ offer' = [offer EXCEPT ![self] = 0]
                     /\ price_' = [price_ EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "sellOrder"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, test, 
                                     clearingPrice, pro_r, bid, price, 
                                     Sequence, pro, other_, other >>

matching2(self) == /\ pc[self] = "matching2"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "matching",
                                                            pc        |->  "settlement2" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "matching_"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, test, 
                                   clearingPrice, pro_, offer, price_, pro_r, 
                                   bid, price, Sequence, pro, other_, other >>

settlement2(self) == /\ pc[self] = "settlement2"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "settlement",
                                                              pc        |->  "Done" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "settlement_"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, test, 
                                     clearingPrice, pro_, offer, price_, pro_r, 
                                     bid, price, Sequence, pro, other_, other >>

seller(self) == register_seller(self) \/ validate(self)
                   \/ sell_energy(self) \/ matching2(self)
                   \/ settlement2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ matching(self) \/ settlement(self)
                               \/ registerMarketSellOrder(self)
                               \/ registerMarketBuyOrder(self)
                               \/ validateAccount(self)
                               \/ registerAccount(self))
           \/ (\E self \in Buyers: buyer(self))
           \/ (\E self \in Sellers: seller(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Jan 13 11:13:33 GMT 2024 by naufa
\* Created Fri Jan 05 10:01:04 GMT 2024 by naufa
