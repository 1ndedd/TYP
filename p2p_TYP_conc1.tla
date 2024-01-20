--------------------------- MODULE p2p_TYP_conc1 ---------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANT BALANCE, AMOUNT, 
Buyers, Sellers,
EnergyOfferAmounts, EnergyOfferPrices,
EnergyBidAmounts, EnergyBidPrices,
EnergyBidAmountsSorted, EnergyBidPricesSorted, ReputationLimit


\* single bid, multiple offer, offerers

Prosumers == Buyers \cup Sellers
ListedAmount == 1
ListedPrice == 2
PeriodicOfferList == <<EnergyOfferAmounts, EnergyOfferPrices>>
PeriodicBidList == <<EnergyBidAmounts, EnergyBidPrices>>
(* PeriodicOfferList[ListedAmounts][2] -- EnergyOffers at 2nd hour
   PeriodicOfferList[ListedPrices][3] -- EnergyPrices at 3rd hour
*)


(* LIST OF GLOBAL VARIABLES
    - attack = total attacks/ we try to model
    -bankBalance = The prosumer's bank account balance -- SET AS CONSTANT
    
    -registry = A structure variable that maps prosumers (acts as a key) to another structure that has:
                valid - for validation process of prosumer
                reputation - prosumer's reputation value
    
    -periodicEnergyBids = Function maps buyers to listing of bids submitted by them
    -periodicEnergyOffers = Function maps seller to listing of offers submitted by them
    -validBuyers & validSellers - Set that holds validated prosumer
*)


(*--algorithm p2p_TYP
variables
  attack = 0, \*how many attack we do we want to model
  bankBalance = BALANCE,
  registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]],  
  periodicEnergyBids = [b \in Buyers |-> PeriodicBidList],
  periodicEnergyOffers = [s \in Sellers |-> PeriodicOfferList],
  
  validBuyers = {}, validSellers = {},
  mapBuyerToSeller = <<>>,
  clearingPrice = 0;

(* Invariant Proposals
(1) Prevent Attacks
(2) Consistent Transaction
*)
define
    SafeWithdrawal == 
      \/ (bankBalance > 6000)     
    
    (* Invariants that ensures that all sellers & buyers participating are validated before market session ends*)
    BuyersValidated ==  
    \/ \A x \in validBuyers : x \in Buyers
    
    SellersValidated ==
    \/ \A x \in validSellers : x \in Sellers

end define;


(* macro that: -shows the listings of energy that seller prosumers wants to sell for every hour
               -returns the energy bid amount submitted by to each seller prosumer 
               via the bid & price variable
*)
macro matchingEnergy(periodicEnergyBids, pro)
begin
    
    \*hardcode the sorting in descending order of the periodicEnergyBids
    if pro \in validBuyers then
        
        periodicEnergyBids := [b \in validBuyers |-> <<EnergyBidAmountsSorted, EnergyBidPricesSorted>>];
        clearingPrice := 2; \*energy price determined 
    end if;
    
    
    \* deduct the balance from buyer's money    
    bankBalance := bankBalance - AMOUNT; 
    
\*    assert bankBalance > 6000; ADDED ASSERTION
end macro

(* macro that: -shows the listings of energy that buyer prosumers wants to buy energy for every hour
               -returns the energy bid amount submitted by to each seller prosumer 
               via the bid & price variable
*)
macro getEnergyOffer(validSellers, h, bid, price)
begin
        \*if prosumer is a seller and validated, it can submit offers -- hardcode since its an implementation
    
     with seller \in validSellers do
        bid := periodicEnergyOffers[seller][1][h];
        price := periodicEnergyOffers[seller][2][h];
        print <<"Offers:",bid,"Price:",price,"Sellers:",seller>>;
    end with;
end macro;

(* macro that: -shows the listings of energy that seller prosumers wants to sell for every hour
               -returns the energy bid amount submitted by to each seller prosumer 
               via the bid & price variable
*)
macro getEnergyBid(validBuyers, h, bid, price)
begin
        \*if prosumer is a buyer and validated, it can submit bids -- hardcode since its an implementation
    
     with buyer \in validBuyers do 
        bid := periodicEnergyBids[buyer][1][h];
        price := periodicEnergyBids[buyer][2][h];
        print <<"Bid:",bid,"Price:",price,"Buyers:", buyer>>;
    end with;
end macro;


(*----Validation of Sellers and Buyers------*)
macro ValidateSellers(Sellers, registry)
begin
   validSellers := {p \in Sellers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
end macro;

macro ValidateBuyer(Buyers, registry)
begin
   validBuyers := {p \in Buyers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
end macro;

(* procedure that simulates the market's matching process 
*)
procedure matching(pro)
begin
 matching:
    
    matchingEnergy(periodicEnergyBids, pro);
    
\* returnMatch:
  return;
end procedure;

(* procedure that simulates the market's settlement process 
*)
procedure settlement(pro)
begin
  
  settlement:
  if pro \in validSellers then validSellers := validSellers \ {pro}; end if;
  if pro \in validBuyers then validBuyers := validBuyers \ {pro};
  end if;
  
\*   returnSettlement:
   return; 
end procedure;

(* procedure that simulates the market's sell process 
*)
procedure registerMarketSellOrder (pro) 
variables offer = 0;
          price = 0;
begin
    sellOrder:
    \* if a prosumer reputation count is greater than threshold, it can validate other prosumer
    if registry[pro].reputation > ReputationLimit then 
    
        \* validate the prosumers again to see if there is non-validated buyers
        ValidateSellers(Sellers,registry);
        await validSellers /= {};
        getEnergyOffer(validSellers, 2, offer, price);
    end if;
    
    FinishSellOrder:
    return;
end procedure;

(* procedure that simulates the market's buying process 
*)
procedure registerMarketBuyOrder (pro)
variables bid = 0; price = 0;

begin
  BuyOrder:
  \* if a prosumer reputation count is greater than threshold, it can validate other prosumer
  if registry[pro].reputation > ReputationLimit then
    
    \* validate the registry again to see if there is non-validated buyers
    ValidateBuyer(Buyers,registry);

\*    validBuyers := registry \in {Buyers \in {registry -> [valid == TRUE, reputation > 0]}};

    getEnergyBid (validBuyers, 2, bid, price);
   end if;
    
  FinishBuyOrder:
  return;
end procedure;

(* procedure that validates prosumers -- increments reputation by 1
*)
procedure validateAccount(pro)
begin
      
      ValidateProsumer:
      registry[pro].reputation := registry[pro].reputation + 1;

\*      await Sequence /= <<>>;
\*      registry := [x \in Prosumers |-> IF x \in Sequence THEN [valid |-> TRUE, reputation |-> registry[x].reputation + 1] ELSE x];
  
      return;
end procedure;

(* procedure that registers prosumers -- sets valid to true and reputation value is zero
*)
procedure registerAccount(pro)
begin
    RegisterProsumer:
    registry[pro] := [valid |-> TRUE, reputation |-> 0];

\*    registry := [p \in Prosumers |-> IF p \in Seq1 THEN [valid |-> FALSE, reputation |-> 0] ELSE p];
    
    FinishRegisterProsumer:
    return;
end procedure;

fair process buyer \in Buyers
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
    call matching(self);
  settlement1:
    call settlement(self);
 end process;
 
fair process seller \in Sellers
variables
  other = CHOOSE x \in Prosumers: x /= self;
begin 
  register_seller:
    call registerAccount(self);
  validate:
    call validateAccount(other);
  sell_energy:
    call registerMarketSellOrder(self);
  matching2:
\*    await validBuyers = Buyers;
    call matching(self);
  settlement2:
\*     await validSellers = Sellers;
    call settlement(self);
 end process;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "56d1bd5c" /\ chksum(tla) = "b6277d89")
\* Label matching of procedure matching at line 74 col 5 changed to matching_
\* Label settlement of procedure settlement at line 147 col 3 changed to settlement_
\* Process variable other of process buyer at line 226 col 3 changed to other_
\* Procedure variable price of procedure registerMarketSellOrder at line 159 col 11 changed to price_
\* Parameter pro of procedure matching at line 131 col 20 changed to pro_
\* Parameter pro of procedure settlement at line 143 col 22 changed to pro_s
\* Parameter pro of procedure registerMarketSellOrder at line 157 col 36 changed to pro_r
\* Parameter pro of procedure registerMarketBuyOrder at line 177 col 35 changed to pro_re
\* Parameter pro of procedure validateAccount at line 199 col 27 changed to pro_v
CONSTANT defaultInitValue
VARIABLES attack, bankBalance, registry, periodicEnergyBids, 
          periodicEnergyOffers, validBuyers, validSellers, mapBuyerToSeller, 
          clearingPrice, pc, stack

(* define statement *)
SafeWithdrawal ==
  \/ (bankBalance > 6000)


BuyersValidated ==
\/ \A x \in validBuyers : x \in Buyers

SellersValidated ==
\/ \A x \in validSellers : x \in Sellers

VARIABLES pro_, pro_s, pro_r, offer, price_, pro_re, bid, price, pro_v, pro, 
          other_, other

vars == << attack, bankBalance, registry, periodicEnergyBids, 
           periodicEnergyOffers, validBuyers, validSellers, mapBuyerToSeller, 
           clearingPrice, pc, stack, pro_, pro_s, pro_r, offer, price_, 
           pro_re, bid, price, pro_v, pro, other_, other >>

ProcSet == (Buyers) \cup (Sellers)

Init == (* Global variables *)
        /\ attack = 0
        /\ bankBalance = BALANCE
        /\ registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]]
        /\ periodicEnergyBids = [b \in Buyers |-> PeriodicBidList]
        /\ periodicEnergyOffers = [s \in Sellers |-> PeriodicOfferList]
        /\ validBuyers = {}
        /\ validSellers = {}
        /\ mapBuyerToSeller = <<>>
        /\ clearingPrice = 0
        (* Procedure matching *)
        /\ pro_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure settlement *)
        /\ pro_s = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure registerMarketSellOrder *)
        /\ pro_r = [ self \in ProcSet |-> defaultInitValue]
        /\ offer = [ self \in ProcSet |-> 0]
        /\ price_ = [ self \in ProcSet |-> 0]
        (* Procedure registerMarketBuyOrder *)
        /\ pro_re = [ self \in ProcSet |-> defaultInitValue]
        /\ bid = [ self \in ProcSet |-> 0]
        /\ price = [ self \in ProcSet |-> 0]
        (* Procedure validateAccount *)
        /\ pro_v = [ self \in ProcSet |-> defaultInitValue]
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
                   /\ IF pro_[self] \in validBuyers
                         THEN /\ periodicEnergyBids' = [b \in validBuyers |-> <<EnergyBidAmountsSorted, EnergyBidPricesSorted>>]
                              /\ clearingPrice' = 2
                         ELSE /\ TRUE
                              /\ UNCHANGED << periodicEnergyBids, 
                                              clearingPrice >>
                   /\ bankBalance' = bankBalance - AMOUNT
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ pro_' = [pro_ EXCEPT ![self] = Head(stack[self]).pro_]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << attack, registry, periodicEnergyOffers, 
                                   validBuyers, validSellers, mapBuyerToSeller, 
                                   pro_s, pro_r, offer, price_, pro_re, bid, 
                                   price, pro_v, pro, other_, other >>

matching(self) == matching_(self)

settlement_(self) == /\ pc[self] = "settlement_"
                     /\ IF pro_s[self] \in validSellers
                           THEN /\ validSellers' = validSellers \ {pro_s[self]}
                           ELSE /\ TRUE
                                /\ UNCHANGED validSellers
                     /\ IF pro_s[self] \in validBuyers
                           THEN /\ validBuyers' = validBuyers \ {pro_s[self]}
                           ELSE /\ TRUE
                                /\ UNCHANGED validBuyers
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ pro_s' = [pro_s EXCEPT ![self] = Head(stack[self]).pro_s]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     mapBuyerToSeller, clearingPrice, pro_, 
                                     pro_r, offer, price_, pro_re, bid, price, 
                                     pro_v, pro, other_, other >>

settlement(self) == settlement_(self)

sellOrder(self) == /\ pc[self] = "sellOrder"
                   /\ IF registry[pro_r[self]].reputation > ReputationLimit
                         THEN /\ validSellers' = {p \in Sellers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
                              /\ validSellers' /= {}
                              /\ \E seller \in validSellers':
                                   /\ offer' = [offer EXCEPT ![self] = periodicEnergyOffers[seller][1][2]]
                                   /\ price_' = [price_ EXCEPT ![self] = periodicEnergyOffers[seller][2][2]]
                                   /\ PrintT(<<"Offers:",offer'[self],"Price:",price_'[self],"Sellers:",seller>>)
                         ELSE /\ TRUE
                              /\ UNCHANGED << validSellers, offer, price_ >>
                   /\ pc' = [pc EXCEPT ![self] = "FinishSellOrder"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, mapBuyerToSeller, 
                                   clearingPrice, stack, pro_, pro_s, pro_r, 
                                   pro_re, bid, price, pro_v, pro, other_, 
                                   other >>

FinishSellOrder(self) == /\ pc[self] = "FinishSellOrder"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ offer' = [offer EXCEPT ![self] = Head(stack[self]).offer]
                         /\ price_' = [price_ EXCEPT ![self] = Head(stack[self]).price_]
                         /\ pro_r' = [pro_r EXCEPT ![self] = Head(stack[self]).pro_r]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << attack, bankBalance, registry, 
                                         periodicEnergyBids, 
                                         periodicEnergyOffers, validBuyers, 
                                         validSellers, mapBuyerToSeller, 
                                         clearingPrice, pro_, pro_s, pro_re, 
                                         bid, price, pro_v, pro, other_, other >>

registerMarketSellOrder(self) == sellOrder(self) \/ FinishSellOrder(self)

BuyOrder(self) == /\ pc[self] = "BuyOrder"
                  /\ IF registry[pro_re[self]].reputation > ReputationLimit
                        THEN /\ validBuyers' = {p \in Buyers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
                             /\ \E buyer \in validBuyers':
                                  /\ bid' = [bid EXCEPT ![self] = periodicEnergyBids[buyer][1][2]]
                                  /\ price' = [price EXCEPT ![self] = periodicEnergyBids[buyer][2][2]]
                                  /\ PrintT(<<"Bid:",bid'[self],"Price:",price'[self],"Buyers:", buyer>>)
                        ELSE /\ TRUE
                             /\ UNCHANGED << validBuyers, bid, price >>
                  /\ pc' = [pc EXCEPT ![self] = "FinishBuyOrder"]
                  /\ UNCHANGED << attack, bankBalance, registry, 
                                  periodicEnergyBids, periodicEnergyOffers, 
                                  validSellers, mapBuyerToSeller, 
                                  clearingPrice, stack, pro_, pro_s, pro_r, 
                                  offer, price_, pro_re, pro_v, pro, other_, 
                                  other >>

FinishBuyOrder(self) == /\ pc[self] = "FinishBuyOrder"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ bid' = [bid EXCEPT ![self] = Head(stack[self]).bid]
                        /\ price' = [price EXCEPT ![self] = Head(stack[self]).price]
                        /\ pro_re' = [pro_re EXCEPT ![self] = Head(stack[self]).pro_re]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << attack, bankBalance, registry, 
                                        periodicEnergyBids, 
                                        periodicEnergyOffers, validBuyers, 
                                        validSellers, mapBuyerToSeller, 
                                        clearingPrice, pro_, pro_s, pro_r, 
                                        offer, price_, pro_v, pro, other_, 
                                        other >>

registerMarketBuyOrder(self) == BuyOrder(self) \/ FinishBuyOrder(self)

ValidateProsumer(self) == /\ pc[self] = "ValidateProsumer"
                          /\ registry' = [registry EXCEPT ![pro_v[self]].reputation = registry[pro_v[self]].reputation + 1]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ pro_v' = [pro_v EXCEPT ![self] = Head(stack[self]).pro_v]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << attack, bankBalance, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validSellers, mapBuyerToSeller, 
                                          clearingPrice, pro_, pro_s, pro_r, 
                                          offer, price_, pro_re, bid, price, 
                                          pro, other_, other >>

validateAccount(self) == ValidateProsumer(self)

RegisterProsumer(self) == /\ pc[self] = "RegisterProsumer"
                          /\ registry' = [registry EXCEPT ![pro[self]] = [valid |-> TRUE, reputation |-> 0]]
                          /\ pc' = [pc EXCEPT ![self] = "FinishRegisterProsumer"]
                          /\ UNCHANGED << attack, bankBalance, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validSellers, mapBuyerToSeller, 
                                          clearingPrice, stack, pro_, pro_s, 
                                          pro_r, offer, price_, pro_re, bid, 
                                          price, pro_v, pro, other_, other >>

FinishRegisterProsumer(self) == /\ pc[self] = "FinishRegisterProsumer"
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ pro' = [pro EXCEPT ![self] = Head(stack[self]).pro]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << attack, bankBalance, registry, 
                                                periodicEnergyBids, 
                                                periodicEnergyOffers, 
                                                validBuyers, validSellers, 
                                                mapBuyerToSeller, 
                                                clearingPrice, pro_, pro_s, 
                                                pro_r, offer, price_, pro_re, 
                                                bid, price, pro_v, other_, 
                                                other >>

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
                                        validSellers, mapBuyerToSeller, 
                                        clearingPrice, pro_, pro_s, pro_r, 
                                        offer, price_, pro_re, bid, price, 
                                        pro_v, other_, other >>

validate_buyer(self) == /\ pc[self] = "validate_buyer"
                        /\ /\ pro_v' = [pro_v EXCEPT ![self] = other_[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "validateAccount",
                                                                    pc        |->  "buy_energy",
                                                                    pro_v     |->  pro_v[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "ValidateProsumer"]
                        /\ UNCHANGED << attack, bankBalance, registry, 
                                        periodicEnergyBids, 
                                        periodicEnergyOffers, validBuyers, 
                                        validSellers, mapBuyerToSeller, 
                                        clearingPrice, pro_, pro_s, pro_r, 
                                        offer, price_, pro_re, bid, price, pro, 
                                        other_, other >>

buy_energy(self) == /\ pc[self] = "buy_energy"
                    /\ /\ pro_re' = [pro_re EXCEPT ![self] = self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "registerMarketBuyOrder",
                                                                pc        |->  "matching1",
                                                                bid       |->  bid[self],
                                                                price     |->  price[self],
                                                                pro_re    |->  pro_re[self] ] >>
                                                            \o stack[self]]
                    /\ bid' = [bid EXCEPT ![self] = 0]
                    /\ price' = [price EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "BuyOrder"]
                    /\ UNCHANGED << attack, bankBalance, registry, 
                                    periodicEnergyBids, periodicEnergyOffers, 
                                    validBuyers, validSellers, 
                                    mapBuyerToSeller, clearingPrice, pro_, 
                                    pro_s, pro_r, offer, price_, pro_v, pro, 
                                    other_, other >>

matching1(self) == /\ pc[self] = "matching1"
                   /\ /\ pro_' = [pro_ EXCEPT ![self] = self]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "matching",
                                                               pc        |->  "settlement1",
                                                               pro_      |->  pro_[self] ] >>
                                                           \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "matching_"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, mapBuyerToSeller, 
                                   clearingPrice, pro_s, pro_r, offer, price_, 
                                   pro_re, bid, price, pro_v, pro, other_, 
                                   other >>

settlement1(self) == /\ pc[self] = "settlement1"
                     /\ /\ pro_s' = [pro_s EXCEPT ![self] = self]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "settlement",
                                                                 pc        |->  "Done",
                                                                 pro_s     |->  pro_s[self] ] >>
                                                             \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "settlement_"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     mapBuyerToSeller, clearingPrice, pro_, 
                                     pro_r, offer, price_, pro_re, bid, price, 
                                     pro_v, pro, other_, other >>

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
                                         validSellers, mapBuyerToSeller, 
                                         clearingPrice, pro_, pro_s, pro_r, 
                                         offer, price_, pro_re, bid, price, 
                                         pro_v, other_, other >>

validate(self) == /\ pc[self] = "validate"
                  /\ /\ pro_v' = [pro_v EXCEPT ![self] = other[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "validateAccount",
                                                              pc        |->  "sell_energy",
                                                              pro_v     |->  pro_v[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "ValidateProsumer"]
                  /\ UNCHANGED << attack, bankBalance, registry, 
                                  periodicEnergyBids, periodicEnergyOffers, 
                                  validBuyers, validSellers, mapBuyerToSeller, 
                                  clearingPrice, pro_, pro_s, pro_r, offer, 
                                  price_, pro_re, bid, price, pro, other_, 
                                  other >>

sell_energy(self) == /\ pc[self] = "sell_energy"
                     /\ /\ pro_r' = [pro_r EXCEPT ![self] = self]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "registerMarketSellOrder",
                                                                 pc        |->  "matching2",
                                                                 offer     |->  offer[self],
                                                                 price_    |->  price_[self],
                                                                 pro_r     |->  pro_r[self] ] >>
                                                             \o stack[self]]
                     /\ offer' = [offer EXCEPT ![self] = 0]
                     /\ price_' = [price_ EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "sellOrder"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     mapBuyerToSeller, clearingPrice, pro_, 
                                     pro_s, pro_re, bid, price, pro_v, pro, 
                                     other_, other >>

matching2(self) == /\ pc[self] = "matching2"
                   /\ /\ pro_' = [pro_ EXCEPT ![self] = self]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "matching",
                                                               pc        |->  "settlement2",
                                                               pro_      |->  pro_[self] ] >>
                                                           \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "matching_"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, mapBuyerToSeller, 
                                   clearingPrice, pro_s, pro_r, offer, price_, 
                                   pro_re, bid, price, pro_v, pro, other_, 
                                   other >>

settlement2(self) == /\ pc[self] = "settlement2"
                     /\ /\ pro_s' = [pro_s EXCEPT ![self] = self]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "settlement",
                                                                 pc        |->  "Done",
                                                                 pro_s     |->  pro_s[self] ] >>
                                                             \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "settlement_"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     mapBuyerToSeller, clearingPrice, pro_, 
                                     pro_r, offer, price_, pro_re, bid, price, 
                                     pro_v, pro, other_, other >>

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

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Buyers : /\ WF_vars(buyer(self))
                                /\ WF_vars(registerAccount(self))
                                /\ WF_vars(validateAccount(self))
                                /\ WF_vars(registerMarketBuyOrder(self))
                                /\ WF_vars(matching(self))
                                /\ WF_vars(settlement(self))
        /\ \A self \in Sellers : /\ WF_vars(seller(self))
                                 /\ WF_vars(registerAccount(self))
                                 /\ WF_vars(validateAccount(self))
                                 /\ WF_vars(registerMarketSellOrder(self))
                                 /\ WF_vars(matching(self))
                                 /\ WF_vars(settlement(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Jan 20 19:54:58 GMT 2024 by naufa
\* Created Fri Jan 05 10:01:04 GMT 2024 by naufa
