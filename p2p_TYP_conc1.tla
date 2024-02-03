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
  validBuyerWallet = {}, mapBuyerToSeller = {}, valBuyer,valSeller,
  clearingPrice = 0,
  
  temp = 0, flagValBuyer = [b \in validBuyers |-> FALSE];

(* Invariant Proposals
(1) Prevent Attacks
(2) Consistent Transaction
*)
define
    SafeWithdrawal == 
       (bankBalance > 6000)     
    
    (* Invariants that ensures that all sellers & buyers participating are validated before market session ends*)
    BuyersValidated ==  
    \/ \A x \in validBuyers : x \in Buyers
    
    SellersValidated ==
    \/ \A x \in validSellers : x \in Sellers

end define;

\*(* macro that: -shows the listings of energy that seller prosumers wants to sell for every hour
\*               -returns the energy bid amount submitted by to each seller prosumer 
\*               via the bid & price variable
\**)
\*macro matchingEnergy(periodicEnergyBids, pro)
\*begin
\*    
\*   skip;
\*end macro

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
\*        print <<"Offers:",bid,"Price:",price,"Sellers:",seller>>;
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
\*        print <<"Bid:",bid,"Price:",price,"Buyers:", buyer>>;
    end with;
end macro;


(*----Validation of Sellers and Buyers------*)
macro ValidateSellers(Sellers, registry, pro)
begin
\*   if pro \in registry then
\*    validSellers := {pro \in Sellers : registry[pro].valid = TRUE /\ registry[pro].reputation > 0}
      validSellers := validSellers \union {pro};
\*   end if;
end macro;

macro ValidateBuyer(Buyers, registry, pro)
begin
\*   validBuyers := {p \in Buyers : registry[p].valid = TRUE /\ registry[p].reputation > 0};
   validBuyers := validBuyers \union {pro};
   validBuyerWallet := [b \in validBuyers |-> bankBalance]; \* maps validated buyer to bankBalance -- means they can take part in the market session
end macro;

(* procedure that simulates the market's matching process 
*)
procedure matching(pro)
begin
 matching:
 
    await flagValBuyer /= << >>;
    if validBuyers /= {} then
    
     \*hardcode the sorting in descending order of the periodicEnergyBids
\*    await validBuyers /= {};
    sorting:
        if pro \in validBuyers then
            periodicEnergyBids[pro] := <<EnergyBidAmountsSorted, EnergyBidPricesSorted>>;
            clearingPrice := 1; \*energy price determined 
        end if;
        
    \*matching of buyers with prosumers (2B, 1S)
    selectBuyer:
         
      if validBuyers /= {} then
        with b \in validBuyers do
            flagValBuyer[b] := TRUE;
        end with;
      end if;
    
    criticalSection:
    print("KAT SINI");
    \*    await \A DOMAIN x \in flagValBuyer: flagValBuyer[x] = TRUE;
        temp:= CHOOSE buyer \in DOMAIN flagValBuyer: flagValBuyer[buyer] = TRUE;
        
        \*deduct buyers bankBalance
        validBuyerWallet[temp] := bankBalance - AMOUNT;
    
    \*reset flag to false
    resetCounter:
    flagValBuyer[temp] := FALSE; 
   end if;
    
 returnMatch:
  return;
end procedure;

(* procedure that simulates the market's settlement process 
*)
procedure settlement(pro)
begin
  
  settlement:
  if pro \in validSellers then validSellers := validSellers \ {pro}; end if;
  if pro \in validBuyers then validBuyers := validBuyers \ {pro}; end if;
  
\*   returnSettlement:
   return; 
end procedure;

(* procedure that simulates the market's sell process *)
procedure registerMarketSellOrder (pro) 
variables offer = 0;
          price = 0;
begin
    sellOrder:
    \* if a prosumer reputation count is greater than threshold, it can validate other prosumer
    if registry[pro].reputation >= ReputationLimit then 
    
        \* validate the prosumers again to see if there is non-validated buyers
        ValidateSellers(Sellers,registry, pro);
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
  if registry[pro].reputation >= ReputationLimit then
    
    \* validate the registry again to see if there is non-validated buyers
    ValidateBuyer(Buyers,registry, pro);

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
  test = {};
begin
  register_buyer:
     call registerAccount(self); \*register buyers
  validate_buyer: 
    call validateAccount(self);   \*validate buyers
  buy_energy:
    call registerMarketBuyOrder(self);
    Chill:
    if self \in validBuyers then
        flagValBuyer := [elem \in validBuyers |-> FALSE];
\*        print(flagValBuyer);
    end if;
  matching1:
    await validBuyers /= {};
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
    call validateAccount(self);
  sell_energy:
    call registerMarketSellOrder(self);
  matching2:
\*    await validSellers /= {};
\*    call matching(self);
      skip;
  settlement2:
\*     await validSellers = Sellers;
    call settlement(self);
 end process;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "f13bcb83" /\ chksum(tla) = "30b7e2a6")
\* Label matching of procedure matching at line 130 col 5 changed to matching_
\* Label settlement of procedure settlement at line 173 col 3 changed to settlement_
\* Process variable other of process buyer at line 250 col 3 changed to other_
\* Procedure variable price of procedure registerMarketSellOrder at line 183 col 11 changed to price_
\* Parameter pro of procedure matching at line 126 col 20 changed to pro_
\* Parameter pro of procedure settlement at line 169 col 22 changed to pro_s
\* Parameter pro of procedure registerMarketSellOrder at line 181 col 36 changed to pro_r
\* Parameter pro of procedure registerMarketBuyOrder at line 201 col 35 changed to pro_re
\* Parameter pro of procedure validateAccount at line 223 col 27 changed to pro_v
CONSTANT defaultInitValue
VARIABLES attack, bankBalance, registry, periodicEnergyBids, 
          periodicEnergyOffers, validBuyers, validSellers, validBuyerWallet, 
          mapBuyerToSeller, valBuyer, valSeller, clearingPrice, temp, 
          flagValBuyer, pc, stack

(* define statement *)
SafeWithdrawal ==
   (bankBalance > 6000)


BuyersValidated ==
\/ \A x \in validBuyers : x \in Buyers

SellersValidated ==
\/ \A x \in validSellers : x \in Sellers

VARIABLES pro_, pro_s, pro_r, offer, price_, pro_re, bid, price, pro_v, pro, 
          other_, test, other

vars == << attack, bankBalance, registry, periodicEnergyBids, 
           periodicEnergyOffers, validBuyers, validSellers, validBuyerWallet, 
           mapBuyerToSeller, valBuyer, valSeller, clearingPrice, temp, 
           flagValBuyer, pc, stack, pro_, pro_s, pro_r, offer, price_, pro_re, 
           bid, price, pro_v, pro, other_, test, other >>

ProcSet == (Buyers) \cup (Sellers)

Init == (* Global variables *)
        /\ attack = 0
        /\ bankBalance = BALANCE
        /\ registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]]
        /\ periodicEnergyBids = [b \in Buyers |-> PeriodicBidList]
        /\ periodicEnergyOffers = [s \in Sellers |-> PeriodicOfferList]
        /\ validBuyers = {}
        /\ validSellers = {}
        /\ validBuyerWallet = {}
        /\ mapBuyerToSeller = {}
        /\ valBuyer = defaultInitValue
        /\ valSeller = defaultInitValue
        /\ clearingPrice = 0
        /\ temp = 0
        /\ flagValBuyer = [b \in validBuyers |-> FALSE]
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
        /\ test = [self \in Buyers |-> {}]
        (* Process seller *)
        /\ other = [self \in Sellers |-> CHOOSE x \in Prosumers: x /= self]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Buyers -> "register_buyer"
                                        [] self \in Sellers -> "register_seller"]

matching_(self) == /\ pc[self] = "matching_"
                   /\ flagValBuyer /= << >>
                   /\ IF validBuyers /= {}
                         THEN /\ pc' = [pc EXCEPT ![self] = "sorting"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "returnMatch"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, validBuyerWallet, 
                                   mapBuyerToSeller, valBuyer, valSeller, 
                                   clearingPrice, temp, flagValBuyer, stack, 
                                   pro_, pro_s, pro_r, offer, price_, pro_re, 
                                   bid, price, pro_v, pro, other_, test, other >>

sorting(self) == /\ pc[self] = "sorting"
                 /\ IF pro_[self] \in validBuyers
                       THEN /\ periodicEnergyBids' = [periodicEnergyBids EXCEPT ![pro_[self]] = <<EnergyBidAmountsSorted, EnergyBidPricesSorted>>]
                            /\ clearingPrice' = 1
                       ELSE /\ TRUE
                            /\ UNCHANGED << periodicEnergyBids, clearingPrice >>
                 /\ pc' = [pc EXCEPT ![self] = "selectBuyer"]
                 /\ UNCHANGED << attack, bankBalance, registry, 
                                 periodicEnergyOffers, validBuyers, 
                                 validSellers, validBuyerWallet, 
                                 mapBuyerToSeller, valBuyer, valSeller, temp, 
                                 flagValBuyer, stack, pro_, pro_s, pro_r, 
                                 offer, price_, pro_re, bid, price, pro_v, pro, 
                                 other_, test, other >>

selectBuyer(self) == /\ pc[self] = "selectBuyer"
                     /\ IF validBuyers /= {}
                           THEN /\ \E b \in validBuyers:
                                     flagValBuyer' = [flagValBuyer EXCEPT ![b] = TRUE]
                           ELSE /\ TRUE
                                /\ UNCHANGED flagValBuyer
                     /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     stack, pro_, pro_s, pro_r, offer, price_, 
                                     pro_re, bid, price, pro_v, pro, other_, 
                                     test, other >>

criticalSection(self) == /\ pc[self] = "criticalSection"
                         /\ PrintT(("KAT SINI"))
                         /\ temp' = (CHOOSE buyer \in DOMAIN flagValBuyer: flagValBuyer[buyer] = TRUE)
                         /\ validBuyerWallet' = [validBuyerWallet EXCEPT ![temp'] = bankBalance - AMOUNT]
                         /\ pc' = [pc EXCEPT ![self] = "resetCounter"]
                         /\ UNCHANGED << attack, bankBalance, registry, 
                                         periodicEnergyBids, 
                                         periodicEnergyOffers, validBuyers, 
                                         validSellers, mapBuyerToSeller, 
                                         valBuyer, valSeller, clearingPrice, 
                                         flagValBuyer, stack, pro_, pro_s, 
                                         pro_r, offer, price_, pro_re, bid, 
                                         price, pro_v, pro, other_, test, 
                                         other >>

resetCounter(self) == /\ pc[self] = "resetCounter"
                      /\ flagValBuyer' = [flagValBuyer EXCEPT ![temp] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = "returnMatch"]
                      /\ UNCHANGED << attack, bankBalance, registry, 
                                      periodicEnergyBids, periodicEnergyOffers, 
                                      validBuyers, validSellers, 
                                      validBuyerWallet, mapBuyerToSeller, 
                                      valBuyer, valSeller, clearingPrice, temp, 
                                      stack, pro_, pro_s, pro_r, offer, price_, 
                                      pro_re, bid, price, pro_v, pro, other_, 
                                      test, other >>

returnMatch(self) == /\ pc[self] = "returnMatch"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ pro_' = [pro_ EXCEPT ![self] = Head(stack[self]).pro_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, pro_s, pro_r, offer, price_, 
                                     pro_re, bid, price, pro_v, pro, other_, 
                                     test, other >>

matching(self) == matching_(self) \/ sorting(self) \/ selectBuyer(self)
                     \/ criticalSection(self) \/ resetCounter(self)
                     \/ returnMatch(self)

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
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, pro_, pro_r, offer, price_, 
                                     pro_re, bid, price, pro_v, pro, other_, 
                                     test, other >>

settlement(self) == settlement_(self)

sellOrder(self) == /\ pc[self] = "sellOrder"
                   /\ IF registry[pro_r[self]].reputation >= ReputationLimit
                         THEN /\ validSellers' = (validSellers \union {pro_r[self]})
                              /\ validSellers' /= {}
                              /\ \E seller \in validSellers':
                                   /\ offer' = [offer EXCEPT ![self] = periodicEnergyOffers[seller][1][2]]
                                   /\ price_' = [price_ EXCEPT ![self] = periodicEnergyOffers[seller][2][2]]
                         ELSE /\ TRUE
                              /\ UNCHANGED << validSellers, offer, price_ >>
                   /\ pc' = [pc EXCEPT ![self] = "FinishSellOrder"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validBuyerWallet, 
                                   mapBuyerToSeller, valBuyer, valSeller, 
                                   clearingPrice, temp, flagValBuyer, stack, 
                                   pro_, pro_s, pro_r, pro_re, bid, price, 
                                   pro_v, pro, other_, test, other >>

FinishSellOrder(self) == /\ pc[self] = "FinishSellOrder"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ offer' = [offer EXCEPT ![self] = Head(stack[self]).offer]
                         /\ price_' = [price_ EXCEPT ![self] = Head(stack[self]).price_]
                         /\ pro_r' = [pro_r EXCEPT ![self] = Head(stack[self]).pro_r]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << attack, bankBalance, registry, 
                                         periodicEnergyBids, 
                                         periodicEnergyOffers, validBuyers, 
                                         validSellers, validBuyerWallet, 
                                         mapBuyerToSeller, valBuyer, valSeller, 
                                         clearingPrice, temp, flagValBuyer, 
                                         pro_, pro_s, pro_re, bid, price, 
                                         pro_v, pro, other_, test, other >>

registerMarketSellOrder(self) == sellOrder(self) \/ FinishSellOrder(self)

BuyOrder(self) == /\ pc[self] = "BuyOrder"
                  /\ IF registry[pro_re[self]].reputation >= ReputationLimit
                        THEN /\ validBuyers' = (validBuyers \union {pro_re[self]})
                             /\ validBuyerWallet' = [b \in validBuyers' |-> bankBalance]
                             /\ \E buyer \in validBuyers':
                                  /\ bid' = [bid EXCEPT ![self] = periodicEnergyBids[buyer][1][2]]
                                  /\ price' = [price EXCEPT ![self] = periodicEnergyBids[buyer][2][2]]
                        ELSE /\ TRUE
                             /\ UNCHANGED << validBuyers, validBuyerWallet, 
                                             bid, price >>
                  /\ pc' = [pc EXCEPT ![self] = "FinishBuyOrder"]
                  /\ UNCHANGED << attack, bankBalance, registry, 
                                  periodicEnergyBids, periodicEnergyOffers, 
                                  validSellers, mapBuyerToSeller, valBuyer, 
                                  valSeller, clearingPrice, temp, flagValBuyer, 
                                  stack, pro_, pro_s, pro_r, offer, price_, 
                                  pro_re, pro_v, pro, other_, test, other >>

FinishBuyOrder(self) == /\ pc[self] = "FinishBuyOrder"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ bid' = [bid EXCEPT ![self] = Head(stack[self]).bid]
                        /\ price' = [price EXCEPT ![self] = Head(stack[self]).price]
                        /\ pro_re' = [pro_re EXCEPT ![self] = Head(stack[self]).pro_re]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << attack, bankBalance, registry, 
                                        periodicEnergyBids, 
                                        periodicEnergyOffers, validBuyers, 
                                        validSellers, validBuyerWallet, 
                                        mapBuyerToSeller, valBuyer, valSeller, 
                                        clearingPrice, temp, flagValBuyer, 
                                        pro_, pro_s, pro_r, offer, price_, 
                                        pro_v, pro, other_, test, other >>

registerMarketBuyOrder(self) == BuyOrder(self) \/ FinishBuyOrder(self)

ValidateProsumer(self) == /\ pc[self] = "ValidateProsumer"
                          /\ registry' = [registry EXCEPT ![pro_v[self]].reputation = registry[pro_v[self]].reputation + 1]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ pro_v' = [pro_v EXCEPT ![self] = Head(stack[self]).pro_v]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << attack, bankBalance, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validSellers, validBuyerWallet, 
                                          mapBuyerToSeller, valBuyer, 
                                          valSeller, clearingPrice, temp, 
                                          flagValBuyer, pro_, pro_s, pro_r, 
                                          offer, price_, pro_re, bid, price, 
                                          pro, other_, test, other >>

validateAccount(self) == ValidateProsumer(self)

RegisterProsumer(self) == /\ pc[self] = "RegisterProsumer"
                          /\ registry' = [registry EXCEPT ![pro[self]] = [valid |-> TRUE, reputation |-> 0]]
                          /\ pc' = [pc EXCEPT ![self] = "FinishRegisterProsumer"]
                          /\ UNCHANGED << attack, bankBalance, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validSellers, validBuyerWallet, 
                                          mapBuyerToSeller, valBuyer, 
                                          valSeller, clearingPrice, temp, 
                                          flagValBuyer, stack, pro_, pro_s, 
                                          pro_r, offer, price_, pro_re, bid, 
                                          price, pro_v, pro, other_, test, 
                                          other >>

FinishRegisterProsumer(self) == /\ pc[self] = "FinishRegisterProsumer"
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ pro' = [pro EXCEPT ![self] = Head(stack[self]).pro]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << attack, bankBalance, registry, 
                                                periodicEnergyBids, 
                                                periodicEnergyOffers, 
                                                validBuyers, validSellers, 
                                                validBuyerWallet, 
                                                mapBuyerToSeller, valBuyer, 
                                                valSeller, clearingPrice, temp, 
                                                flagValBuyer, pro_, pro_s, 
                                                pro_r, offer, price_, pro_re, 
                                                bid, price, pro_v, other_, 
                                                test, other >>

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
                                        validSellers, validBuyerWallet, 
                                        mapBuyerToSeller, valBuyer, valSeller, 
                                        clearingPrice, temp, flagValBuyer, 
                                        pro_, pro_s, pro_r, offer, price_, 
                                        pro_re, bid, price, pro_v, other_, 
                                        test, other >>

validate_buyer(self) == /\ pc[self] = "validate_buyer"
                        /\ /\ pro_v' = [pro_v EXCEPT ![self] = self]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "validateAccount",
                                                                    pc        |->  "buy_energy",
                                                                    pro_v     |->  pro_v[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "ValidateProsumer"]
                        /\ UNCHANGED << attack, bankBalance, registry, 
                                        periodicEnergyBids, 
                                        periodicEnergyOffers, validBuyers, 
                                        validSellers, validBuyerWallet, 
                                        mapBuyerToSeller, valBuyer, valSeller, 
                                        clearingPrice, temp, flagValBuyer, 
                                        pro_, pro_s, pro_r, offer, price_, 
                                        pro_re, bid, price, pro, other_, test, 
                                        other >>

buy_energy(self) == /\ pc[self] = "buy_energy"
                    /\ /\ pro_re' = [pro_re EXCEPT ![self] = self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "registerMarketBuyOrder",
                                                                pc        |->  "Chill",
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
                                    validBuyerWallet, mapBuyerToSeller, 
                                    valBuyer, valSeller, clearingPrice, temp, 
                                    flagValBuyer, pro_, pro_s, pro_r, offer, 
                                    price_, pro_v, pro, other_, test, other >>

Chill(self) == /\ pc[self] = "Chill"
               /\ IF self \in validBuyers
                     THEN /\ flagValBuyer' = [elem \in validBuyers |-> FALSE]
                     ELSE /\ TRUE
                          /\ UNCHANGED flagValBuyer
               /\ pc' = [pc EXCEPT ![self] = "matching1"]
               /\ UNCHANGED << attack, bankBalance, registry, 
                               periodicEnergyBids, periodicEnergyOffers, 
                               validBuyers, validSellers, validBuyerWallet, 
                               mapBuyerToSeller, valBuyer, valSeller, 
                               clearingPrice, temp, stack, pro_, pro_s, pro_r, 
                               offer, price_, pro_re, bid, price, pro_v, pro, 
                               other_, test, other >>

matching1(self) == /\ pc[self] = "matching1"
                   /\ validBuyers /= {}
                   /\ /\ pro_' = [pro_ EXCEPT ![self] = self]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "matching",
                                                               pc        |->  "settlement1",
                                                               pro_      |->  pro_[self] ] >>
                                                           \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "matching_"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, validBuyerWallet, 
                                   mapBuyerToSeller, valBuyer, valSeller, 
                                   clearingPrice, temp, flagValBuyer, pro_s, 
                                   pro_r, offer, price_, pro_re, bid, price, 
                                   pro_v, pro, other_, test, other >>

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
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, pro_, pro_r, offer, price_, 
                                     pro_re, bid, price, pro_v, pro, other_, 
                                     test, other >>

buyer(self) == register_buyer(self) \/ validate_buyer(self)
                  \/ buy_energy(self) \/ Chill(self) \/ matching1(self)
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
                                         validSellers, validBuyerWallet, 
                                         mapBuyerToSeller, valBuyer, valSeller, 
                                         clearingPrice, temp, flagValBuyer, 
                                         pro_, pro_s, pro_r, offer, price_, 
                                         pro_re, bid, price, pro_v, other_, 
                                         test, other >>

validate(self) == /\ pc[self] = "validate"
                  /\ /\ pro_v' = [pro_v EXCEPT ![self] = self]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "validateAccount",
                                                              pc        |->  "sell_energy",
                                                              pro_v     |->  pro_v[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "ValidateProsumer"]
                  /\ UNCHANGED << attack, bankBalance, registry, 
                                  periodicEnergyBids, periodicEnergyOffers, 
                                  validBuyers, validSellers, validBuyerWallet, 
                                  mapBuyerToSeller, valBuyer, valSeller, 
                                  clearingPrice, temp, flagValBuyer, pro_, 
                                  pro_s, pro_r, offer, price_, pro_re, bid, 
                                  price, pro, other_, test, other >>

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
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, pro_, pro_s, pro_re, bid, 
                                     price, pro_v, pro, other_, test, other >>

matching2(self) == /\ pc[self] = "matching2"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "settlement2"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, validBuyerWallet, 
                                   mapBuyerToSeller, valBuyer, valSeller, 
                                   clearingPrice, temp, flagValBuyer, stack, 
                                   pro_, pro_s, pro_r, offer, price_, pro_re, 
                                   bid, price, pro_v, pro, other_, test, other >>

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
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, pro_, pro_r, offer, price_, 
                                     pro_re, bid, price, pro_v, pro, other_, 
                                     test, other >>

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
                                 /\ WF_vars(settlement(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Feb 03 09:30:07 GMT 2024 by naufa
\* Created Fri Jan 05 10:01:04 GMT 2024 by naufa
