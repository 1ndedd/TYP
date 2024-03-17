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
  
  validBuyers = {}, validSellers = {}, validBuyers_copy = Buyers, validSellers_copy = Sellers,
  validBuyerWallet = [b \in Buyers |-> 0], mapBuyerToSeller = [b \in Buyers |-> 0], valBuyer,valSeller,
  clearingPrice = 0,
  
  temp = 0, flagValBuyer = [b \in Buyers |-> FALSE],
  
  finalValBuyer = [b \in Buyers |-> 0], flagBuyers = FALSE, flagSellers = FALSE,
  BuyerState = [b \in Buyers |-> "Start"];
  SellerState = [s \in Sellers |-> "Start"];
  count_seller = 0, count_buyer = 0, process_count = 0, lockSell = FALSE, lockBuy = FALSE, semaphore =0, flag1=FALSE,flag2=FALSE;

(* Invariant Proposals
(1) Prevent Attacks
(2) Consistent Transaction
*)
define
    SafeWithdrawal == 
       <>(bankBalance > 6000)
       
    SafeWithdrawal2 == SafeWithdrawal
    
    FinalAmountBank == 
             <>(\A x \in validBuyers: finalValBuyer[x] = 6000)
    
    FinalAmountBank2 == FinalAmountBank
         
    (* Invariants that ensures that all sellers & buyers participating are validated before market session ends*)
    BuyersValidated ==  
    /\ \A x \in validBuyers : x \in Buyers
    
    SellersValidated ==
    /\ \A x \in validSellers : x \in Sellers
    
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
   validBuyerWallet := [b \in Buyers |-> bankBalance]; \* maps validated buyer to bankBalance -- means they can take part in the market session
end macro;

(* procedure that simulates the market's matching process 
*)
procedure matching(pro)
variable checkBuyer, UnmappedSellers;

begin
 checkEmptySeller:
    if validSellers = {} then validSellers := validSellers_copy; end if;

 matching:
    await validSellers /= {};
    await validBuyers /= {};
    await flagValBuyer /= << >>;
    
\*    if pro \in validSellers /\ flag1 = FALSE then flag1 := TRUE; count_seller := 1; end if;
    
    if validBuyers /= {} then
    
    \*validSellers
    makeBackupValidSeller:
    if validSellers /= {} then validSellers_copy := validSellers; end if;
    
    \*hardcode the sorting in descending order of the periodicEnergyBids
    sorting:
        if pro \in validBuyers then
            periodicEnergyBids[pro] := <<EnergyBidAmountsSorted, EnergyBidPricesSorted>>;
            clearingPrice := 1; \*energy price determined 
        end if;
        
    \*matching of buyers with prosumers (2B, 1S)
    \*only 1 buyer can match with 1 seller at a time
    
    \* need to add a statement that checks if there is already a flagValBuyer set to true must wait
    
    selectSeller:
    UnmappedSellers := validSellers;\*{x \in validSellers: ~\E y \in validBuyers: mapBuyerToSeller[y] = {x}};
    
    selectBuyer:
      if validBuyers /= {} then
         if pro \in validBuyers  then
        with b \in validBuyers do
            with s \in UnmappedSellers do \* problem since validSellers is not mapped exclusively to just one buyer
                flagValBuyer[b] := TRUE;   
                mapBuyerToSeller[b] := s;
                UnmappedSellers := UnmappedSellers \ {s};
            end with;
        end with;
        end if;
      end if;
      
    waitForTrue:
    
    await \E bool \in DOMAIN flagValBuyer: flagValBuyer[bool] = TRUE;
    if pro \in validSellers then SellerState[pro] := "matching"; end if;
    
    \*lock critical section behaviour by checking the mapping
    checkBuyer := CHOOSE buyer \in DOMAIN flagValBuyer: flagValBuyer[buyer] = TRUE;
    
    if \E bool \in  DOMAIN flagValBuyer: flagValBuyer[bool] then
        criticalSection:
\*            temp:= flagValBuyer[checkBuyer];\*CHOOSE buyer \in DOMAIN flagValBuyer: flagValBuyer[buyer] = TRUE;
\*            print("KAT SINI");
            \*deduct buyers bankBalance
            if pro \in validBuyers then
                validBuyerWallet[checkBuyer] := bankBalance - AMOUNT;
                finalValBuyer := validBuyerWallet;
                await \E elem \in DOMAIN SellerState: SellerState[elem] = "matching";
                flagValBuyer[checkBuyer] := FALSE;
                flag1 :=TRUE;
            end if;
\*    else 
\*    
\*    selectBuyer2:
\*         with b \in validBuyers do
\*            with  s \in validSellers do \* problem since validSellers is not mapped exclusively to just one buyer
\*                flagValBuyer[b] := TRUE;
\*                mapBuyerToSeller[b] := {s};
\*            end with;
\*         end with;
\*        
\*        criticalSection2:
\*    
\*\*            temp:= flagValBuyer[checkBuyer];\*CHOOSE buyer \in DOMAIN flagValBuyer: flagValBuyer[buyer] = TRUE;
\*            \*deduct buyers bankBalance
\*            validBuyerWallet[checkBuyer] := bankBalance - AMOUNT;
\*            finalValBuyer := validBuyerWallet;
     end if;
     
    \*reset flag to false
\*    resetCounter:
   end if;
    
 returnMatch:
  return;
end procedure;

(* procedure that simulates the market's settlement process
   the appropriate comodities of buyer are deducted from the system
   the transfer of commodities is shown via the change in the PeriodicEnergyBids & PeriodicEnergyOffers 
*)
procedure settlementBuyer(pro)
variables hourChosen = 1, sellerAssosciated = 0, npc = 0, 
           commodity1 = 10, commodity2 = 11;

begin
\*  awaitForSellersAndBuyers:
\*    await flagBuyers = TRUE;
\*    if pro \in validSellers then count_seller := count_seller + 1;  end if;
\*    if pro \in validBuyers then count_buyer := count_buyer + 1;  end if;
\*    
\*    if count_seller = 1 then lockSell := TRUE; end if;
\*    
\*    if count_buyer = 1 then lockBuy := TRUE; flagSellers := TRUE; end if;
\*        
\*   awaitLockTrue:
\*    await lockBuy = TRUE /\ lockSell = TRUE;
    
  settlementBuyer:
  if pro \in DOMAIN mapBuyerToSeller then
       lockSell := TRUE;
       flagSellers := TRUE;
    \*   await \E elem \in DOMAIN SellerState: SellerState[elem] = "settlement";
       await lockBuy = TRUE;
       sellerAssosciated := mapBuyerToSeller[pro]; \*map the seller assosciated with the buyer
   
   \*transfer assosciated commodity with a specified amount to buyer 
\*   periodicEnergyBids[pro] := << <<EnergyBidAmountsSorted[hourChosen]+EnergyOfferAmounts[hourChosen] , EnergyBidPricesSorted[hourChosen] + EnergyOfferPrices[hourChosen]>> >>;
    periodicEnergyBids[pro][1][hourChosen] :=  periodicEnergyBids[pro][1][hourChosen] + EnergyOfferAmounts[hourChosen];
   
   
   \*transfer assosciated commodity with a specificed amount to seller
     periodicEnergyOffers[sellerAssosciated][1][hourChosen] :=periodicEnergyOffers[sellerAssosciated][1][hourChosen] - periodicEnergyBids[pro][1][hourChosen]  ;
   
       if pro \in validBuyers then 
    \*       semaphore := 1;
           validBuyers := validBuyers \ {pro}; 
           validBuyers_copy := validBuyers;
    \*       process_count := process_count + 1;
    \*       flag1 := TRUE;
       end if;
   
   end if;
   \*The following label in this operation is to allow the transfer of commodities
   
  resetFlags1:
\*    await flag2= TRUE;await flag1 = TRUE;
\*    await process_count = 2;
\*    process_count := 0;
\*    count_seller := 0;
\*    count_buyer := 0;
    flagSellers := FALSE;
\*    flagBuyers := FALSE;
\*    lockSell := FALSE;
\*    lockBuy := FALSE;
  
  returnSettlement:
   return; 
end procedure;

(* procedure that simulates the market's settlement process
   the appropriate comodities of seller and buyer are deducted from the system
   the transfer of commodities is shown via the change in the PeriodicEnergyBids & PeriodicEnergyOffers 
*)
procedure settlementSeller(pro)
variables hourChosen = 1, sellerAssosciated = pro, npc = 0, 
           commodity1 = 10, commodity2 = 11;

begin
\*  awaitForSellersAndBuyers:
\*    await flagBuyers = TRUE;
\*    if pro \in validSellers then count_seller := count_seller + 1;  end if;
\*    if pro \in validBuyers then count_buyer := count_buyer + 1;  end if;
\*    
\*    if count_seller = 1 then lockSell := TRUE; end if;
\*    
\*    if count_buyer = 1 then lockBuy := TRUE; flagSellers := TRUE; end if;
\*        
\*   awaitLockTrue:
\*    await lockBuy = TRUE /\ lockSell = TRUE;
    
  settlement:
     SellerState[pro] := "settlement";
   \*The following label in this operation is to allow the transfer of commodities
    lockBuy := TRUE;
\*    await \E elem \in DOMAIN BuyerState: BuyerState[elem] = "settlement";
    await lockSell = TRUE;
        
    flagBuyers := TRUE;
\*    await count_seller = 1;  
   AssosciateSeller:
   
   if pro \in validSellers then 
        
        SellerState[pro] := "settlement";
   
       (* check on commodity of sellers if they have commodities available
        if not just remove it
       *)
       if periodicEnergyOffers[sellerAssosciated][1][hourChosen] < 11 then
        validSellers := validSellers \ {sellerAssosciated};
       end if;
       
       copyState:
\*        semaphore := 1;
        validSellers := validSellers_copy;
\*        process_count := process_count + 1;
        
       resetSemaphore1:
        semaphore := 0;
        flag2:=TRUE;
   end if;
  
  
  resetFlags2:
\*    await flag2= TRUE;await flag1 = TRUE;
\*    await process_count = 2;
\*    process_count := 0;
\*    count_seller := 0;
\*    count_buyer := 0;
\*    flagSellers := FALSE;
    flagBuyers := FALSE;
\*    lockSell := FALSE;
\*    lockBuy := FALSE;
  
  returnSettlement:
   return; 
end procedure;

(* procedure that simulates the market's settlement process
   the appropriate comodities of seller and buyer are deducted from the system
   the transfer of commodities is shown via the change in the PeriodicEnergyBids & PeriodicEnergyOffers 
*)
\*procedure settlementSeller(pro)
\*variables hourChosen = 1, sellerAssosciated = 4, npc = 0, 
\*           commodity1 = 10, commodity2 = 11;
\*
\*begin
\*  awaitForSellersAndBuyers:
\*    await flagBuyers = TRUE;
\*    if pro \in validSellers then count_seller := count_seller + 1;  end if;
\*    if pro \in validBuyers then count_buyer := count_buyer + 1;  end if;
\*    
\*    if count_seller = 1 then lockSell := TRUE; end if;
\*    
\*    if count_buyer = 1 then lockBuy := TRUE; flagSellers := TRUE; end if;
\*        
\*   awaitLockTrue:
\*    await lockBuy = TRUE /\ lockSell = TRUE;
\*    
\*  settlement:
\*  if pro \in DOMAIN mapBuyerToSeller then
\*   
\*   await count_buyer = 1;
\*   
\*   \*transfer assosciated commodity with a specified amount to buyer 
\*   periodicEnergyBids[pro] := << <<EnergyBidAmountsSorted[hourChosen]+EnergyOfferAmounts[hourChosen] , EnergyBidPricesSorted[hourChosen] + EnergyOfferPrices[hourChosen]>> >>;
\*   
\*   \*transfer assosciated commodity with a specificed amount to seller
\*   periodicEnergyOffers[sellerAssosciated] := << <<EnergyBidAmounts[hourChosen] - EnergyOfferAmounts[hourChosen] , EnergyBidPricesSorted[hourChosen] - EnergyOfferPrices[hourChosen]>> >>;
\*   
\*   if pro \in validBuyers then 
\*       semaphore := 1;
\*       validBuyers := validBuyers \ {pro}; 
\*       validBuyers_copy := validBuyers;
\*       process_count := process_count + 1;
\*       flag1 := TRUE;
\*   end if;
\*   resetSemaphore:
\*   semaphore := 0;
\*   end if;
\*   \*The following label in this operation is to allow the transfer of commodities
\*   awaitAssosciatedSeller:
\*    
\*    flag1 :=FALSE;
\*    await count_seller = 1;  
\*   AssosciateSeller:
\*   
\*   if pro \in validSellers then 
\*   
\*       (* check on commodity of sellers if they have commodities available
\*        if not just remove it
\*       *)
\*       if periodicEnergyOffers[sellerAssosciated][1][hourChosen] < 11 then
\*        validSellers := validSellers \ {sellerAssosciated};
\*       end if;
\*       
\*       copyState:
\*        semaphore := 1;
\*        validSellers := validSellers_copy;
\*        process_count := process_count + 1;
\*        
\*       resetSemaphore1:
\*        semaphore := 0;
\*        flag2:=TRUE;
\*   end if;
\*  
\*  
\*  resetFlags:
\*    await flag2= TRUE;await flag1 = TRUE;
\*    await process_count = 2;
\*    process_count := 0;
\*    count_seller := 0;
\*    count_buyer := 0;
\*    flagSellers := FALSE;
\*    flagBuyers := FALSE;
\*    lockSell := FALSE;
\*    lockBuy := FALSE;
\*  
\*  returnSettlement:
\*   return; 
\*end procedure;


(* procedure that simulates the market's sell process
*)
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
     await validBuyers = validBuyers_copy;
    if self \in validBuyers then
        flagValBuyer := [elem \in validBuyers |-> FALSE];
    end if;
  matching1:
    await validBuyers /= {};
    call matching(self);
  settlement1:
  if self \in validBuyers then
\*    flagSettlement := flagSettlement + 1;
    loopJO2:
    lockSell := TRUE;
    await flagBuyers = FALSE;
    BuyerState[pro] := "settlement";
    call settlementBuyer(self);
\*    SetToTrue:
\*    flagSettlement := flagSettlement + 1;
  end if;
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
    call matching(self);
  settlement2:
  if self \in validSellers then
\*    count_seller := count_seller + 1;
    lockBuy := TRUE;
    loopJO1:
\*    await lockSell = FALSE;
    await flagSellers = FALSE; \*wait for buyer to go inside the settlement, and only then seller goes in
    call settlementSeller(self);
\*    SetToFalse:
\*    flagSettlement := flagSettlement - 1;
   end if;
 end process;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "1cba39aa" /\ chksum(tla) = "1757d440")
\* Label matching of procedure matching at line 146 col 5 changed to matching_
\* Label settlementBuyer of procedure settlementBuyer at line 254 col 3 changed to settlementBuyer_
\* Label returnSettlement of procedure settlementBuyer at line 292 col 4 changed to returnSettlement_
\* Process variable other of process buyer at line 520 col 3 changed to other_
\* Procedure variable hourChosen of procedure settlementBuyer at line 237 col 11 changed to hourChosen_
\* Procedure variable sellerAssosciated of procedure settlementBuyer at line 237 col 27 changed to sellerAssosciated_
\* Procedure variable npc of procedure settlementBuyer at line 237 col 50 changed to npc_
\* Procedure variable commodity1 of procedure settlementBuyer at line 238 col 12 changed to commodity1_
\* Procedure variable commodity2 of procedure settlementBuyer at line 238 col 29 changed to commodity2_
\* Procedure variable price of procedure registerMarketSellOrder at line 453 col 11 changed to price_
\* Parameter pro of procedure matching at line 138 col 20 changed to pro_
\* Parameter pro of procedure settlementBuyer at line 236 col 27 changed to pro_s
\* Parameter pro of procedure settlementSeller at line 299 col 28 changed to pro_se
\* Parameter pro of procedure registerMarketSellOrder at line 451 col 36 changed to pro_r
\* Parameter pro of procedure registerMarketBuyOrder at line 471 col 35 changed to pro_re
\* Parameter pro of procedure validateAccount at line 493 col 27 changed to pro_v
CONSTANT defaultInitValue
VARIABLES attack, bankBalance, registry, periodicEnergyBids, 
          periodicEnergyOffers, validBuyers, validSellers, validBuyers_copy, 
          validSellers_copy, validBuyerWallet, mapBuyerToSeller, valBuyer, 
          valSeller, clearingPrice, temp, flagValBuyer, finalValBuyer, 
          flagBuyers, flagSellers, BuyerState, SellerState, count_seller, 
          count_buyer, process_count, lockSell, lockBuy, semaphore, flag1, 
          flag2, pc, stack

(* define statement *)
SafeWithdrawal ==
   <>(bankBalance > 6000)

SafeWithdrawal2 == SafeWithdrawal

FinalAmountBank ==
         <>(\A x \in validBuyers: finalValBuyer[x] = 6000)

FinalAmountBank2 == FinalAmountBank


BuyersValidated ==
/\ \A x \in validBuyers : x \in Buyers

SellersValidated ==
/\ \A x \in validSellers : x \in Sellers

VARIABLES pro_, checkBuyer, UnmappedSellers, pro_s, hourChosen_, 
          sellerAssosciated_, npc_, commodity1_, commodity2_, pro_se, 
          hourChosen, sellerAssosciated, npc, commodity1, commodity2, pro_r, 
          offer, price_, pro_re, bid, price, pro_v, pro, other_, test, other

vars == << attack, bankBalance, registry, periodicEnergyBids, 
           periodicEnergyOffers, validBuyers, validSellers, validBuyers_copy, 
           validSellers_copy, validBuyerWallet, mapBuyerToSeller, valBuyer, 
           valSeller, clearingPrice, temp, flagValBuyer, finalValBuyer, 
           flagBuyers, flagSellers, BuyerState, SellerState, count_seller, 
           count_buyer, process_count, lockSell, lockBuy, semaphore, flag1, 
           flag2, pc, stack, pro_, checkBuyer, UnmappedSellers, pro_s, 
           hourChosen_, sellerAssosciated_, npc_, commodity1_, commodity2_, 
           pro_se, hourChosen, sellerAssosciated, npc, commodity1, commodity2, 
           pro_r, offer, price_, pro_re, bid, price, pro_v, pro, other_, test, 
           other >>

ProcSet == (Buyers) \cup (Sellers)

Init == (* Global variables *)
        /\ attack = 0
        /\ bankBalance = BALANCE
        /\ registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]]
        /\ periodicEnergyBids = [b \in Buyers |-> PeriodicBidList]
        /\ periodicEnergyOffers = [s \in Sellers |-> PeriodicOfferList]
        /\ validBuyers = {}
        /\ validSellers = {}
        /\ validBuyers_copy = Buyers
        /\ validSellers_copy = Sellers
        /\ validBuyerWallet = [b \in Buyers |-> 0]
        /\ mapBuyerToSeller = [b \in Buyers |-> 0]
        /\ valBuyer = defaultInitValue
        /\ valSeller = defaultInitValue
        /\ clearingPrice = 0
        /\ temp = 0
        /\ flagValBuyer = [b \in Buyers |-> FALSE]
        /\ finalValBuyer = [b \in Buyers |-> 0]
        /\ flagBuyers = FALSE
        /\ flagSellers = FALSE
        /\ BuyerState = [b \in Buyers |-> "Start"]
        /\ SellerState = [s \in Sellers |-> "Start"]
        /\ count_seller = 0
        /\ count_buyer = 0
        /\ process_count = 0
        /\ lockSell = FALSE
        /\ lockBuy = FALSE
        /\ semaphore = 0
        /\ flag1 = FALSE
        /\ flag2 = FALSE
        (* Procedure matching *)
        /\ pro_ = [ self \in ProcSet |-> defaultInitValue]
        /\ checkBuyer = [ self \in ProcSet |-> defaultInitValue]
        /\ UnmappedSellers = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure settlementBuyer *)
        /\ pro_s = [ self \in ProcSet |-> defaultInitValue]
        /\ hourChosen_ = [ self \in ProcSet |-> 1]
        /\ sellerAssosciated_ = [ self \in ProcSet |-> 0]
        /\ npc_ = [ self \in ProcSet |-> 0]
        /\ commodity1_ = [ self \in ProcSet |-> 10]
        /\ commodity2_ = [ self \in ProcSet |-> 11]
        (* Procedure settlementSeller *)
        /\ pro_se = [ self \in ProcSet |-> defaultInitValue]
        /\ hourChosen = [ self \in ProcSet |-> 1]
        /\ sellerAssosciated = [ self \in ProcSet |-> pro_se[self]]
        /\ npc = [ self \in ProcSet |-> 0]
        /\ commodity1 = [ self \in ProcSet |-> 10]
        /\ commodity2 = [ self \in ProcSet |-> 11]
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

checkEmptySeller(self) == /\ pc[self] = "checkEmptySeller"
                          /\ IF validSellers = {}
                                THEN /\ validSellers' = validSellers_copy
                                ELSE /\ TRUE
                                     /\ UNCHANGED validSellers
                          /\ pc' = [pc EXCEPT ![self] = "matching_"]
                          /\ UNCHANGED << attack, bankBalance, registry, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validBuyers_copy, validSellers_copy, 
                                          validBuyerWallet, mapBuyerToSeller, 
                                          valBuyer, valSeller, clearingPrice, 
                                          temp, flagValBuyer, finalValBuyer, 
                                          flagBuyers, flagSellers, BuyerState, 
                                          SellerState, count_seller, 
                                          count_buyer, process_count, lockSell, 
                                          lockBuy, semaphore, flag1, flag2, 
                                          stack, pro_, checkBuyer, 
                                          UnmappedSellers, pro_s, hourChosen_, 
                                          sellerAssosciated_, npc_, 
                                          commodity1_, commodity2_, pro_se, 
                                          hourChosen, sellerAssosciated, npc, 
                                          commodity1, commodity2, pro_r, offer, 
                                          price_, pro_re, bid, price, pro_v, 
                                          pro, other_, test, other >>

matching_(self) == /\ pc[self] = "matching_"
                   /\ validSellers /= {}
                   /\ validBuyers /= {}
                   /\ flagValBuyer /= << >>
                   /\ IF validBuyers /= {}
                         THEN /\ pc' = [pc EXCEPT ![self] = "makeBackupValidSeller"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "returnMatch"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, validBuyers_copy, 
                                   validSellers_copy, validBuyerWallet, 
                                   mapBuyerToSeller, valBuyer, valSeller, 
                                   clearingPrice, temp, flagValBuyer, 
                                   finalValBuyer, flagBuyers, flagSellers, 
                                   BuyerState, SellerState, count_seller, 
                                   count_buyer, process_count, lockSell, 
                                   lockBuy, semaphore, flag1, flag2, stack, 
                                   pro_, checkBuyer, UnmappedSellers, pro_s, 
                                   hourChosen_, sellerAssosciated_, npc_, 
                                   commodity1_, commodity2_, pro_se, 
                                   hourChosen, sellerAssosciated, npc, 
                                   commodity1, commodity2, pro_r, offer, 
                                   price_, pro_re, bid, price, pro_v, pro, 
                                   other_, test, other >>

makeBackupValidSeller(self) == /\ pc[self] = "makeBackupValidSeller"
                               /\ IF validSellers /= {}
                                     THEN /\ validSellers_copy' = validSellers
                                     ELSE /\ TRUE
                                          /\ UNCHANGED validSellers_copy
                               /\ pc' = [pc EXCEPT ![self] = "sorting"]
                               /\ UNCHANGED << attack, bankBalance, registry, 
                                               periodicEnergyBids, 
                                               periodicEnergyOffers, 
                                               validBuyers, validSellers, 
                                               validBuyers_copy, 
                                               validBuyerWallet, 
                                               mapBuyerToSeller, valBuyer, 
                                               valSeller, clearingPrice, temp, 
                                               flagValBuyer, finalValBuyer, 
                                               flagBuyers, flagSellers, 
                                               BuyerState, SellerState, 
                                               count_seller, count_buyer, 
                                               process_count, lockSell, 
                                               lockBuy, semaphore, flag1, 
                                               flag2, stack, pro_, checkBuyer, 
                                               UnmappedSellers, pro_s, 
                                               hourChosen_, sellerAssosciated_, 
                                               npc_, commodity1_, commodity2_, 
                                               pro_se, hourChosen, 
                                               sellerAssosciated, npc, 
                                               commodity1, commodity2, pro_r, 
                                               offer, price_, pro_re, bid, 
                                               price, pro_v, pro, other_, test, 
                                               other >>

sorting(self) == /\ pc[self] = "sorting"
                 /\ IF pro_[self] \in validBuyers
                       THEN /\ periodicEnergyBids' = [periodicEnergyBids EXCEPT ![pro_[self]] = <<EnergyBidAmountsSorted, EnergyBidPricesSorted>>]
                            /\ clearingPrice' = 1
                       ELSE /\ TRUE
                            /\ UNCHANGED << periodicEnergyBids, clearingPrice >>
                 /\ pc' = [pc EXCEPT ![self] = "selectSeller"]
                 /\ UNCHANGED << attack, bankBalance, registry, 
                                 periodicEnergyOffers, validBuyers, 
                                 validSellers, validBuyers_copy, 
                                 validSellers_copy, validBuyerWallet, 
                                 mapBuyerToSeller, valBuyer, valSeller, temp, 
                                 flagValBuyer, finalValBuyer, flagBuyers, 
                                 flagSellers, BuyerState, SellerState, 
                                 count_seller, count_buyer, process_count, 
                                 lockSell, lockBuy, semaphore, flag1, flag2, 
                                 stack, pro_, checkBuyer, UnmappedSellers, 
                                 pro_s, hourChosen_, sellerAssosciated_, npc_, 
                                 commodity1_, commodity2_, pro_se, hourChosen, 
                                 sellerAssosciated, npc, commodity1, 
                                 commodity2, pro_r, offer, price_, pro_re, bid, 
                                 price, pro_v, pro, other_, test, other >>

selectSeller(self) == /\ pc[self] = "selectSeller"
                      /\ UnmappedSellers' = [UnmappedSellers EXCEPT ![self] = validSellers]
                      /\ pc' = [pc EXCEPT ![self] = "selectBuyer"]
                      /\ UNCHANGED << attack, bankBalance, registry, 
                                      periodicEnergyBids, periodicEnergyOffers, 
                                      validBuyers, validSellers, 
                                      validBuyers_copy, validSellers_copy, 
                                      validBuyerWallet, mapBuyerToSeller, 
                                      valBuyer, valSeller, clearingPrice, temp, 
                                      flagValBuyer, finalValBuyer, flagBuyers, 
                                      flagSellers, BuyerState, SellerState, 
                                      count_seller, count_buyer, process_count, 
                                      lockSell, lockBuy, semaphore, flag1, 
                                      flag2, stack, pro_, checkBuyer, pro_s, 
                                      hourChosen_, sellerAssosciated_, npc_, 
                                      commodity1_, commodity2_, pro_se, 
                                      hourChosen, sellerAssosciated, npc, 
                                      commodity1, commodity2, pro_r, offer, 
                                      price_, pro_re, bid, price, pro_v, pro, 
                                      other_, test, other >>

selectBuyer(self) == /\ pc[self] = "selectBuyer"
                     /\ IF validBuyers /= {}
                           THEN /\ IF pro_[self] \in validBuyers
                                      THEN /\ \E b \in validBuyers:
                                                \E s \in UnmappedSellers[self]:
                                                  /\ flagValBuyer' = [flagValBuyer EXCEPT ![b] = TRUE]
                                                  /\ mapBuyerToSeller' = [mapBuyerToSeller EXCEPT ![b] = s]
                                                  /\ UnmappedSellers' = [UnmappedSellers EXCEPT ![self] = UnmappedSellers[self] \ {s}]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << mapBuyerToSeller, 
                                                           flagValBuyer, 
                                                           UnmappedSellers >>
                           ELSE /\ TRUE
                                /\ UNCHANGED << mapBuyerToSeller, flagValBuyer, 
                                                UnmappedSellers >>
                     /\ pc' = [pc EXCEPT ![self] = "waitForTrue"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     validBuyers_copy, validSellers_copy, 
                                     validBuyerWallet, valBuyer, valSeller, 
                                     clearingPrice, temp, finalValBuyer, 
                                     flagBuyers, flagSellers, BuyerState, 
                                     SellerState, count_seller, count_buyer, 
                                     process_count, lockSell, lockBuy, 
                                     semaphore, flag1, flag2, stack, pro_, 
                                     checkBuyer, pro_s, hourChosen_, 
                                     sellerAssosciated_, npc_, commodity1_, 
                                     commodity2_, pro_se, hourChosen, 
                                     sellerAssosciated, npc, commodity1, 
                                     commodity2, pro_r, offer, price_, pro_re, 
                                     bid, price, pro_v, pro, other_, test, 
                                     other >>

waitForTrue(self) == /\ pc[self] = "waitForTrue"
                     /\ \E bool \in DOMAIN flagValBuyer: flagValBuyer[bool] = TRUE
                     /\ IF pro_[self] \in validSellers
                           THEN /\ SellerState' = [SellerState EXCEPT ![pro_[self]] = "matching"]
                           ELSE /\ TRUE
                                /\ UNCHANGED SellerState
                     /\ checkBuyer' = [checkBuyer EXCEPT ![self] = CHOOSE buyer \in DOMAIN flagValBuyer: flagValBuyer[buyer] = TRUE]
                     /\ IF \E bool \in  DOMAIN flagValBuyer: flagValBuyer[bool]
                           THEN /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "returnMatch"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     validBuyers_copy, validSellers_copy, 
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, finalValBuyer, flagBuyers, 
                                     flagSellers, BuyerState, count_seller, 
                                     count_buyer, process_count, lockSell, 
                                     lockBuy, semaphore, flag1, flag2, stack, 
                                     pro_, UnmappedSellers, pro_s, hourChosen_, 
                                     sellerAssosciated_, npc_, commodity1_, 
                                     commodity2_, pro_se, hourChosen, 
                                     sellerAssosciated, npc, commodity1, 
                                     commodity2, pro_r, offer, price_, pro_re, 
                                     bid, price, pro_v, pro, other_, test, 
                                     other >>

criticalSection(self) == /\ pc[self] = "criticalSection"
                         /\ IF pro_[self] \in validBuyers
                               THEN /\ validBuyerWallet' = [validBuyerWallet EXCEPT ![checkBuyer[self]] = bankBalance - AMOUNT]
                                    /\ finalValBuyer' = validBuyerWallet'
                                    /\ \E elem \in DOMAIN SellerState: SellerState[elem] = "matching"
                                    /\ flagValBuyer' = [flagValBuyer EXCEPT ![checkBuyer[self]] = FALSE]
                                    /\ flag1' = TRUE
                               ELSE /\ TRUE
                                    /\ UNCHANGED << validBuyerWallet, 
                                                    flagValBuyer, 
                                                    finalValBuyer, flag1 >>
                         /\ pc' = [pc EXCEPT ![self] = "returnMatch"]
                         /\ UNCHANGED << attack, bankBalance, registry, 
                                         periodicEnergyBids, 
                                         periodicEnergyOffers, validBuyers, 
                                         validSellers, validBuyers_copy, 
                                         validSellers_copy, mapBuyerToSeller, 
                                         valBuyer, valSeller, clearingPrice, 
                                         temp, flagBuyers, flagSellers, 
                                         BuyerState, SellerState, count_seller, 
                                         count_buyer, process_count, lockSell, 
                                         lockBuy, semaphore, flag2, stack, 
                                         pro_, checkBuyer, UnmappedSellers, 
                                         pro_s, hourChosen_, 
                                         sellerAssosciated_, npc_, commodity1_, 
                                         commodity2_, pro_se, hourChosen, 
                                         sellerAssosciated, npc, commodity1, 
                                         commodity2, pro_r, offer, price_, 
                                         pro_re, bid, price, pro_v, pro, 
                                         other_, test, other >>

returnMatch(self) == /\ pc[self] = "returnMatch"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ checkBuyer' = [checkBuyer EXCEPT ![self] = Head(stack[self]).checkBuyer]
                     /\ UnmappedSellers' = [UnmappedSellers EXCEPT ![self] = Head(stack[self]).UnmappedSellers]
                     /\ pro_' = [pro_ EXCEPT ![self] = Head(stack[self]).pro_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     validBuyers_copy, validSellers_copy, 
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, finalValBuyer, flagBuyers, 
                                     flagSellers, BuyerState, SellerState, 
                                     count_seller, count_buyer, process_count, 
                                     lockSell, lockBuy, semaphore, flag1, 
                                     flag2, pro_s, hourChosen_, 
                                     sellerAssosciated_, npc_, commodity1_, 
                                     commodity2_, pro_se, hourChosen, 
                                     sellerAssosciated, npc, commodity1, 
                                     commodity2, pro_r, offer, price_, pro_re, 
                                     bid, price, pro_v, pro, other_, test, 
                                     other >>

matching(self) == checkEmptySeller(self) \/ matching_(self)
                     \/ makeBackupValidSeller(self) \/ sorting(self)
                     \/ selectSeller(self) \/ selectBuyer(self)
                     \/ waitForTrue(self) \/ criticalSection(self)
                     \/ returnMatch(self)

settlementBuyer_(self) == /\ pc[self] = "settlementBuyer_"
                          /\ IF pro_s[self] \in DOMAIN mapBuyerToSeller
                                THEN /\ lockSell' = TRUE
                                     /\ flagSellers' = TRUE
                                     /\ lockBuy = TRUE
                                     /\ sellerAssosciated_' = [sellerAssosciated_ EXCEPT ![self] = mapBuyerToSeller[pro_s[self]]]
                                     /\ periodicEnergyBids' = [periodicEnergyBids EXCEPT ![pro_s[self]][1][hourChosen_[self]] = periodicEnergyBids[pro_s[self]][1][hourChosen_[self]] + EnergyOfferAmounts[hourChosen_[self]]]
                                     /\ periodicEnergyOffers' = [periodicEnergyOffers EXCEPT ![sellerAssosciated_'[self]][1][hourChosen_[self]] = periodicEnergyOffers[sellerAssosciated_'[self]][1][hourChosen_[self]] - periodicEnergyBids'[pro_s[self]][1][hourChosen_[self]]]
                                     /\ IF pro_s[self] \in validBuyers
                                           THEN /\ validBuyers' = validBuyers \ {pro_s[self]}
                                                /\ validBuyers_copy' = validBuyers'
                                           ELSE /\ TRUE
                                                /\ UNCHANGED << validBuyers, 
                                                                validBuyers_copy >>
                                ELSE /\ TRUE
                                     /\ UNCHANGED << periodicEnergyBids, 
                                                     periodicEnergyOffers, 
                                                     validBuyers, 
                                                     validBuyers_copy, 
                                                     flagSellers, lockSell, 
                                                     sellerAssosciated_ >>
                          /\ pc' = [pc EXCEPT ![self] = "resetFlags1"]
                          /\ UNCHANGED << attack, bankBalance, registry, 
                                          validSellers, validSellers_copy, 
                                          validBuyerWallet, mapBuyerToSeller, 
                                          valBuyer, valSeller, clearingPrice, 
                                          temp, flagValBuyer, finalValBuyer, 
                                          flagBuyers, BuyerState, SellerState, 
                                          count_seller, count_buyer, 
                                          process_count, lockBuy, semaphore, 
                                          flag1, flag2, stack, pro_, 
                                          checkBuyer, UnmappedSellers, pro_s, 
                                          hourChosen_, npc_, commodity1_, 
                                          commodity2_, pro_se, hourChosen, 
                                          sellerAssosciated, npc, commodity1, 
                                          commodity2, pro_r, offer, price_, 
                                          pro_re, bid, price, pro_v, pro, 
                                          other_, test, other >>

resetFlags1(self) == /\ pc[self] = "resetFlags1"
                     /\ flagSellers' = FALSE
                     /\ pc' = [pc EXCEPT ![self] = "returnSettlement_"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     validBuyers_copy, validSellers_copy, 
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, finalValBuyer, flagBuyers, 
                                     BuyerState, SellerState, count_seller, 
                                     count_buyer, process_count, lockSell, 
                                     lockBuy, semaphore, flag1, flag2, stack, 
                                     pro_, checkBuyer, UnmappedSellers, pro_s, 
                                     hourChosen_, sellerAssosciated_, npc_, 
                                     commodity1_, commodity2_, pro_se, 
                                     hourChosen, sellerAssosciated, npc, 
                                     commodity1, commodity2, pro_r, offer, 
                                     price_, pro_re, bid, price, pro_v, pro, 
                                     other_, test, other >>

returnSettlement_(self) == /\ pc[self] = "returnSettlement_"
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ hourChosen_' = [hourChosen_ EXCEPT ![self] = Head(stack[self]).hourChosen_]
                           /\ sellerAssosciated_' = [sellerAssosciated_ EXCEPT ![self] = Head(stack[self]).sellerAssosciated_]
                           /\ npc_' = [npc_ EXCEPT ![self] = Head(stack[self]).npc_]
                           /\ commodity1_' = [commodity1_ EXCEPT ![self] = Head(stack[self]).commodity1_]
                           /\ commodity2_' = [commodity2_ EXCEPT ![self] = Head(stack[self]).commodity2_]
                           /\ pro_s' = [pro_s EXCEPT ![self] = Head(stack[self]).pro_s]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << attack, bankBalance, registry, 
                                           periodicEnergyBids, 
                                           periodicEnergyOffers, validBuyers, 
                                           validSellers, validBuyers_copy, 
                                           validSellers_copy, validBuyerWallet, 
                                           mapBuyerToSeller, valBuyer, 
                                           valSeller, clearingPrice, temp, 
                                           flagValBuyer, finalValBuyer, 
                                           flagBuyers, flagSellers, BuyerState, 
                                           SellerState, count_seller, 
                                           count_buyer, process_count, 
                                           lockSell, lockBuy, semaphore, flag1, 
                                           flag2, pro_, checkBuyer, 
                                           UnmappedSellers, pro_se, hourChosen, 
                                           sellerAssosciated, npc, commodity1, 
                                           commodity2, pro_r, offer, price_, 
                                           pro_re, bid, price, pro_v, pro, 
                                           other_, test, other >>

settlementBuyer(self) == settlementBuyer_(self) \/ resetFlags1(self)
                            \/ returnSettlement_(self)

settlement(self) == /\ pc[self] = "settlement"
                    /\ SellerState' = [SellerState EXCEPT ![pro_se[self]] = "settlement"]
                    /\ lockBuy' = TRUE
                    /\ lockSell = TRUE
                    /\ flagBuyers' = TRUE
                    /\ pc' = [pc EXCEPT ![self] = "AssosciateSeller"]
                    /\ UNCHANGED << attack, bankBalance, registry, 
                                    periodicEnergyBids, periodicEnergyOffers, 
                                    validBuyers, validSellers, 
                                    validBuyers_copy, validSellers_copy, 
                                    validBuyerWallet, mapBuyerToSeller, 
                                    valBuyer, valSeller, clearingPrice, temp, 
                                    flagValBuyer, finalValBuyer, flagSellers, 
                                    BuyerState, count_seller, count_buyer, 
                                    process_count, lockSell, semaphore, flag1, 
                                    flag2, stack, pro_, checkBuyer, 
                                    UnmappedSellers, pro_s, hourChosen_, 
                                    sellerAssosciated_, npc_, commodity1_, 
                                    commodity2_, pro_se, hourChosen, 
                                    sellerAssosciated, npc, commodity1, 
                                    commodity2, pro_r, offer, price_, pro_re, 
                                    bid, price, pro_v, pro, other_, test, 
                                    other >>

AssosciateSeller(self) == /\ pc[self] = "AssosciateSeller"
                          /\ IF pro_se[self] \in validSellers
                                THEN /\ SellerState' = [SellerState EXCEPT ![pro_se[self]] = "settlement"]
                                     /\ IF periodicEnergyOffers[sellerAssosciated[self]][1][hourChosen[self]] < 11
                                           THEN /\ validSellers' = validSellers \ {sellerAssosciated[self]}
                                           ELSE /\ TRUE
                                                /\ UNCHANGED validSellers
                                     /\ pc' = [pc EXCEPT ![self] = "copyState"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "resetFlags2"]
                                     /\ UNCHANGED << validSellers, SellerState >>
                          /\ UNCHANGED << attack, bankBalance, registry, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validBuyers_copy, validSellers_copy, 
                                          validBuyerWallet, mapBuyerToSeller, 
                                          valBuyer, valSeller, clearingPrice, 
                                          temp, flagValBuyer, finalValBuyer, 
                                          flagBuyers, flagSellers, BuyerState, 
                                          count_seller, count_buyer, 
                                          process_count, lockSell, lockBuy, 
                                          semaphore, flag1, flag2, stack, pro_, 
                                          checkBuyer, UnmappedSellers, pro_s, 
                                          hourChosen_, sellerAssosciated_, 
                                          npc_, commodity1_, commodity2_, 
                                          pro_se, hourChosen, 
                                          sellerAssosciated, npc, commodity1, 
                                          commodity2, pro_r, offer, price_, 
                                          pro_re, bid, price, pro_v, pro, 
                                          other_, test, other >>

copyState(self) == /\ pc[self] = "copyState"
                   /\ validSellers' = validSellers_copy
                   /\ pc' = [pc EXCEPT ![self] = "resetSemaphore1"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validBuyers_copy, 
                                   validSellers_copy, validBuyerWallet, 
                                   mapBuyerToSeller, valBuyer, valSeller, 
                                   clearingPrice, temp, flagValBuyer, 
                                   finalValBuyer, flagBuyers, flagSellers, 
                                   BuyerState, SellerState, count_seller, 
                                   count_buyer, process_count, lockSell, 
                                   lockBuy, semaphore, flag1, flag2, stack, 
                                   pro_, checkBuyer, UnmappedSellers, pro_s, 
                                   hourChosen_, sellerAssosciated_, npc_, 
                                   commodity1_, commodity2_, pro_se, 
                                   hourChosen, sellerAssosciated, npc, 
                                   commodity1, commodity2, pro_r, offer, 
                                   price_, pro_re, bid, price, pro_v, pro, 
                                   other_, test, other >>

resetSemaphore1(self) == /\ pc[self] = "resetSemaphore1"
                         /\ semaphore' = 0
                         /\ flag2' = TRUE
                         /\ pc' = [pc EXCEPT ![self] = "resetFlags2"]
                         /\ UNCHANGED << attack, bankBalance, registry, 
                                         periodicEnergyBids, 
                                         periodicEnergyOffers, validBuyers, 
                                         validSellers, validBuyers_copy, 
                                         validSellers_copy, validBuyerWallet, 
                                         mapBuyerToSeller, valBuyer, valSeller, 
                                         clearingPrice, temp, flagValBuyer, 
                                         finalValBuyer, flagBuyers, 
                                         flagSellers, BuyerState, SellerState, 
                                         count_seller, count_buyer, 
                                         process_count, lockSell, lockBuy, 
                                         flag1, stack, pro_, checkBuyer, 
                                         UnmappedSellers, pro_s, hourChosen_, 
                                         sellerAssosciated_, npc_, commodity1_, 
                                         commodity2_, pro_se, hourChosen, 
                                         sellerAssosciated, npc, commodity1, 
                                         commodity2, pro_r, offer, price_, 
                                         pro_re, bid, price, pro_v, pro, 
                                         other_, test, other >>

resetFlags2(self) == /\ pc[self] = "resetFlags2"
                     /\ flagBuyers' = FALSE
                     /\ pc' = [pc EXCEPT ![self] = "returnSettlement"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     validBuyers_copy, validSellers_copy, 
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, finalValBuyer, flagSellers, 
                                     BuyerState, SellerState, count_seller, 
                                     count_buyer, process_count, lockSell, 
                                     lockBuy, semaphore, flag1, flag2, stack, 
                                     pro_, checkBuyer, UnmappedSellers, pro_s, 
                                     hourChosen_, sellerAssosciated_, npc_, 
                                     commodity1_, commodity2_, pro_se, 
                                     hourChosen, sellerAssosciated, npc, 
                                     commodity1, commodity2, pro_r, offer, 
                                     price_, pro_re, bid, price, pro_v, pro, 
                                     other_, test, other >>

returnSettlement(self) == /\ pc[self] = "returnSettlement"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ hourChosen' = [hourChosen EXCEPT ![self] = Head(stack[self]).hourChosen]
                          /\ sellerAssosciated' = [sellerAssosciated EXCEPT ![self] = Head(stack[self]).sellerAssosciated]
                          /\ npc' = [npc EXCEPT ![self] = Head(stack[self]).npc]
                          /\ commodity1' = [commodity1 EXCEPT ![self] = Head(stack[self]).commodity1]
                          /\ commodity2' = [commodity2 EXCEPT ![self] = Head(stack[self]).commodity2]
                          /\ pro_se' = [pro_se EXCEPT ![self] = Head(stack[self]).pro_se]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << attack, bankBalance, registry, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validSellers, validBuyers_copy, 
                                          validSellers_copy, validBuyerWallet, 
                                          mapBuyerToSeller, valBuyer, 
                                          valSeller, clearingPrice, temp, 
                                          flagValBuyer, finalValBuyer, 
                                          flagBuyers, flagSellers, BuyerState, 
                                          SellerState, count_seller, 
                                          count_buyer, process_count, lockSell, 
                                          lockBuy, semaphore, flag1, flag2, 
                                          pro_, checkBuyer, UnmappedSellers, 
                                          pro_s, hourChosen_, 
                                          sellerAssosciated_, npc_, 
                                          commodity1_, commodity2_, pro_r, 
                                          offer, price_, pro_re, bid, price, 
                                          pro_v, pro, other_, test, other >>

settlementSeller(self) == settlement(self) \/ AssosciateSeller(self)
                             \/ copyState(self) \/ resetSemaphore1(self)
                             \/ resetFlags2(self) \/ returnSettlement(self)

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
                                   validBuyers, validBuyers_copy, 
                                   validSellers_copy, validBuyerWallet, 
                                   mapBuyerToSeller, valBuyer, valSeller, 
                                   clearingPrice, temp, flagValBuyer, 
                                   finalValBuyer, flagBuyers, flagSellers, 
                                   BuyerState, SellerState, count_seller, 
                                   count_buyer, process_count, lockSell, 
                                   lockBuy, semaphore, flag1, flag2, stack, 
                                   pro_, checkBuyer, UnmappedSellers, pro_s, 
                                   hourChosen_, sellerAssosciated_, npc_, 
                                   commodity1_, commodity2_, pro_se, 
                                   hourChosen, sellerAssosciated, npc, 
                                   commodity1, commodity2, pro_r, pro_re, bid, 
                                   price, pro_v, pro, other_, test, other >>

FinishSellOrder(self) == /\ pc[self] = "FinishSellOrder"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ offer' = [offer EXCEPT ![self] = Head(stack[self]).offer]
                         /\ price_' = [price_ EXCEPT ![self] = Head(stack[self]).price_]
                         /\ pro_r' = [pro_r EXCEPT ![self] = Head(stack[self]).pro_r]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << attack, bankBalance, registry, 
                                         periodicEnergyBids, 
                                         periodicEnergyOffers, validBuyers, 
                                         validSellers, validBuyers_copy, 
                                         validSellers_copy, validBuyerWallet, 
                                         mapBuyerToSeller, valBuyer, valSeller, 
                                         clearingPrice, temp, flagValBuyer, 
                                         finalValBuyer, flagBuyers, 
                                         flagSellers, BuyerState, SellerState, 
                                         count_seller, count_buyer, 
                                         process_count, lockSell, lockBuy, 
                                         semaphore, flag1, flag2, pro_, 
                                         checkBuyer, UnmappedSellers, pro_s, 
                                         hourChosen_, sellerAssosciated_, npc_, 
                                         commodity1_, commodity2_, pro_se, 
                                         hourChosen, sellerAssosciated, npc, 
                                         commodity1, commodity2, pro_re, bid, 
                                         price, pro_v, pro, other_, test, 
                                         other >>

registerMarketSellOrder(self) == sellOrder(self) \/ FinishSellOrder(self)

BuyOrder(self) == /\ pc[self] = "BuyOrder"
                  /\ IF registry[pro_re[self]].reputation >= ReputationLimit
                        THEN /\ validBuyers' = (validBuyers \union {pro_re[self]})
                             /\ validBuyerWallet' = [b \in Buyers |-> bankBalance]
                             /\ \E buyer \in validBuyers':
                                  /\ bid' = [bid EXCEPT ![self] = periodicEnergyBids[buyer][1][2]]
                                  /\ price' = [price EXCEPT ![self] = periodicEnergyBids[buyer][2][2]]
                        ELSE /\ TRUE
                             /\ UNCHANGED << validBuyers, validBuyerWallet, 
                                             bid, price >>
                  /\ pc' = [pc EXCEPT ![self] = "FinishBuyOrder"]
                  /\ UNCHANGED << attack, bankBalance, registry, 
                                  periodicEnergyBids, periodicEnergyOffers, 
                                  validSellers, validBuyers_copy, 
                                  validSellers_copy, mapBuyerToSeller, 
                                  valBuyer, valSeller, clearingPrice, temp, 
                                  flagValBuyer, finalValBuyer, flagBuyers, 
                                  flagSellers, BuyerState, SellerState, 
                                  count_seller, count_buyer, process_count, 
                                  lockSell, lockBuy, semaphore, flag1, flag2, 
                                  stack, pro_, checkBuyer, UnmappedSellers, 
                                  pro_s, hourChosen_, sellerAssosciated_, npc_, 
                                  commodity1_, commodity2_, pro_se, hourChosen, 
                                  sellerAssosciated, npc, commodity1, 
                                  commodity2, pro_r, offer, price_, pro_re, 
                                  pro_v, pro, other_, test, other >>

FinishBuyOrder(self) == /\ pc[self] = "FinishBuyOrder"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ bid' = [bid EXCEPT ![self] = Head(stack[self]).bid]
                        /\ price' = [price EXCEPT ![self] = Head(stack[self]).price]
                        /\ pro_re' = [pro_re EXCEPT ![self] = Head(stack[self]).pro_re]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << attack, bankBalance, registry, 
                                        periodicEnergyBids, 
                                        periodicEnergyOffers, validBuyers, 
                                        validSellers, validBuyers_copy, 
                                        validSellers_copy, validBuyerWallet, 
                                        mapBuyerToSeller, valBuyer, valSeller, 
                                        clearingPrice, temp, flagValBuyer, 
                                        finalValBuyer, flagBuyers, flagSellers, 
                                        BuyerState, SellerState, count_seller, 
                                        count_buyer, process_count, lockSell, 
                                        lockBuy, semaphore, flag1, flag2, pro_, 
                                        checkBuyer, UnmappedSellers, pro_s, 
                                        hourChosen_, sellerAssosciated_, npc_, 
                                        commodity1_, commodity2_, pro_se, 
                                        hourChosen, sellerAssosciated, npc, 
                                        commodity1, commodity2, pro_r, offer, 
                                        price_, pro_v, pro, other_, test, 
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
                                          validSellers, validBuyers_copy, 
                                          validSellers_copy, validBuyerWallet, 
                                          mapBuyerToSeller, valBuyer, 
                                          valSeller, clearingPrice, temp, 
                                          flagValBuyer, finalValBuyer, 
                                          flagBuyers, flagSellers, BuyerState, 
                                          SellerState, count_seller, 
                                          count_buyer, process_count, lockSell, 
                                          lockBuy, semaphore, flag1, flag2, 
                                          pro_, checkBuyer, UnmappedSellers, 
                                          pro_s, hourChosen_, 
                                          sellerAssosciated_, npc_, 
                                          commodity1_, commodity2_, pro_se, 
                                          hourChosen, sellerAssosciated, npc, 
                                          commodity1, commodity2, pro_r, offer, 
                                          price_, pro_re, bid, price, pro, 
                                          other_, test, other >>

validateAccount(self) == ValidateProsumer(self)

RegisterProsumer(self) == /\ pc[self] = "RegisterProsumer"
                          /\ registry' = [registry EXCEPT ![pro[self]] = [valid |-> TRUE, reputation |-> 0]]
                          /\ pc' = [pc EXCEPT ![self] = "FinishRegisterProsumer"]
                          /\ UNCHANGED << attack, bankBalance, 
                                          periodicEnergyBids, 
                                          periodicEnergyOffers, validBuyers, 
                                          validSellers, validBuyers_copy, 
                                          validSellers_copy, validBuyerWallet, 
                                          mapBuyerToSeller, valBuyer, 
                                          valSeller, clearingPrice, temp, 
                                          flagValBuyer, finalValBuyer, 
                                          flagBuyers, flagSellers, BuyerState, 
                                          SellerState, count_seller, 
                                          count_buyer, process_count, lockSell, 
                                          lockBuy, semaphore, flag1, flag2, 
                                          stack, pro_, checkBuyer, 
                                          UnmappedSellers, pro_s, hourChosen_, 
                                          sellerAssosciated_, npc_, 
                                          commodity1_, commodity2_, pro_se, 
                                          hourChosen, sellerAssosciated, npc, 
                                          commodity1, commodity2, pro_r, offer, 
                                          price_, pro_re, bid, price, pro_v, 
                                          pro, other_, test, other >>

FinishRegisterProsumer(self) == /\ pc[self] = "FinishRegisterProsumer"
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ pro' = [pro EXCEPT ![self] = Head(stack[self]).pro]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << attack, bankBalance, registry, 
                                                periodicEnergyBids, 
                                                periodicEnergyOffers, 
                                                validBuyers, validSellers, 
                                                validBuyers_copy, 
                                                validSellers_copy, 
                                                validBuyerWallet, 
                                                mapBuyerToSeller, valBuyer, 
                                                valSeller, clearingPrice, temp, 
                                                flagValBuyer, finalValBuyer, 
                                                flagBuyers, flagSellers, 
                                                BuyerState, SellerState, 
                                                count_seller, count_buyer, 
                                                process_count, lockSell, 
                                                lockBuy, semaphore, flag1, 
                                                flag2, pro_, checkBuyer, 
                                                UnmappedSellers, pro_s, 
                                                hourChosen_, 
                                                sellerAssosciated_, npc_, 
                                                commodity1_, commodity2_, 
                                                pro_se, hourChosen, 
                                                sellerAssosciated, npc, 
                                                commodity1, commodity2, pro_r, 
                                                offer, price_, pro_re, bid, 
                                                price, pro_v, other_, test, 
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
                                        validSellers, validBuyers_copy, 
                                        validSellers_copy, validBuyerWallet, 
                                        mapBuyerToSeller, valBuyer, valSeller, 
                                        clearingPrice, temp, flagValBuyer, 
                                        finalValBuyer, flagBuyers, flagSellers, 
                                        BuyerState, SellerState, count_seller, 
                                        count_buyer, process_count, lockSell, 
                                        lockBuy, semaphore, flag1, flag2, pro_, 
                                        checkBuyer, UnmappedSellers, pro_s, 
                                        hourChosen_, sellerAssosciated_, npc_, 
                                        commodity1_, commodity2_, pro_se, 
                                        hourChosen, sellerAssosciated, npc, 
                                        commodity1, commodity2, pro_r, offer, 
                                        price_, pro_re, bid, price, pro_v, 
                                        other_, test, other >>

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
                                        validSellers, validBuyers_copy, 
                                        validSellers_copy, validBuyerWallet, 
                                        mapBuyerToSeller, valBuyer, valSeller, 
                                        clearingPrice, temp, flagValBuyer, 
                                        finalValBuyer, flagBuyers, flagSellers, 
                                        BuyerState, SellerState, count_seller, 
                                        count_buyer, process_count, lockSell, 
                                        lockBuy, semaphore, flag1, flag2, pro_, 
                                        checkBuyer, UnmappedSellers, pro_s, 
                                        hourChosen_, sellerAssosciated_, npc_, 
                                        commodity1_, commodity2_, pro_se, 
                                        hourChosen, sellerAssosciated, npc, 
                                        commodity1, commodity2, pro_r, offer, 
                                        price_, pro_re, bid, price, pro, 
                                        other_, test, other >>

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
                                    validBuyers_copy, validSellers_copy, 
                                    validBuyerWallet, mapBuyerToSeller, 
                                    valBuyer, valSeller, clearingPrice, temp, 
                                    flagValBuyer, finalValBuyer, flagBuyers, 
                                    flagSellers, BuyerState, SellerState, 
                                    count_seller, count_buyer, process_count, 
                                    lockSell, lockBuy, semaphore, flag1, flag2, 
                                    pro_, checkBuyer, UnmappedSellers, pro_s, 
                                    hourChosen_, sellerAssosciated_, npc_, 
                                    commodity1_, commodity2_, pro_se, 
                                    hourChosen, sellerAssosciated, npc, 
                                    commodity1, commodity2, pro_r, offer, 
                                    price_, pro_v, pro, other_, test, other >>

Chill(self) == /\ pc[self] = "Chill"
               /\ validBuyers = validBuyers_copy
               /\ IF self \in validBuyers
                     THEN /\ flagValBuyer' = [elem \in validBuyers |-> FALSE]
                     ELSE /\ TRUE
                          /\ UNCHANGED flagValBuyer
               /\ pc' = [pc EXCEPT ![self] = "matching1"]
               /\ UNCHANGED << attack, bankBalance, registry, 
                               periodicEnergyBids, periodicEnergyOffers, 
                               validBuyers, validSellers, validBuyers_copy, 
                               validSellers_copy, validBuyerWallet, 
                               mapBuyerToSeller, valBuyer, valSeller, 
                               clearingPrice, temp, finalValBuyer, flagBuyers, 
                               flagSellers, BuyerState, SellerState, 
                               count_seller, count_buyer, process_count, 
                               lockSell, lockBuy, semaphore, flag1, flag2, 
                               stack, pro_, checkBuyer, UnmappedSellers, pro_s, 
                               hourChosen_, sellerAssosciated_, npc_, 
                               commodity1_, commodity2_, pro_se, hourChosen, 
                               sellerAssosciated, npc, commodity1, commodity2, 
                               pro_r, offer, price_, pro_re, bid, price, pro_v, 
                               pro, other_, test, other >>

matching1(self) == /\ pc[self] = "matching1"
                   /\ validBuyers /= {}
                   /\ /\ pro_' = [pro_ EXCEPT ![self] = self]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "matching",
                                                               pc        |->  "settlement1",
                                                               checkBuyer |->  checkBuyer[self],
                                                               UnmappedSellers |->  UnmappedSellers[self],
                                                               pro_      |->  pro_[self] ] >>
                                                           \o stack[self]]
                   /\ checkBuyer' = [checkBuyer EXCEPT ![self] = defaultInitValue]
                   /\ UnmappedSellers' = [UnmappedSellers EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "checkEmptySeller"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, validBuyers_copy, 
                                   validSellers_copy, validBuyerWallet, 
                                   mapBuyerToSeller, valBuyer, valSeller, 
                                   clearingPrice, temp, flagValBuyer, 
                                   finalValBuyer, flagBuyers, flagSellers, 
                                   BuyerState, SellerState, count_seller, 
                                   count_buyer, process_count, lockSell, 
                                   lockBuy, semaphore, flag1, flag2, pro_s, 
                                   hourChosen_, sellerAssosciated_, npc_, 
                                   commodity1_, commodity2_, pro_se, 
                                   hourChosen, sellerAssosciated, npc, 
                                   commodity1, commodity2, pro_r, offer, 
                                   price_, pro_re, bid, price, pro_v, pro, 
                                   other_, test, other >>

settlement1(self) == /\ pc[self] = "settlement1"
                     /\ IF self \in validBuyers
                           THEN /\ pc' = [pc EXCEPT ![self] = "loopJO2"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     validBuyers_copy, validSellers_copy, 
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, finalValBuyer, flagBuyers, 
                                     flagSellers, BuyerState, SellerState, 
                                     count_seller, count_buyer, process_count, 
                                     lockSell, lockBuy, semaphore, flag1, 
                                     flag2, stack, pro_, checkBuyer, 
                                     UnmappedSellers, pro_s, hourChosen_, 
                                     sellerAssosciated_, npc_, commodity1_, 
                                     commodity2_, pro_se, hourChosen, 
                                     sellerAssosciated, npc, commodity1, 
                                     commodity2, pro_r, offer, price_, pro_re, 
                                     bid, price, pro_v, pro, other_, test, 
                                     other >>

loopJO2(self) == /\ pc[self] = "loopJO2"
                 /\ lockSell' = TRUE
                 /\ flagBuyers = FALSE
                 /\ BuyerState' = [BuyerState EXCEPT ![pro[self]] = "settlement"]
                 /\ /\ pro_s' = [pro_s EXCEPT ![self] = self]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "settlementBuyer",
                                                             pc        |->  "Done",
                                                             hourChosen_ |->  hourChosen_[self],
                                                             sellerAssosciated_ |->  sellerAssosciated_[self],
                                                             npc_      |->  npc_[self],
                                                             commodity1_ |->  commodity1_[self],
                                                             commodity2_ |->  commodity2_[self],
                                                             pro_s     |->  pro_s[self] ] >>
                                                         \o stack[self]]
                 /\ hourChosen_' = [hourChosen_ EXCEPT ![self] = 1]
                 /\ sellerAssosciated_' = [sellerAssosciated_ EXCEPT ![self] = 0]
                 /\ npc_' = [npc_ EXCEPT ![self] = 0]
                 /\ commodity1_' = [commodity1_ EXCEPT ![self] = 10]
                 /\ commodity2_' = [commodity2_ EXCEPT ![self] = 11]
                 /\ pc' = [pc EXCEPT ![self] = "settlementBuyer_"]
                 /\ UNCHANGED << attack, bankBalance, registry, 
                                 periodicEnergyBids, periodicEnergyOffers, 
                                 validBuyers, validSellers, validBuyers_copy, 
                                 validSellers_copy, validBuyerWallet, 
                                 mapBuyerToSeller, valBuyer, valSeller, 
                                 clearingPrice, temp, flagValBuyer, 
                                 finalValBuyer, flagBuyers, flagSellers, 
                                 SellerState, count_seller, count_buyer, 
                                 process_count, lockBuy, semaphore, flag1, 
                                 flag2, pro_, checkBuyer, UnmappedSellers, 
                                 pro_se, hourChosen, sellerAssosciated, npc, 
                                 commodity1, commodity2, pro_r, offer, price_, 
                                 pro_re, bid, price, pro_v, pro, other_, test, 
                                 other >>

buyer(self) == register_buyer(self) \/ validate_buyer(self)
                  \/ buy_energy(self) \/ Chill(self) \/ matching1(self)
                  \/ settlement1(self) \/ loopJO2(self)

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
                                         validSellers, validBuyers_copy, 
                                         validSellers_copy, validBuyerWallet, 
                                         mapBuyerToSeller, valBuyer, valSeller, 
                                         clearingPrice, temp, flagValBuyer, 
                                         finalValBuyer, flagBuyers, 
                                         flagSellers, BuyerState, SellerState, 
                                         count_seller, count_buyer, 
                                         process_count, lockSell, lockBuy, 
                                         semaphore, flag1, flag2, pro_, 
                                         checkBuyer, UnmappedSellers, pro_s, 
                                         hourChosen_, sellerAssosciated_, npc_, 
                                         commodity1_, commodity2_, pro_se, 
                                         hourChosen, sellerAssosciated, npc, 
                                         commodity1, commodity2, pro_r, offer, 
                                         price_, pro_re, bid, price, pro_v, 
                                         other_, test, other >>

validate(self) == /\ pc[self] = "validate"
                  /\ /\ pro_v' = [pro_v EXCEPT ![self] = self]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "validateAccount",
                                                              pc        |->  "sell_energy",
                                                              pro_v     |->  pro_v[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "ValidateProsumer"]
                  /\ UNCHANGED << attack, bankBalance, registry, 
                                  periodicEnergyBids, periodicEnergyOffers, 
                                  validBuyers, validSellers, validBuyers_copy, 
                                  validSellers_copy, validBuyerWallet, 
                                  mapBuyerToSeller, valBuyer, valSeller, 
                                  clearingPrice, temp, flagValBuyer, 
                                  finalValBuyer, flagBuyers, flagSellers, 
                                  BuyerState, SellerState, count_seller, 
                                  count_buyer, process_count, lockSell, 
                                  lockBuy, semaphore, flag1, flag2, pro_, 
                                  checkBuyer, UnmappedSellers, pro_s, 
                                  hourChosen_, sellerAssosciated_, npc_, 
                                  commodity1_, commodity2_, pro_se, hourChosen, 
                                  sellerAssosciated, npc, commodity1, 
                                  commodity2, pro_r, offer, price_, pro_re, 
                                  bid, price, pro, other_, test, other >>

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
                                     validBuyers_copy, validSellers_copy, 
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, finalValBuyer, flagBuyers, 
                                     flagSellers, BuyerState, SellerState, 
                                     count_seller, count_buyer, process_count, 
                                     lockSell, lockBuy, semaphore, flag1, 
                                     flag2, pro_, checkBuyer, UnmappedSellers, 
                                     pro_s, hourChosen_, sellerAssosciated_, 
                                     npc_, commodity1_, commodity2_, pro_se, 
                                     hourChosen, sellerAssosciated, npc, 
                                     commodity1, commodity2, pro_re, bid, 
                                     price, pro_v, pro, other_, test, other >>

matching2(self) == /\ pc[self] = "matching2"
                   /\ /\ pro_' = [pro_ EXCEPT ![self] = self]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "matching",
                                                               pc        |->  "settlement2",
                                                               checkBuyer |->  checkBuyer[self],
                                                               UnmappedSellers |->  UnmappedSellers[self],
                                                               pro_      |->  pro_[self] ] >>
                                                           \o stack[self]]
                   /\ checkBuyer' = [checkBuyer EXCEPT ![self] = defaultInitValue]
                   /\ UnmappedSellers' = [UnmappedSellers EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "checkEmptySeller"]
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   validBuyers, validSellers, validBuyers_copy, 
                                   validSellers_copy, validBuyerWallet, 
                                   mapBuyerToSeller, valBuyer, valSeller, 
                                   clearingPrice, temp, flagValBuyer, 
                                   finalValBuyer, flagBuyers, flagSellers, 
                                   BuyerState, SellerState, count_seller, 
                                   count_buyer, process_count, lockSell, 
                                   lockBuy, semaphore, flag1, flag2, pro_s, 
                                   hourChosen_, sellerAssosciated_, npc_, 
                                   commodity1_, commodity2_, pro_se, 
                                   hourChosen, sellerAssosciated, npc, 
                                   commodity1, commodity2, pro_r, offer, 
                                   price_, pro_re, bid, price, pro_v, pro, 
                                   other_, test, other >>

settlement2(self) == /\ pc[self] = "settlement2"
                     /\ IF self \in validSellers
                           THEN /\ lockBuy' = TRUE
                                /\ pc' = [pc EXCEPT ![self] = "loopJO1"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED lockBuy
                     /\ UNCHANGED << attack, bankBalance, registry, 
                                     periodicEnergyBids, periodicEnergyOffers, 
                                     validBuyers, validSellers, 
                                     validBuyers_copy, validSellers_copy, 
                                     validBuyerWallet, mapBuyerToSeller, 
                                     valBuyer, valSeller, clearingPrice, temp, 
                                     flagValBuyer, finalValBuyer, flagBuyers, 
                                     flagSellers, BuyerState, SellerState, 
                                     count_seller, count_buyer, process_count, 
                                     lockSell, semaphore, flag1, flag2, stack, 
                                     pro_, checkBuyer, UnmappedSellers, pro_s, 
                                     hourChosen_, sellerAssosciated_, npc_, 
                                     commodity1_, commodity2_, pro_se, 
                                     hourChosen, sellerAssosciated, npc, 
                                     commodity1, commodity2, pro_r, offer, 
                                     price_, pro_re, bid, price, pro_v, pro, 
                                     other_, test, other >>

loopJO1(self) == /\ pc[self] = "loopJO1"
                 /\ flagSellers = FALSE
                 /\ /\ pro_se' = [pro_se EXCEPT ![self] = self]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "settlementSeller",
                                                             pc        |->  "Done",
                                                             hourChosen |->  hourChosen[self],
                                                             sellerAssosciated |->  sellerAssosciated[self],
                                                             npc       |->  npc[self],
                                                             commodity1 |->  commodity1[self],
                                                             commodity2 |->  commodity2[self],
                                                             pro_se    |->  pro_se[self] ] >>
                                                         \o stack[self]]
                 /\ hourChosen' = [hourChosen EXCEPT ![self] = 1]
                 /\ sellerAssosciated' = [sellerAssosciated EXCEPT ![self] = pro_se'[self]]
                 /\ npc' = [npc EXCEPT ![self] = 0]
                 /\ commodity1' = [commodity1 EXCEPT ![self] = 10]
                 /\ commodity2' = [commodity2 EXCEPT ![self] = 11]
                 /\ pc' = [pc EXCEPT ![self] = "settlement"]
                 /\ UNCHANGED << attack, bankBalance, registry, 
                                 periodicEnergyBids, periodicEnergyOffers, 
                                 validBuyers, validSellers, validBuyers_copy, 
                                 validSellers_copy, validBuyerWallet, 
                                 mapBuyerToSeller, valBuyer, valSeller, 
                                 clearingPrice, temp, flagValBuyer, 
                                 finalValBuyer, flagBuyers, flagSellers, 
                                 BuyerState, SellerState, count_seller, 
                                 count_buyer, process_count, lockSell, lockBuy, 
                                 semaphore, flag1, flag2, pro_, checkBuyer, 
                                 UnmappedSellers, pro_s, hourChosen_, 
                                 sellerAssosciated_, npc_, commodity1_, 
                                 commodity2_, pro_r, offer, price_, pro_re, 
                                 bid, price, pro_v, pro, other_, test, other >>

seller(self) == register_seller(self) \/ validate(self)
                   \/ sell_energy(self) \/ matching2(self)
                   \/ settlement2(self) \/ loopJO1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ matching(self) \/ settlementBuyer(self)
                               \/ settlementSeller(self)
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
                                /\ WF_vars(settlementBuyer(self))
        /\ \A self \in Sellers : /\ WF_vars(seller(self))
                                 /\ WF_vars(registerAccount(self))
                                 /\ WF_vars(validateAccount(self))
                                 /\ WF_vars(registerMarketSellOrder(self))
                                 /\ WF_vars(matching(self))
                                 /\ WF_vars(settlementSeller(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Mar 17 17:08:53 GMT 2024 by naufa
\* Created Fri Jan 05 10:01:04 GMT 2024 by naufa
