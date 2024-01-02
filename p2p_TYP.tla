------------------------------ MODULE p2p_TYP ------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANT BALANCE, AMOUNT, 
Buyers, Sellers,
EnergyOfferAmounts, EnergyOfferPrices,
EnergyBidAmounts, EnergyBidPrices,
EnergyBidAmountsSorted, EnergyBidPricesSorted


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
  
  bid = 0, offer = 0; \* For usage with registerMarketSellOrder
  validBuyers = {}, validSellers = {},
  test = 0, price= 0,
  clearingPrice = 0;

(* Invariant Proposals
(1) Prevent Attacks
(2) Consistent Transaction
*)
define
  SafeWithdrawal == 
      \/ (bankBalance=BALANCE-AMOUNT)
  (*Ensures that all sellers & buyers participating     are validated before market session ends*)
  BuyersValidated ==  
    \/ \A x \in validBuyers : x \in Buyers
  SellersValidated ==
   \/ \A x \in validSellers : x \in Sellers
end define;

macro matchingEnergy(periodicEnergyBids)
begin
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

macro ValidateSellers(Sellers, registry)
begin
   validSellers := {p \in Sellers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
end macro;

macro registerMarketSellOrder (Sellers, registry) 
begin
    \* validate the registry again to see if there is non-validated buyers
    ValidateSellers(Sellers,registry);
    getEnergyOffer(validSellers, 2, offer, price);
end macro;

macro registerSellers(Sellers)
begin
    registry := [p \in Prosumers |-> IF p \in Sellers THEN [valid |-> FALSE, reputation |-> 0] ELSE p];
end macro


(*----BUYERS/BIDDING SECTION------*)

macro getEnergyBid(validBuyers, h, bid, price)
begin
     with x \in validBuyers do 
        bid := periodicEnergyBids[x][1][h];
        price := periodicEnergyBids[x][2][h];
        print <<"Bid:",bid,"Price:",price,"Buyers:", x>>;
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
end macro;

\* macro that registers prosumers -- maps it to registry
macro registerAccount(Buyers)
begin
    registry := [p \in Prosumers |-> IF p \in Buyers THEN [valid |-> FALSE, reputation |-> 0] ELSE p];
end macro

macro validateAccount(Sequence)
begin
      registry := [x \in Prosumers |-> IF x \in Sequence THEN [valid |-> TRUE, reputation |-> registry[x].reputation + 1] ELSE x];
end macro

begin
  register_buyer:
     registerAccount(Buyers); \*register buyers
  validate_buyer: 
    validateAccount(Buyers);   \*validate buyers
  buy_energy:
    registerMarketBuyOrder(Buyers, registry);
  
  register_seller:
    registerAccount(Sellers);
  validate:
    validateAccount(Sellers);
  validate_seller:
    ValidateSellers(Sellers, registry);
  sell_energy:
    registerMarketSellOrder(Sellers, registry);
  
  matching:
    matchingEnergy(periodicEnergyBids);
    
  settlement:
    bankBalance := BALANCE - AMOUNT;    

end algorithm*)

\* BEGIN TRANSLATION (chksum(pcal) = "3036bd10" /\ chksum(tla) = "a2415340")
VARIABLES attack, bankBalance, registry, periodicEnergyBids, 
          periodicEnergyOffers, bid, offer, validBuyers, validSellers, test, 
          price, clearingPrice, pc

(* define statement *)
SafeWithdrawal ==
    \/ (bankBalance=BALANCE-AMOUNT)

BuyersValidated ==
  \/ \A x \in validBuyers : x \in Buyers
SellersValidated ==
 \/ \A x \in validSellers : x \in Sellers


vars == << attack, bankBalance, registry, periodicEnergyBids, 
           periodicEnergyOffers, bid, offer, validBuyers, validSellers, test, 
           price, clearingPrice, pc >>

Init == (* Global variables *)
        /\ attack = 0
        /\ bankBalance = BALANCE
        /\ registry = [p \in Prosumers |-> [valid |-> FALSE, reputation |-> 0]]
        /\ periodicEnergyBids = [b \in Buyers |-> PeriodicBidList]
        /\ periodicEnergyOffers = [s \in Sellers |-> PeriodicOfferList]
        /\ bid = 0
        /\ offer = 0
        /\ validBuyers = {}
        /\ validSellers = {}
        /\ test = 0
        /\ price = 0
        /\ clearingPrice = 0
        /\ pc = "register_buyer"

register_buyer == /\ pc = "register_buyer"
                  /\ registry' = [p \in Prosumers |-> IF p \in Buyers THEN [valid |-> FALSE, reputation |-> 0] ELSE p]
                  /\ pc' = "validate_buyer"
                  /\ UNCHANGED << attack, bankBalance, periodicEnergyBids, 
                                  periodicEnergyOffers, bid, offer, 
                                  validBuyers, validSellers, test, price, 
                                  clearingPrice >>

validate_buyer == /\ pc = "validate_buyer"
                  /\ registry' = [x \in Prosumers |-> IF x \in Buyers THEN [valid |-> TRUE, reputation |-> registry[x].reputation + 1] ELSE x]
                  /\ pc' = "buy_energy"
                  /\ UNCHANGED << attack, bankBalance, periodicEnergyBids, 
                                  periodicEnergyOffers, bid, offer, 
                                  validBuyers, validSellers, test, price, 
                                  clearingPrice >>

buy_energy == /\ pc = "buy_energy"
              /\ validBuyers' = {p \in Buyers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
              /\ \E x \in validBuyers':
                   /\ bid' = periodicEnergyBids[x][1][2]
                   /\ price' = periodicEnergyBids[x][2][2]
                   /\ PrintT(<<"Bid:",bid',"Price:",price',"Buyers:", x>>)
              /\ pc' = "register_seller"
              /\ UNCHANGED << attack, bankBalance, registry, 
                              periodicEnergyBids, periodicEnergyOffers, offer, 
                              validSellers, test, clearingPrice >>

register_seller == /\ pc = "register_seller"
                   /\ registry' = [p \in Prosumers |-> IF p \in Sellers THEN [valid |-> FALSE, reputation |-> 0] ELSE p]
                   /\ pc' = "validate"
                   /\ UNCHANGED << attack, bankBalance, periodicEnergyBids, 
                                   periodicEnergyOffers, bid, offer, 
                                   validBuyers, validSellers, test, price, 
                                   clearingPrice >>

validate == /\ pc = "validate"
            /\ registry' = [x \in Prosumers |-> IF x \in Sellers THEN [valid |-> TRUE, reputation |-> registry[x].reputation + 1] ELSE x]
            /\ pc' = "validate_seller"
            /\ UNCHANGED << attack, bankBalance, periodicEnergyBids, 
                            periodicEnergyOffers, bid, offer, validBuyers, 
                            validSellers, test, price, clearingPrice >>

validate_seller == /\ pc = "validate_seller"
                   /\ validSellers' = {p \in Sellers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
                   /\ pc' = "sell_energy"
                   /\ UNCHANGED << attack, bankBalance, registry, 
                                   periodicEnergyBids, periodicEnergyOffers, 
                                   bid, offer, validBuyers, test, price, 
                                   clearingPrice >>

sell_energy == /\ pc = "sell_energy"
               /\ validSellers' = {p \in Sellers : registry[p].valid = TRUE /\ registry[p].reputation > 0}
               /\ \E x \in validSellers':
                    /\ offer' = periodicEnergyOffers[x][1][2]
                    /\ price' = periodicEnergyOffers[x][2][2]
                    /\ PrintT(<<"Offers:",offer',"Price:",price',"Sellers:", x>>)
               /\ pc' = "matching"
               /\ UNCHANGED << attack, bankBalance, registry, 
                               periodicEnergyBids, periodicEnergyOffers, bid, 
                               validBuyers, test, clearingPrice >>

matching == /\ pc = "matching"
            /\ periodicEnergyBids' = [b \in validBuyers |-> <<EnergyBidAmountsSorted, EnergyBidPricesSorted>>]
            /\ clearingPrice' = 2
            /\ pc' = "settlement"
            /\ UNCHANGED << attack, bankBalance, registry, 
                            periodicEnergyOffers, bid, offer, validBuyers, 
                            validSellers, test, price >>

settlement == /\ pc = "settlement"
              /\ bankBalance' = BALANCE - AMOUNT
              /\ pc' = "Done"
              /\ UNCHANGED << attack, registry, periodicEnergyBids, 
                              periodicEnergyOffers, bid, offer, validBuyers, 
                              validSellers, test, price, clearingPrice >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == register_buyer \/ validate_buyer \/ buy_energy \/ register_seller
           \/ validate \/ validate_seller \/ sell_energy \/ matching
           \/ settlement
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

\*macro determineClearingPrice(seq1, seq2)
\*begin
\*    while (i <= Len(seq1) /\ j >= 1) do
\*    if seq1[2][i] < seq2[2][j] then
\*      i := i + 1;
\*    elsif (seq1[2][i] > seq2[2][j]) then
\*      j := j - 1;
\*    else 
\*      lowestSimilar := seq1[2][i];
\*      end if;
\*   end while;
\*  
\*  print lowestSimilar;
\*  i := 1;
\*  j := 1;
\*  temp := 0;
\*end macro
\*
\*macro sortDesc(seq)
\*begin
\*  while (i <= Len(seq)) do
\*    j := 1;
\*    if (j <= Len(seq) - i) then
\*      if (seq[2][j] < seq[2][j+1]) then
\*        temp := seq[2][j];
\*        seq[2][j] := seq[2][j+1];
\*        seq[2][j+1] := temp;
\*      end if;
\*      j := j + 1;
\*
\*    i := i + 1;
\*   end if;
\*  end while;
\*  i := 1;
\*  j := 1;
\*  temp := 0;
\*end macro
\*
\*macro sortAsc(seq)
\*begin
\*  while (i <= Len(seq)) do
\*    j := 1;
\*    while (j <= Len(seq) - i) do
\*      if (seq[2][j] > seq[2][j+1]) then
\*        temp := seq[2][j];
\*        seq[2][j] := seq[2][j+1];
\*        seq[2][j+1] := temp;
\*      end if;
\*      j := j + 1;
\*    end while;
\*    i := i + 1;
\*  end while;
\*  i := 1;
\*  j := 1;
\*  temp := 0;
\*end macro
\*
\*macro matchingEnergy(periodicEnergyOffers, periodicEnergyBids)
\*begin
\*    \* sorts offer price ascending and bid price descending
\*    sortAsc(periodicEnergyOffers);
\*    sortDesc(periodicEnergyBids); 
\*    determineClearingPrice(periodicEnergyOffers, periodicEnergyBids);
\*end macro

=============================================================================
\* Modification History
\* Last modified Sun Dec 31 22:29:16 GMT 2023 by naufa
\* Created Thu Nov 16 09:31:42 GMT 2023 by naufa
