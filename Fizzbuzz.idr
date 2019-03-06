import Syntax.PreorderReasoning

%default total

-- Our own Nat, because we want to be in control

%hide Nat
%hide LTE
%hide minus

data Nat : Type where
  Z : Nat
  S : Nat -> Nat

-- Equality

DecEq Nat where
  decEq Z Z = Yes Refl
  decEq Z (S m) = No $ \Refl impossible
  decEq (S n) Z = No $ \Refl impossible
  decEq (S n) (S m) = case decEq n m of
                           Yes Refl => Yes Refl
                           No contra => No $ \Refl => contra Refl

Uninhabited (S k = Z) where
  uninhabited Refl impossible

Uninhabited (Z = S k) where
  uninhabited Refl impossible

-- Num instances

infixl 8 .+.
(.+.) : Nat -> Nat -> Nat
(.+.) Z y = y
(.+.) (S x) y = S (x .+. y)

infixl 9 .*.
(.*.) : Nat -> Nat -> Nat
(.*.) Z _ = Z
(.*.) (S n) m = m .+. (n .*. m)

Num Nat where
  (+) = (.+.)
  (*) = (.*.)
  fromInteger k = if k <= 0
                     then Z
                     else S $ fromInteger $ assert_smaller k (k - 1)

-- Addition

plusRightZero : (n : Nat) -> n = n + Z
plusRightZero Z = Refl
plusRightZero (S n) = cong $ plusRightZero n

plusRightS : (n, m : Nat) -> n + S m = S (n + m)
plusRightS Z m = Refl
plusRightS (S n) m = cong $ plusRightS n m

plusCommutes : (n, m : Nat) -> n + m = m + n
plusCommutes Z m = plusRightZero m
plusCommutes (S n) m = rewrite plusCommutes n m in sym $ plusRightS m n

plusAssoc : (n, m, k : Nat) -> n + (m + k) = (n + m) + k
plusAssoc Z m k = Refl
plusAssoc (S n) m k = cong $ plusAssoc n m k

plusAssocSym : (n, m, k : Nat) -> (n + m) + k = n + (m + k)
plusAssocSym n m k = sym $ plusAssoc n m k

plusLeftPreservesEq : (n, m, k : Nat) -> n = m -> k + n = k + m
plusLeftPreservesEq n n k Refl = Refl

plusRightPreservesEq : (n, m, k : Nat) -> n = m -> n + k = m + k
plusRightPreservesEq n n k Refl = Refl

-- Multiplication

timesLeftOne : (n : Nat) -> n = 1 * n
timesLeftOne n = plusRightZero n

timesRightOne : (n : Nat) -> n = n * 1
timesRightOne Z = Refl
timesRightOne (S n) = rewrite timesRightOne n in Refl

timesRightZero : (n : Nat) -> Z = n * Z
timesRightZero Z = Refl
timesRightZero (S n) = timesRightZero n

timesPlusSRight : (n, m : Nat) -> n + n * m = n * S m
timesPlusSRight Z m = Refl
timesPlusSRight (S n) m = rewrite sym $ timesPlusSRight n m in
                          rewrite plusAssoc n m (n * m) in
                          rewrite plusAssoc m n (n * m) in
                          rewrite plusCommutes n m in Refl

timesCommutes : (n, m : Nat) -> n * m = m * n
timesCommutes Z m = timesRightZero m
timesCommutes (S n) m = rewrite sym $ timesPlusSRight m n in
                        rewrite timesCommutes n m in Refl


timesDistrLeft : (n, m, k : Nat) -> k * (n + m) = k * n + k * m
timesDistrLeft n m Z = Refl
timesDistrLeft n m (S k) = rewrite timesDistrLeft n m k in
                           rewrite shuffleLemma n m (k * n) (k * m) in Refl
  where
    shuffleLemma : (n, m, kn, km : Nat) -> (n + m) + (kn + km) = (n + kn) + (m + km)
    shuffleLemma n m kn km =
      ((n + m) + (kn + km)) ={ plusAssocSym n m (kn + km) }=
      (n + (m + (kn + km))) ={ cong $ plusAssoc m kn km }=
      (n + ((m + kn) + km)) ={ cong { f = \x => n + (x + km) } $ plusCommutes m kn }=
      (n + ((kn + m) + km)) ={ cong $ plusAssocSym kn m km }=
      (n + (kn + (m + km))) ={ plusAssoc n kn (m + km) }=
      ((n + kn) + (m + km)) QED

timesDistrRight : (n, m, k : Nat) -> (n + m) * k = n * k + m * k
timesDistrRight n m k = rewrite timesCommutes (n + m) k in
                        rewrite timesDistrLeft n m k in
                        rewrite timesCommutes n k in
                        rewrite timesCommutes m k in
                        Refl

timesAssoc : (n, m, k : Nat) -> n * (m * k) = (n * m) * k
timesAssoc Z m k = Refl
timesAssoc (S n) m k = rewrite timesAssoc n m k in
                       rewrite sym $ timesDistrRight m (n * m) k in
                       Refl


-- Inequality

data LTE : (l, r : Nat) -> Type where
  LTEZ : LTE Z r
  LTES : (prevPrf : LTE l r) -> LTE (S l) (S r)

lte : (l, r : Nat) -> Dec (LTE l r)
lte Z r = Yes LTEZ
lte (S l) Z = No contraBase
  where
    contraBase : LTE (S l) Z -> Void
    contraBase LTEZ impossible
    contraBase (LTES _) impossible
lte (S l) (S r) = case lte l r of
                       Yes prf => Yes (LTES prf)
                       No contra => No (contraStep contra)
  where
    contraStep : (LTE l r -> Void) -> LTE (S l) (S r) -> Void
    contraStep contra (LTES prevPrf) = contra prevPrf

%hint
lteRefl : (n : Nat) -> LTE n n
lteRefl Z = LTEZ
lteRefl (S n) = LTES (lteRefl n)

%hint
lteWeakenS : LTE n m -> LTE n (S m)
lteWeakenS {n = Z} LTEZ = LTEZ
lteWeakenS {n = S l} {m = S r} (LTES prevPrf) = LTES $ lteWeakenS prevPrf

lteWeaken : (k : Nat) -> l `LTE` r -> l `LTE` k + r
lteWeaken Z prf = prf
lteWeaken (S k) prf = lteWeakenS $ lteWeaken k prf

LT : (l, r : Nat) -> Type
LT l r = LTE (S l) r

lt : (l, r : Nat) -> Dec (LT l r)
lt l r = lte (S l) r

invertLte : (l, r : Nat) -> Not (l `LTE` r) -> r `LT` l
invertLte Z r contra = void $ contra LTEZ
invertLte (S l) Z contra = LTES LTEZ
invertLte (S l) (S r) contra = let rec = invertLte l r (\prf => contra $ LTES prf) in LTES rec

ltWeakenLte : (l, r : Nat) -> l `LT` r -> l `LTE` r
ltWeakenLte l r prf = let LTES prev = lteWeakenS prf in prev

-- Inequality and plus

summandLTEsum : (n, m : Nat) -> m `LTE` n + m
summandLTEsum n m = lteWeaken n $ lteRefl m

sumLTEcancelLeft : {n1, n2 : Nat} -> (m : Nat) -> (prf : m + n1 `LTE` m + n2) -> n1 `LTE` n2
sumLTEcancelLeft Z prf = prf
sumLTEcancelLeft (S m) (LTES prevPrf) = sumLTEcancelLeft m prevPrf

-- Safe subtraction

minus : (n, m : Nat) -> { auto prf : m `LTE` n } -> Nat
minus { prf = LTEZ } n Z = n
minus { prf = LTES prevPrf } (S n) (S m) = minus n m

minusSelf : (n : Nat) -> n `minus` n = 0
minusSelf Z = Refl
minusSelf (S n) = minusSelf n

minusSLeftCommutes : (n, m : Nat) -> (prf : m `LTE` n) -> minus (S n) m = S (minus n m)
minusSLeftCommutes n Z LTEZ = Refl
minusSLeftCommutes (S r) (S l) (LTES prevPrf) = minusSLeftCommutes r l prevPrf

minusPlusCancels : (n, m : Nat) -> (prf : m `LTE` n) -> (n `minus` m) + m = n
minusPlusCancels n Z LTEZ = sym $ plusRightZero _
minusPlusCancels (S n) (S m) (LTES prevPrf) = rewrite plusRightS (n `minus` m) m in
                                              rewrite minusPlusCancels n m prevPrf in
                                              Refl

minusS : (n, m : Nat) -> (prf1 : m `LTE` n) -> (prf2 : m `LTE` S n) -> minus (S n) m = S (minus n m)
minusS n Z LTEZ LTEZ = Refl
minusS (S n) (S m) (LTES prevPrf1) (LTES prevPrf2) = minusS n m prevPrf1 prevPrf2

minusSS : (n, m : Nat) -> { auto prf : m `LTE` n } -> minus (S n) (S m) = minus n m
minusSS { prf = LTEZ } n Z = Refl
minusSS { prf = LTES prevPrf } (S n) (S m) = Refl

proofIrrelevanceForMinus : (prf1, prf2 : m `LTE` n) -> minus { prf = prf1 } n m = minus { prf = prf2 } n m
proofIrrelevanceForMinus LTEZ LTEZ = Refl
proofIrrelevanceForMinus (LTES prevPrf1) (LTES prevPrf2) = proofIrrelevanceForMinus prevPrf1 prevPrf2

minusReflLeft : { n1, n2, m : Nat } -> (prf : n1 = n2) -> (prf_n1 : m `LTE` n1) -> (prf_n2 : m `LTE` n2) -> n1 `minus` m = n2 `minus` m
minusReflLeft Refl LTEZ LTEZ = Refl
minusReflLeft Refl (LTES prev1) (LTES prev2) = minusReflLeft Refl prev1 prev2

plusMinusCancelsRight : (n, m : Nat) -> { auto prf : m `LTE` n + m } -> minus (n + m) m = n
plusMinusCancelsRight {prf = LTEZ} n Z = sym $ plusRightZero n
plusMinusCancelsRight {prf} n (S m) =
  rewrite minusReflLeft (plusRightS n m) prf (LTES $ summandLTEsum n m)
  in plusMinusCancelsRight { prf = summandLTEsum n m } n m

plusMinusCancelsLeft : (n, m : Nat) -> { auto prf : n `LTE` n + m } -> minus (n + m) n = m
plusMinusCancelsLeft {prf} n m =
  rewrite minusReflLeft (plusCommutes n m) prf (summandLTEsum m n)
  in plusMinusCancelsRight m n

minusPlusTossS : (n, m, k : Nat) -> { auto prf1 : k `LTE` n + S m } -> { auto prf2 : k `LTE` S n + m } -> minus (n + S m) k = minus (S n + m) k
minusPlusTossS {prf1} {prf2} n m k = minusReflLeft (plusRightS n m) prf1 prf2

plusMinusAssoc : (n, m, k : Nat) -> { auto prf1 : k `LTE` n + m } -> { auto prf2 : k `LTE` m } -> (n + m) `minus` k = n + (m `minus` k)
plusMinusAssoc { prf1 = LTEZ } { prf2 = LTEZ } n m Z = Refl
plusMinusAssoc { prf1 = LTES prevPrf1 } { prf2 = LTES prevPrf2 } Z (S m) (S k) = proofIrrelevanceForMinus prevPrf1 prevPrf2
plusMinusAssoc { prf1 = LTES prevPrf1 } { prf2 = LTES prevPrf2 } (S n) (S m) (S k) =
  let l_lte_nr = lteWeaken n prevPrf2
      l_lte_S_nr = lteWeakenS l_lte_nr
  in
  ((n + S m) `minus` k)   ={ minusPlusTossS n m k }=
  ((S n + m) `minus` k)   ={ minusS (n + m) k (lteWeaken n prevPrf2) l_lte_S_nr }=
  (S ((n + m) `minus` k)) ={ cong $ plusMinusAssoc n m k }=
  (S (n + (m `minus` k))) QED

-- Helpers

NotZero : (n : Nat) -> Type
NotZero n = Not (n = Z)

%hint
sNotZero : NotZero (S k)
sNotZero = uninhabited

-- Division

data Div : (n, d, q, r : Nat) -> Type where
  MkDiv : (eqPrf : q * d + r = n) -> (lessPrf : r `LT` d) -> Div n d q r

divide' : (n, d : Nat) -> { auto notZero : NotZero d } -> (q ** r ** Div n d q r)
divide' {notZero} n d with (n `lt` d)
  | Yes lessPrf = (0 ** n ** MkDiv Refl lessPrf)
  | No contra = let LTES dnPrf = invertLte _ _ contra
                    (q ** r ** MkDiv eqPrf lessPrf) = assert_total $ divide' {notZero} (n `minus` d) d
                    in (S q ** r ** MkDiv (stepEqPrf q r dnPrf eqPrf) lessPrf)
    where
      stepEqPrf : (q, r : Nat) -> (dnPrf : LTE d n) -> (eqPrf : q * d + r = minus n d) -> (S q) * d + r = n
      stepEqPrf q r dnPrf eqPrf = rewrite sym $ leftPart in
                                  rewrite sym $ minusPlusCancels n d dnPrf in
                                  plusRightPreservesEq _ _ d eqPrf
        where
          leftPart : (q * d + r) + d = (S q) * d + r
          leftPart =
            ((q * d + r) + d) ={ plusAssocSym (q * d) r d }=
            (q * d + (r + d)) ={ cong $ plusCommutes r d }=
            (q * d + (d + r)) ={ plusAssoc (q * d) d r }=
            ((q * d + d) + r) ={ cong { f = \x => x + r } $ plusCommutes (q * d) d }=
            ((d + q * d) + r) ={ Refl }=
            ((S q) * d + r) QED

lemma1 : { k, r, k', r' : Nat } -> { auto ltePrf : r `LTE` r' } -> k' + r' = k + r -> k' + (r' `minus` r) = k
lemma1 {k} {r} {k'} {r'} {ltePrf} eqPrf =
  let r_lte_kr' = lteWeaken k ltePrf
      r_lte_kr'' = lteWeaken k' ltePrf
      r_lte_kr = summandLTEsum k r
  in
  (k' + (r' `minus` r)) ={ sym $ plusMinusAssoc k' r' r }=
  ((k' + r') `minus` r) ={ minusReflLeft eqPrf r_lte_kr'' r_lte_kr }=
  ((k + r) `minus` r) ={ sub k r r_lte_kr }=
  (k + Z) ={ sym $ plusRightZero k }=
  (k) QED
  where
    sub : (k, r : Nat) -> (prf : r `LTE` k + r) -> (k + r) `minus` r = k + Z
    sub k r prf = rewrite plusMinusAssoc k r r in rewrite minusSelf r in Refl

divEqualQBase : (n, d, q, q', r, r' : Nat) -> (rPrf : r `LTE` r') -> (div1 : Div n d q r) -> (div2 : Div n d q' r') -> q = q'
divEqualQBase n d q q' r r' rPrf (MkDiv eqPrf1 lessPrf1) (MkDiv eqPrf2 lessPrf2) =
  let r'_minus_r = r' `minus` r
      eqPrf = trans eqPrf1 $ sym eqPrf2
  in ?divEqualQBase_rhs

divEqualQ : (div1 : Div n d q r) -> (div2 : Div n d q' r') -> q = q'
divEqualQ {r} {r'} div1 div2 =
  case r `lte` r' of
       Yes prf => divEqualQBase _ _ _ _ _ _ prf div1 div2
       No contra => let inv = ltWeakenLte _ _ $ invertLte _ _ contra
                    in sym $ divEqualQBase _ _ _ _ _ _ inv div2 div1

divEqualR : (div1 : Div n d q r) -> (div2 : Div n d q' r') -> r = r'

data Remainder : (n, d, r : Nat) -> Type where
  MkRemainder : (q : Nat) -> (prf : Div n d q r) -> Remainder n d r

decRem : (n, d, r : Nat) -> (notZero : NotZero d) -> Dec (Remainder n d r)
decRem n d r notZero =
  let (q' ** r' ** div') = divide' {notZero} n d in
  case decEq r r' of
       Yes Refl => Yes (MkRemainder q' div')
       No contra => No (\(MkRemainder q div) => void $ contra $ divEqualR div div')

data Output = OutFizz
            | OutBuzz
            | OutFizzBuzz
            | OutNum Nat

infixl 9 .|.
(.|.) : Nat -> Nat -> Type
r .|. n = Remainder n r 0

data OutVerified : Nat -> Output -> Type where
  MkOutFizz     : (n : Nat) -> (prf3 : 3 .|.n)         -> (nprf5 : Not (5 .|. n)) -> OutVerified n OutFizz
  MkOutBuzz     : (n : Nat) -> (nprf3 : Not (3 .|. n)) -> (prf5 : 5 .|. n)        -> OutVerified n OutBuzz
  MkOutFizzBuzz : (n : Nat) -> (prf3 : 3 .|. n)        -> (prf5 : 5 .|. n)        -> OutVerified n OutFizzBuzz
  MkOutNum      : (n : Nat) -> (nprf3 : Not (3 .|. n)) -> (nprf5 : Not (5 .|. n)) -> OutVerified n (OutNum n)

fizzbuzz : (n : Nat) -> (out ** OutVerified n out)
fizzbuzz n with (decRem n 3 0 sNotZero, decRem n 5 0 sNotZero)
  | (Yes div3, Yes div5) = (_ ** MkOutFizzBuzz n div3 div5)
  | (Yes div3, No ndiv5) = (_ ** MkOutFizz n div3 ndiv5)
  | (No ndiv3, Yes div5) = (_ ** MkOutBuzz n ndiv3 div5)
  | (No ndiv3, No ndiv5) = (_ ** MkOutNum n ndiv3 ndiv5)
