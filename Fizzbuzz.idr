import Control.WellFounded
import Decidable.Equality
import Syntax.PreorderReasoning

%default total

-- Our own Nat, because we want to be in control

%hide Nat
%hide Z
%hide S
%hide minus

data Nat : Type where
  Z : Nat
  S : Nat -> Nat

-- Equality

DecEq Nat where
  decEq Z Z = Yes Refl
  decEq Z (S m) = No $ \case Refl impossible
  decEq (S n) Z = No $ \case Refl impossible
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

-- Basic Nat properties

sInjective : (prf : S n = S m) -> n = m
sInjective Refl = Refl

-- Addition

plusRightZero : (n : Nat) -> n = n + Z
plusRightZero Z = Refl
plusRightZero (S n) = cong S $ plusRightZero n

plusRightS : (n, m : Nat) -> n + S m = S (n + m)
plusRightS Z m = Refl
plusRightS (S n) m = cong S $ plusRightS n m

plusCommutes : (n, m : Nat) -> n + m = m + n
plusCommutes Z m = plusRightZero m
plusCommutes (S n) m = rewrite plusCommutes n m in sym $ plusRightS m n

plusAssoc : (n, m, k : Nat) -> n + (m + k) = (n + m) + k
plusAssoc Z m k = Refl
plusAssoc (S n) m k = cong S $ plusAssoc n m k

plusAssocSym : (n, m, k : Nat) -> (n + m) + k = n + (m + k)
plusAssocSym n m k = sym $ plusAssoc n m k

plusLeftPreservesEq : (n, m, k : Nat) -> n = m -> k + n = k + m
plusLeftPreservesEq n n k Refl = Refl

plusRightPreservesEq : (n, m, k : Nat) -> n = m -> n + k = m + k
plusRightPreservesEq n n k Refl = Refl

plusCancelsLeft : (n : Nat) -> n + k1 = n + k2 -> k1 = k2
plusCancelsLeft Z prf = prf
plusCancelsLeft (S n) prf = plusCancelsLeft n (sInjective prf)

-- Multiplication

timesLeftOne : (n : Nat) -> n = 1 * n
timesLeftOne n = plusRightZero n

timesRightOne : (n : Nat) -> n = n * 1
timesRightOne Z = Refl
timesRightOne (S n) = cong S $ timesRightOne n

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
    shuffleLemma n m kn km = Calc $
      |~ ((n + m) + (kn + km))
      ~~ (n + (m + (kn + km))) ...( plusAssocSym n m (kn + km) )
      ~~ (n + ((m + kn) + km)) ...( cong (n +) $ plusAssoc m kn km )
      ~~ (n + ((kn + m) + km)) ...( cong (\x => n + (x + km)) $ plusCommutes m kn )
      ~~ (n + (kn + (m + km))) ...( cong (n +) $ plusAssocSym kn m km )
      ~~ ((n + kn) + (m + km)) ...( plusAssoc n kn (m + km) )

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

-- Helpers

NotZero : (n : Nat) -> Type
NotZero n = Not (n = Z)

%hint
sNotZero : NotZero (S k)
sNotZero = uninhabited


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

lteCongRight : {l, r1, r2 : Nat} -> (prf : r1 = r2) -> l `LTE` r1 -> l `LTE` r2
lteCongRight Refl ltePrf = ltePrf

lteCongLeft : {l1, l2, r : Nat} -> (prf : l1 = l2) -> l1 `LTE` r -> l2 `LTE` r
lteCongLeft Refl ltePrf = ltePrf

lteWeakenRight : {r, l : _} -> (k : Nat) -> l `LTE` r -> l `LTE` r + k
lteWeakenRight {r} k prf = lteCongRight (plusCommutes k r) $ lteWeaken k prf

Uninhabited (S k `LTE` Z) where
  uninhabited LTEZ impossible
  uninhabited (LTES _) impossible

Uninhabited (S k `LTE` k) where
  uninhabited (LTES prevPrf) = uninhabited prevPrf

lteTrans : (a, b, c : Nat) -> a `LTE` b -> b `LTE` c -> a `LTE` c
lteTrans Z _ _ _ _ = LTEZ
lteTrans (S a) (S b) (S c) (LTES prev_lte_ab) (LTES prev_lte_bc) = LTES $ lteTrans a b c prev_lte_ab prev_lte_bc

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

ltImpliesNonZero : {l, r : Nat} -> l `LT` r -> NotZero r
ltImpliesNonZero {r = Z} ltePrf eqPrf = uninhabited ltePrf
ltImpliesNonZero {r = S r} ltePrf eqPrf = uninhabited eqPrf

-- Inequality and plus

summandLTEsum : (n, m : Nat) -> m `LTE` n + m
summandLTEsum n m = lteWeaken n $ lteRefl m

sumLTEcancelLeft : {n1, n2 : Nat} -> (m : Nat) -> (prf : m + n1 `LTE` m + n2) -> n1 `LTE` n2
sumLTEcancelLeft Z prf = prf
sumLTEcancelLeft (S m) (LTES prevPrf) = sumLTEcancelLeft m prevPrf

-- Inequality and multiplication

multLTEcancelRight : (n1, n2, m : Nat) -> (notZero : NotZero m) -> (ltePrf : n1 * m `LTE` n2 * m) -> n1 `LTE` n2
multLTEcancelRight _ _ Z notZero _ = absurd $ notZero Refl
multLTEcancelRight Z _ _ _ _ = LTEZ
multLTEcancelRight (S n1) Z (S m) _ ltePrf = absurd ltePrf
multLTEcancelRight (S n1) (S n2) (S m) notZero (LTES prevPrf) =
  let sumPrf = sumLTEcancelLeft {n1 = n1 * S m} {n2 = n2 * S m} m prevPrf
      rec = multLTEcancelRight n1 n2 (S m) notZero sumPrf
  in LTES rec

multLTEcancelLeft : (n1, n2, m : Nat) -> (notZero : NotZero m) -> (ltePrf : m * n1 `LTE` m * n2) -> n1 `LTE` n2
multLTEcancelLeft n1 n2 m notZero ltePrf =
  multLTEcancelRight _ _ _ notZero $
    replace {p = (n1 * m `LTE`)} (timesCommutes m n2) $
    replace {p = (`LTE` m * n2)} (timesCommutes m n1) ltePrf

-- Safe subtraction

minus : (n, m : Nat) -> {auto 0 prf : m `LTE` n} -> Nat
minus {prf = LTEZ} n Z = n
minus {prf = LTES prevPrf} (S n) (S m) = minus n m

minusSelf : (n : Nat) -> n `minus` n = 0
minusSelf Z = Refl
minusSelf (S n) = minusSelf n

minusCoself : (n, m : Nat) -> {auto 0 ltePrf : m `LTE` n} -> (prf : n `minus` m = 0) -> n = m
minusCoself {ltePrf = LTEZ} n Z prf = prf
minusCoself {ltePrf = LTES prevPrf} (S n) (S m) prf = cong S $ minusCoself n m prf

minusSLeftCommutes : (n, m : Nat) -> (prf : m `LTE` n) -> S n `minus` m = S (n `minus` m)
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

minusSS : (n, m : Nat) -> {auto 0 prf : m `LTE` n} -> minus (S n) (S m) = minus n m
minusSS {prf = LTEZ} n Z = Refl
minusSS {prf = LTES prevPrf} (S n) (S m) = Refl

minusPreservesLTE : (l, r, n : Nat) -> {auto 0 minusLTEprf : n `LTE` l} -> (ltePrf : l `LTE` r) -> (l `minus` n) `LTE` r
minusPreservesLTE {minusLTEprf = LTEZ} _ _ Z ltePrf = ltePrf
minusPreservesLTE {minusLTEprf = LTES prevPrf} (S l) r (S n) ltePrf =
  let LTES prevLTEprf = lteWeakenS ltePrf
  in minusPreservesLTE l r n prevLTEprf

proofIrrelevanceForMinus : {m : _} -> (prf1, prf2 : m `LTE` n) -> minus {prf = prf1} n m = minus {prf = prf2} n m
proofIrrelevanceForMinus {m = Z} LTEZ LTEZ = Refl
proofIrrelevanceForMinus {m = S m} (LTES prevPrf1) (LTES prevPrf2) = proofIrrelevanceForMinus prevPrf1 prevPrf2

minusReflLeft : {n1, n2, m : Nat} -> (0 prf : n1 = n2) -> (0 prf_n1 : m `LTE` n1) -> (0 prf_n2 : m `LTE` n2) -> n1 `minus` m = n2 `minus` m
minusReflLeft Refl LTEZ LTEZ = Refl
minusReflLeft Refl (LTES prev1) (LTES prev2) = minusReflLeft Refl prev1 prev2

plusMinusCancelsRight : (n, m : Nat) -> {auto 0 prf : m `LTE` n + m} -> n + m `minus` m = n
plusMinusCancelsRight {prf = LTEZ} n Z = sym $ plusRightZero n
plusMinusCancelsRight {prf} n (S m) =
  rewrite minusReflLeft (plusRightS n m) prf (LTES $ summandLTEsum n m)
  in plusMinusCancelsRight {prf = summandLTEsum n m} n m

plusMinusCancelsLeft : (n, m : Nat) -> {auto 0 prf : n `LTE` n + m} -> n + m `minus` n = m
plusMinusCancelsLeft n m with (plusCommutes n m) | (n + m)
  _ | Refl | _ = plusMinusCancelsRight m n

minusPlusCancelsLeft : (n, m : Nat) -> {auto 0 prf : m `LTE` n} -> m + (n `minus` m) = n
minusPlusCancelsLeft {prf = LTEZ} n Z = Refl
minusPlusCancelsLeft {prf = LTES prevPrf} (S n) (S m) = cong S $ minusPlusCancelsLeft n m

minusPlusCancelsRight : (n, m : Nat) -> {auto 0 prf : m `LTE` n} -> (n `minus` m) + m = n
minusPlusCancelsRight n m = plusCommutes (n `minus` m) m `trans` minusPlusCancelsLeft n m

minusPlusTossS : (n, m, k : Nat) -> {auto 0 prf1 : k `LTE` n + S m} -> {auto 0 prf2 : k `LTE` S n + m} -> minus (n + S m) k = minus (S n + m) k
minusPlusTossS {prf1} {prf2} n m k = minusReflLeft (plusRightS n m) prf1 prf2

plusMinusAssoc : (n, m, k : Nat) -> {auto prf1 : k `LTE` n + m} -> {auto prf2 : k `LTE` m} -> (n + m) `minus` k = n + (m `minus` k)
plusMinusAssoc {prf1 = LTEZ} {prf2 = LTEZ} n m Z = Refl
plusMinusAssoc {prf1 = LTES prevPrf1} {prf2 = LTES prevPrf2} Z (S m) (S k) = proofIrrelevanceForMinus prevPrf1 prevPrf2
plusMinusAssoc {prf1 = LTES prevPrf1} {prf2 = LTES prevPrf2} (S n) (S m) (S k) =
  let l_lte_nr = lteWeaken n prevPrf2
      l_lte_S_nr = lteWeakenS l_lte_nr
  in Calc $
  |~ ((n + S m) `minus` k)
  ~~ ((S n + m) `minus` k)   ...( minusPlusTossS n m k )
  ~~ (S ((n + m) `minus` k)) ...( minusS (n + m) k l_lte_nr l_lte_S_nr )
  ~~ (S (n + (m `minus` k))) ...( cong S $ plusMinusAssoc n m k )

timesMinusDistrRight : (n1, n2, m : Nat) -> {auto ltePrf1 : n2 * m `LTE` n1 * m} -> {auto ltePrf2 : n2 `LTE` n1} -> n1 * m `minus` n2 * m = (n1 `minus` n2) * m
timesMinusDistrRight {ltePrf1} {ltePrf2} n1 n2 m =
  let
    step1   : (((n1 `minus` n2) + n2) * m = (n1 `minus` n2) * m + n2 * m)            = timesDistrRight (n1 `minus` n2) n2 m
    step2   : (((n1 `minus` n2) + n2) * m = n1 * m)                                  = cong (* m) $ minusPlusCancelsRight n1 n2
    step3   : (n1 * m = (n1 `minus` n2) * m + n2 * m)                                = sym step2 `trans` step1
    ltePrf3 : (n2 * m `LTE` (n1 `minus` n2) * m + n2 * m)                            = summandLTEsum ((n1 `minus` n2) * m) (n2 * m)
    step4   : ((n1 `minus` n2) * m + n2 * m `minus` n2 * m = (n1 `minus` n2) * m)    = plusMinusCancelsRight ((n1 `minus` n2) * m) (n2 * m)
    step5   : (n1 * m `minus` n2 * m = (n1 `minus` n2) * m + n2 * m `minus` n2 * m)  = minusReflLeft step3 ltePrf1 ltePrf3
    step6   : (n1 * m `minus` n2 * m = (n1 `minus` n2) * m)                          = step5 `trans` step4
  in step6

-- Division

data Div : (n, d, q, r : Nat) -> Type where
  MkDiv : (eqPrf : q * d + r = n) -> (lessPrf : r `LT` d) -> Div n d q r

data LTChecked : Nat -> Nat -> Type where
  MkLTChecked : (ltPrf : x `LT` y) -> LTChecked x y

zeroIsAccessible : Accessible LTChecked Z
zeroIsAccessible = Access f
  where
    f : (y : Nat) -> LTChecked y Z -> Accessible LTChecked y
    f _ (MkLTChecked LTEZ) impossible
    f _ (MkLTChecked (LTES _)) impossible

WellFounded Nat LTChecked where
  wellFounded Z = zeroIsAccessible
  wellFounded (S x) = Access f
    where
      f : (y : Nat) -> LTChecked y (S x) -> Accessible LTChecked y
      f Z _ = zeroIsAccessible
      f (S y) (MkLTChecked (LTES prevPrf)) =
        Access $ \y', (MkLTChecked prf) =>
                 let Access rec = wellFounded {rel = LTChecked} x
                 in rec y' $ MkLTChecked $ lteTrans _ _ _ prf prevPrf

minusIsLTE : (n, m : Nat) -> {auto prf : m `LTE` n} -> (n `minus` m) `LTE` n
minusIsLTE {prf = LTEZ} n Z = lteRefl n
minusIsLTE {prf = LTES prevPrf} (S n) (S m) = lteWeakenS $ minusIsLTE n m

minusNonZeroIsLT : (n, m : Nat) -> {auto prf : m `LTE` n} -> (notZero : NotZero m) -> (n `minus` m) `LT` n
minusNonZeroIsLT n Z notZero = absurd $ notZero Refl
minusNonZeroIsLT {prf = LTES prevPrf} (S r) (S m) notZero = LTES $ minusIsLTE r m

{-
divide : (n, d : Nat) -> {auto notZero : NotZero d} -> (q ** r ** Div n d q r)
divide {notZero} n d = wfInd {P = \n' => (q ** r ** Div n' d q r)} st n
  where
    st : (x : Nat) -> ((y : Nat) -> LTChecked y x -> (q ** r ** Div y d q r)) -> (q ** r ** Div x d q r)
    st x next with (x `lt` d)
      | Yes lessPrf = (0 ** x ** MkDiv Refl lessPrf)
      | No contra = let LTES dnPrf = invertLte _ _ contra
                        (q ** r ** MkDiv eqPrf lessPrf) = next (x `minus` d) (MkLTChecked $ minusNonZeroIsLT x d notZero)
                    in (S q ** r ** MkDiv (stepEqPrf q r dnPrf eqPrf) lessPrf)
      where
        stepEqPrf : (q, r : Nat) -> (dnPrf : LTE d x) -> (eqPrf : q * d + r = minus x d) -> (S q) * d + r = x
        stepEqPrf q r dnPrf eqPrf = rewrite sym $ leftPart in
                                    rewrite sym $ minusPlusCancels x d dnPrf in
                                    plusRightPreservesEq _ _ d eqPrf
          where
            leftPart : (q * d + r) + d = (S q) * d + r
            leftPart =
              ((q * d + r) + d) ={ plusAssocSym (q * d) r d }=
              (q * d + (r + d)) ={ cong $ plusCommutes r d }=
              (q * d + (d + r)) ={ plusAssoc (q * d) d r }=
              ((q * d + d) + r) ={ cong {f = \x => x + r} $ plusCommutes (q * d) d }=
              ((d + q * d) + r) ={ Refl }=
              ((S q) * d + r) QED

lemma1 : (k, r, k', r' : Nat) -> {auto ltePrf : r `LTE` r'} -> k' + r' = k + r -> k' + (r' `minus` r) = k
lemma1 k r k' r' {ltePrf} eqPrf =
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

lemma_k_less_summands : (s, l, r : Nat) -> (eqPrf : s = l + r) -> l `LTE` s
lemma_k_less_summands s Z r prf = LTEZ
lemma_k_less_summands Z (S _) _ Refl impossible
lemma_k_less_summands (S (l + r)) (S l) r Refl = LTES $ lemma_k_less_summands (l + r) l r Refl

lemma2 : (k, r, k', r' : Nat) -> (eqPrf : k + r = k' + r') -> (ltePrf : r `LTE` r') -> k' `LTE` k
lemma2 k Z k' r' eqPrf LTEZ = lemma_k_less_summands k k' r' $ trans (plusRightZero k) eqPrf
lemma2 k (S r) k' (S r') eqPrf (LTES prevPrf) = lemma2 k r k' r' (sub eqPrf) prevPrf
  where
    sub : (eqPrf : k + S r = k' + S r') -> k + r = k' + r'
    sub prf = sInjective $ (S (k + r)) ={ sym $ plusRightS k r }=
                           (k + S r) ={ eqPrf }=
                           (k' + S r') ={ plusRightS k' r' }=
                           (S (k' + r')) QED

lemma3 : (n, m : Nat) -> (nzPrf : NotZero m) -> (ltePrf : n * m `LT` m) -> n = 0
lemma3 Z _ _ _ = Refl
lemma3 (S n) Z nzPrf ltePrf = absurd $ nzPrf Refl
lemma3 (S n) (S m) _ (LTES ltePrf) = absurd $ lteWeakenRight (n * S m) ltePrf

divEqualQBase : (n, d, q, q', r, r' : Nat) -> (rPrf : r `LTE` r') -> (div1 : Div n d q r) -> (div2 : Div n d q' r') -> q = q'
divEqualQBase n d q q' r r' rPrf (MkDiv eqPrf1 lessPrf1) (MkDiv eqPrf2 lessPrf2) =
  let
    dNonZero : (NotZero d)                                                       = ltImpliesNonZero lessPrf1
    ltePrf1  : (q' * d `LTE` (q' * d + (r' `minus` r)))                          = rewrite plusCommutes (q' * d) (r' `minus` r) in lteWeaken (r' `minus` r) $ lteRefl (q' * d)
    step1    : (q' * d + r' = q * d + r)                                         = sym $ trans eqPrf1 $ sym eqPrf2
    ltePrf2  : (q' * d `LTE` q * d)                                              = lemma2 _ _ _ _ (sym step1) rPrf
    step2    : (q' * d + (r' `minus` r) = q * d)                                 = lemma1 (q * d) r (q' * d) r' step1
    step3    : ((q' * d + (r' `minus` r)) `minus` q' * d = q * d `minus` q' * d) = minusReflLeft step2 ltePrf1 ltePrf2
    step4    : (r' `minus` r = q * d `minus` q' * d)                             = trans (sym $ plusMinusCancelsLeft (q' * d) (r' `minus` r)) step3
    ltePrf3  : (q' `LTE` q)                                                      = multLTEcancelRight _ _ _ dNonZero ltePrf2
    step5    : (r' `minus` r = (q `minus` q') * d)                               = step4 `trans` timesMinusDistrRight q q' d
    step6    : (((S r') `minus` r) `LTE` d)                                      = minusPreservesLTE (S r') d r lessPrf2
    step7    : ((r' `minus` r) `LT` d)                                           = lteCongLeft (minusSLeftCommutes _ _ rPrf) step6
    step8    : (((q `minus` q') * d) `LT` d)                                     = lteCongLeft (cong step5) step7
    step9    : ((q `minus` q') = 0)                                              = lemma3 _ _ dNonZero step8
    step10   : (q = q')                                                          = minusCoself _ _ step9
  in step10

divEqualQ : (div1 : Div n d q r) -> (div2 : Div n d q' r') -> q = q'
divEqualQ {r} {r'} div1 div2 =
  case r `lte` r' of
       Yes prf => divEqualQBase _ _ _ _ _ _ prf div1 div2
       No contra => let inv = ltWeakenLte _ _ $ invertLte _ _ contra
                    in sym $ divEqualQBase _ _ _ _ _ _ inv div2 div1

divEqualR : (div1 : Div n d q r) -> (div2 : Div n d q' r') -> r = r'
divEqualR {q} {q'} {r} {r'} div1@(MkDiv eqPrf1 lessPrf1) div2@(MkDiv eqPrf2 lessPrf2) =
  let
    step1 : (q = q')                    = divEqualQ div1 div2
    step2 : (q * d + r = q' * d + r')   = eqPrf1 `trans` sym eqPrf2
    step3 : (q' * d + r = q' * d + r')  = replace {P = \q => q * d + r = q' * d + r'} step1 step2
    step4 : (r = r')                    = plusCancelsLeft (q' * d) step3
  in step4

data Remainder : (n, d, r : Nat) -> Type where
  MkRemainder : (q : Nat) -> (prf : Div n d q r) -> Remainder n d r

decRem : (n, d, r : Nat) -> (notZero : NotZero d) -> Dec (Remainder n d r)
decRem n d r notZero =
  let (q' ** r' ** div') = divide {notZero} n d in
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
  MkOutFizz     : (n : Nat) -> (prf3 : 3 .|. n)        -> (nprf5 : Not (5 .|. n)) -> OutVerified n OutFizz
  MkOutBuzz     : (n : Nat) -> (nprf3 : Not (3 .|. n)) -> (prf5 : 5 .|. n)        -> OutVerified n OutBuzz
  MkOutFizzBuzz : (n : Nat) -> (prf3 : 3 .|. n)        -> (prf5 : 5 .|. n)        -> OutVerified n OutFizzBuzz
  MkOutNum      : (n : Nat) -> (nprf3 : Not (3 .|. n)) -> (nprf5 : Not (5 .|. n)) -> OutVerified n (OutNum n)

fizzbuzz : (n : Nat) -> (out ** OutVerified n out)
fizzbuzz n with (decRem n 3 0 sNotZero, decRem n 5 0 sNotZero)
  | (Yes div3, Yes div5) = (_ ** MkOutFizzBuzz n div3 div5)
  | (Yes div3, No ndiv5) = (_ ** MkOutFizz n div3 ndiv5)
  | (No ndiv3, Yes div5) = (_ ** MkOutBuzz n ndiv3 div5)
  | (No ndiv3, No ndiv5) = (_ ** MkOutNum n ndiv3 ndiv5)
  -}
