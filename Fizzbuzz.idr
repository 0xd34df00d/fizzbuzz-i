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

-- Inequality and sum

summandLTEsum : (n, m : Nat) -> m `LTE` n + m
summandLTEsum Z m = lteRefl m
summandLTEsum (S n) m = lteWeakenS $ summandLTEsum n m

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

plusMinusCancels : (n, m : Nat) -> minus { prf = summandLTEsum _ _ } (n + m) m = n
plusMinusCancels Z m = minusSelf m
plusMinusCancels (S n) m = rewrite minusSLeftCommutes (n + m) m (summandLTEsum n m) in
                           rewrite plusMinusCancels n m in Refl

minusPlusCancels : (n, m : Nat) -> (prf : m `LTE` n) -> (n `minus` m) + m = n
minusPlusCancels n Z LTEZ = sym $ plusRightZero _
minusPlusCancels (S n) (S m) (LTES prevPrf) = rewrite plusRightS (n `minus` m) m in
                                              rewrite minusPlusCancels n m prevPrf in
                                              Refl

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

data Remainder : (n, d, r : Nat) -> Type where
  MkRemainder : (q : Nat) -> (prf : Div n d q r) -> Remainder n d r

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
