{-# Language TypeOperators   #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnicodeSyntax   #-}
{-# LANGUAGE RecordWildCards #-}

{-# OPTIONS_GHC -F -pgmF ./preProcessor.sh  #-}


module HottPrimer where

----------------------------
--------  PREAMBLE  --------
----------------------------
infixr 7 :+:
type (a :+: b) = Either a b

pattern Inl a = Left  a
pattern Inr b = Right b
inl = Left
inr = Right

infixr 8 :*:
type a :*: b = (a , b)

pr1 = \(a , _) -> a
pr2 = \(_ , b) -> b

data Z

type ¬ a = a -> Z

infixr 6 ⊣⊢
data p ⊣⊢ q =
  BiImplication
  { to   :: p -> q
  , from :: q -> p
  }

----------------------------

----------------------------
--------- THEOREMS ---------
----------------------------

-- Theorem 1 (&-introduction)
theorem1 :: a -> b -> a :*: b
theorem1 a b = (a, b)

-- Theorem 2 (&-elimination)
theorem2a :: a :*: b -> a
theorem2a = pr1

theorem2b :: a :*: b -> b
theorem2b = pr2

-- Theorem 3 (∨-introduction)
theorem3a :: a -> a :+: b
theorem3a a = inl a

theorem3b :: b -> a :+: b
theorem3b b = inr b

-- Theorem 4 (∨-elimination)
theorem4 :: (a -> z) -> (b -> z) -> (a :+: b) -> z
theorem4 gl gr =
  \case
    Inl a -> gl a
    Inr b -> gr b

-- Theorem 5 (Absorption1)
theorem5 :: a ⊣⊢ a :+: (a :*: b)
theorem5 = BiImplication{..}
  where
    to = inl
    from =
      \case
        Inl a -> a
        Inr p -> pr1 p


-- Theorem 6 (Absorption2)
theorem6a :: a :*: (a :+: b) -> a
theorem6a = pr1

theorem6b :: a -> a :*: (a :+: b)
theorem6b a = (a, inl a)

-- Theorem 7 (Distributivity of ∨ over &)
theorem7 :: a :+: (b :*: c) ⊣⊢ (a :+: b) :*: (a :+: c)
theorem7 = BiImplication{..}
  where
    to =
      \case
        Inl a -> (inl a , inl a)
        Inr p -> (inr . pr1 $ p, inr . pr2 $ p)

    from =
      \case
        (Inl a , _    ) -> inl a
        (_     , Inl a) -> inl a
        (Inr b , Inr c) -> inr (b, c)

-- Theorem 8 (Distribuitivty of & over ∨)
theorem8 :: a :*: (b :+: c) ⊣⊢ (a :*: b) :+: (a :*: c)
theorem8 = BiImplication{..}
  where
    to =
      \case
        (a, Inl b) -> inl (a, b)
        (a, Inr c) -> inr (a, c)
    from =
      \case
        Inl (a, b) -> (a, inl b)
        Inr (a, c) -> (a, inr c)

-- Theorem 9 (Modus Ponens)
theorem9 :: a -> (a -> b) -> b
theorem9 = flip ($) -- cheeky

-- Theorem 10 (Transitivity of =>)
theorem10 :: (a -> b) -> (b -> c) -> (a -> c)
theorem10 = flip (.)


-- Theorem 11 (Currying)
theorem11 :: (a :*: b -> c) -> (a -> (b -> c))
theorem11 = curry

-- Theorem 12 (Uncurrying)
theorem12 :: (a -> (b -> c)) -> (a :*: b -> c)
theorem12 = uncurry

-- Theorem 13 (Swapping the order of functon arguments)
theorem13 :: (a -> (b -> c)) -> (b -> (a -> c))
theorem13 = flip

-- Theorem 14 (Application of deduction)
theorem14 :: (a -> (b -> c)) -> ((a -> b) -> (a -> c))
theorem14 g f a = g a (f a)



theorem ::  ¬ (a :+: b)  ->   ¬ a :*:  ¬ b
theorem g =
  let
    p = \a -> g . inl $ a
    q = \b -> g . inr $ b
  in
    (p, q)

