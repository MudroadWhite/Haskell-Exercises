-- {-# LANGUAGE NoImplicitPrelude #-}

module Main ( main ) where

-- import Test.Hspec

import Data.Foldable (sequenceA_, traverse_)
import Data.Functor.Const (Const (Const, getConst))
import Data.Monoid.Endo (Endo (Endo, appEndo))
import Data.Tree (Tree)
import Test.QuickCheck (Arbitrary (arbitrary), oneof)

-- import Lib

{- Functor Exercise -}

-- 1. Implement Functor instances for Either e and ((->) e).

data Ei a b = L a | R b -- self defined Either

instance (Show a, Show b) => Show (Ei a b) where
  show (L a) = "L " ++ show a
  show (R b) = "R " ++ show b

instance Functor (Ei e) where
  fmap _ (L e) = L e
  fmap f (R a) = R (f a)

-- >>> fmap (+1) (L 3)
-- L 3

-- >>> fmap (show) (R 4)
-- R "4"

newtype Arrow a b = Arrow (a -> b) -- Simulation to e -> type

aapp :: Arrow a b -> a -> b
aapp (Arrow ab) = ab

instance Functor (Arrow e) where
  fmap ab (Arrow ea) = Arrow (ab . ea)

-- >>> aapp (fmap (+1) (Arrow (+1))) 1
-- 3

----------------------------------------------------------------------------------------------------

-- 2. Implement Functor instances for ((,) e) and for Pair, defined as
data Pair a = Pair a a deriving (Show)

-- Explain their similarities and differences.

data Tup a b = T a b deriving (Show) -- self defined tuple

instance Functor (Tup e) where
  fmap f (T e a) = T e (f a)

-- >>> fmap (+1) (T "1" 1)
-- T "1" 2

instance Functor Pair where
  fmap f (Pair a b) = Pair (f a) (f b)

-- >>> fmap (+1) (Pair 2 3)
-- Pair 3 4

{-
Difference: when pair works as a functor, fmap works only on the 2nd element of the pair.
For new defined pair, fmap can act on both elements.
The original pair is allowed to have different types for each element, but the
newly defined pair can only have the same type.

Similarity: Both of them are a container containing two elements.
 -}

----------------------------------------------------------------------------------------------------

-- 3. Implement a Functor instance for the type ITree, defined as
data ITree a
  = Leaf (Int -> a)
  | INode [ITree a]

instance Functor ITree where
  fmap f (Leaf g) = Leaf (f . g)
  fmap _ (INode []) = INode []
  fmap f (INode ts) = INode $ map (fmap f) ts

----------------------------------------------------------------------------------------------------

-- 4. Give an example of a type of kind * -> * which cannot
-- be made an instance of Functor (without using undefined).

{-
Maybe Set
-}

----------------------------------------------------------------------------------------------------

-- 5. Is this statement true or false?
-- The composition of two Functors is also a Functor.
-- If false, give a counterexample; if true, prove it by exhibiting some appropriate Haskell code.

newtype Compose f g a = Compose (f (g a)) deriving (Show)

{-
We examine it by examining the functor laws.
Suppose two Functors F1, F2 with their fmaps f1 and f2, where
    f1 :: (a -> b) -> F1 a -> F1 b
    f2 :: (a -> b) -> F2 a -> F2 b

So we should have the composition of type
    f2 . f1 :: (a -> b) -> F2 (F1 a) -> F2 (F1 b)

For id we have

(f2 . f1) id = f2 (f1 id) = f2 id = id

According to the text, it means that the 2nd law is also satisfied automatically :P
-}

instance (Functor f, Functor g) => Functor (Compose f g) where
  fmap f (Compose x) = Compose (fmap (fmap f) x)

-- >>> fmap (+1) (Compose (Just [1]))
-- Compose (Just [2])

----------------------------------------------------------------------------------------------------
-- 6. Although it is not possible for a Functor instance to satisfy the first Functor
-- law but not the second (excluding undefined), the reverse is possible.
-- Give an example of a (bogus) Functor instance which satisfies the second law but not the first.

fmapPair' :: (a -> b) -> Pair a -> Pair b
fmapPair' g (Pair a b) = Pair (g b) (g a)

-- >>> fmapPair' id (Pair 2 3)
-- Pair 3 2

-- >>> (fmapPair' (+1)) . (fmapPair' (+1)) $ (Pair 2 3)
-- Pair 4 5

-- >>> fmapPair' ((+1) . (+1)) (Pair 2 3)
-- Pair 5 4

----------------------------------------------------------------------------------------------------

-- 7. Which laws are violated by the evil Functor instance for list shown above:
-- both laws, or the first law alone? Give specific counterexamples.

{-
2nd law.
Left hand side: fmap (g . h)
= (g.h) x : (g.h) x : ...
Right hand side: (fmap g) . (fmap h) x = (fmap g) (h x : h x : fmap h xs)
= (g.h) x : (g.h) x : (g.h) x : (g.h) x : ...
-}

-- >>> :t flip ($)
-- flip ($) :: a -> (a -> c) -> c

-- >>> :t ($)
-- ($) :: (a -> b) -> a -> b

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

{- Applicative exercise -}

-- 1. (Tricky) One might imagine a variant of the interchange law that
-- says something about applying a pure function to an effectful argument.
-- Using the above laws, prove that
-- pure f <*> x = pure (flip ($)) <*> x <*> pure f

{-
Id:             pure id <*> v = v
Homo:           pure f <*> pure x = pure (f x)
Interchange:    u <*> pure y = pure ($ y) <*> u
Comp:           u <*> (v <*> w) = pure (.) <*> u <*> v <*> w

  (pure (flip ($)) <*> x) <*> pure f
{Interchange}
= pure ($ f) <*> (pure (flip ($)) <*> pure x)
{Comp}
= pure (.) <*> pure ($ f) <*> pure (flip ($)) <*> x
{Homo}
= pure (($ f) . (flip ($))) <*> x
= pure (flip ($) f . flip ($)) <*> x
= pure f <*> x
-}

----------------------------------------------------------------------------------------------------

-- 2. Implement an instance of Applicative for Maybe.

data M a = N | J a deriving (Show) -- self defined Maybe

instance Functor M where
  fmap _ N = N
  fmap f (J a) = J $ f a

instance Applicative M where
  pure = J
  _ <*> N = N
  N <*> (J _) = N
  (J g) <*> (J x) = J (g x)

-- >>> J (+1) <*> N
-- N

-- >>> J (+1) <*> J 3
-- J 4

----------------------------------------------------------------------------------------------------

-- 3. Determine the correct definition of pure for the ZipList
-- instance of Applicative — there is only one implementation that
-- satisfies the law relating pure and (<*>).

newtype ZipList a = ZipList {getZipList :: [a]} deriving (Show)

instance Functor ZipList where
  fmap g (ZipList xs) = ZipList $ map g xs

instance Applicative ZipList where
  --   pure :: a -> ZipList a
  pure x = ZipList [x]

  --   (<*>) :: ZipList (a -> b) -> ZipList a -> ZipList b
  (ZipList gs) <*> (ZipList xs) = ZipList (zipWith ($) gs xs)

-- >>> ZipList [(+1), (+2)] <*> ZipList [1, 2]
-- ZipList {getZipList = [2,4]}

----------------------------------------------------------------------------------------------------

-- 4. Implement a function
-- sequenceAL :: Applicative f => [f a] -> f [a]
-- There is a generalized version of this, sequenceA, which
-- works for any Traversable (see the later section on Traversable),
-- but implementing this version specialized to lists is a good exercise.

sequenceAL [] = pure []
sequenceAL (x : xs) = (:) <$> x <*> sequenceAL xs

-- >>> sequenceAL [(Just 1) , (Just 2) , (Just 3)]
-- Just [1,2,3]

----------------------------------------------------------------------------------------------------

-- 5. Implement pure and (<*>) in terms of unit and (**), and vice versa.

class Functor f => Monoidal f where
  unit :: f ()
  (**) :: f a -> f b -> f (a, b)

pure' :: (Monoidal f) => a -> f a
pure' x = x <$ unit

(<<*>>) :: (Monoidal f) => f (a -> b) -> f a -> f b
g <<*>> x = (\(f, y) -> f y) <$> (g Main.** x)

unit' :: (Applicative f) => f ()
unit' = pure ()

(****) :: (Applicative f) => f a -> f b -> f (a, b)
fa **** fb = (,) <$> fa <*> fb

----------------------------------------------------------------------------------------------------

-- 6. Are there any Applicative instances for which there are also functions
-- f () -> () and f (a,b) -> (f a, f b), satisfying some "reasonable" laws?

instance Monoidal ((->) e) where
  unit = const ()
  ea ** eb = \x -> (ea x, eb x)

toUnit :: (e -> a) -> ()
toUnit _ = ()

toPair :: (e -> (a, b)) -> (e -> a, e -> b)
toPair eab = (fst . eab, snd . eab)

-- Assuming Int -> ...

-- >>> ((+1) Main.** unit) 1
-- (2,())

-- >>> (unit Main.** (+1)) 2
-- ((),3)

{-
Interesting laws:
toPair $ const ((), ()) = unit ** unit =iso= unit
-}

----------------------------------------------------------------------------------------------------

-- 7. (Tricky) Prove that given your implementations from the first exercise,
-- the usual Applicative laws and the Monoidal laws stated above are equivalent.

-- >>> :t ((,) <$> pure ())
-- ((,) <$> pure ()) :: Applicative f => f (b -> ((), b))

-- >>> :t pure ((,) ())
-- pure ((,) ()) :: Applicative f => f (b -> ((), b))

{-

unit' :: (Applicative f) => f ()
unit' = pure ()

(****) :: (Applicative f) => f a -> f b -> f (a,b)
fa **** fb = (,) <$> fa <*> fb

IdL: unit ** v ≅ v
  unit' **** v
= pure () **** v
= pure (,) <*> pure () <*> v
= pure (\x -> (() , x)) <*> v
= pure (() ,) <*> v
{unit ** _ ≅ id, eta reduce}
≅ pure id <*> v
= v

IdR: u ** unit ≅ u
u **** unit
= u **** pure ()
= pure (,) <*> u <*> pure ()
= pure ($ ()) <*> (pure (,) <*> u)
= pure (.) <*> pure ($ ()) <*> pure (,) <*> u
= pure ((.) ($ ())) <*> pure (,) <*> u
= pure ((.) ($ ()) (,)) <*> u
= pure (\x -> (.) ($ ()) (,) x) <*> u
= pure (\x -> ($ ()) ((,) x)) <*> u
= pure (\x -> (,) x ()) <*> u
= pure (\x -> (x , ())) <*> u
= pure (, ()) <*> u
≅ pure id <*> u
= u

-}

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

{- Monad Exercises -}
-- 1. Implement a Monad instance for the list constructor, []. Follow the types!

data L a = Lnil | Lcons a (L a) deriving (Show) -- self defined list

infix 5 <:>
x <:> xs = Lcons x xs

lToList :: L a -> [a]
lToList Lnil = []
lToList (Lcons x xs) = x : lToList xs

listToL :: [a] -> L a
listToL = foldr (<:>) Lnil

-- listToL [] = Lnil
-- listToL (x : xs) = x <:> listToL xs

instance Functor L where
  fmap _ Lnil = Lnil
  fmap f (Lcons x xs) = f x <:> fmap f xs

instance Applicative L where
  pure x = x <:> Lnil
  gs <*> xs = listToL [g x | g <- lToList gs, x <- lToList xs]

instance Monad L where
  -- concatMap :: (a -> [b]) -> [a] -> [b]
  -- (>>=) :: m a -> (a -> m b) -> m b
  -- (>>=) = flip concatMap
  --   la >>= f = (listToL . concat) (map (lToList . f) (lToList la))
  la >>= f = listToL (concatMap (lToList . f) (lToList la))

----------------------------------------------------------------------------------------------------

-- 2. Implement a Monad instance for ((->) e).
-- data Arrow a b = Arrow (a -> b)

instance Applicative (Arrow e) where
  pure x = Arrow $ const x
  eab <*> ea = Arrow (\e -> aapp eab e (aapp ea e))

instance Monad (Arrow e) where
  -- (>>=) :: (e -> a) -> (a -> e -> b) -> e -> b
  -- ea :: Arrow e a
  -- aeb :: a -> (Arrow e b)
  ea >>= aeb = Arrow (\e -> aapp (aeb (aapp ea e)) e)

----------------------------------------------------------------------------------------------------

-- 3. Implement Functor and Monad instances for Free f, defined as
data Free f a
  = Var a
  | Nd (f (Free f a)) -- Node
  -- You may assume that f has a Functor instance. This is known as the free monad built from the functor f.

instance Functor f => Functor (Free f) where
  fmap g (Var a) = Var $ g a
  fmap g (Nd x) = Nd $ fmap (fmap g) x

----------------------------------------------------------------------------------------------------
-- 4. Implement (>>=) in terms of fmap (or liftM) and join.
-- join :: m (m a) -> m a
class Applicative m => Monad'' m where
  join :: m (m a) -> m a

(>>>=) :: Monad'' m => m a -> (a -> m b) -> m b
ma >>>= amb = join $ fmap amb ma

----------------------------------------------------------------------------------------------------

-- 5. Now implement join and fmap (liftM) in terms of (>>=) and return.
-- (>>=) :: m a -> (a -> m b) -> m b
-- return :: a -> m a

fmap' :: Monad m => (a -> b) -> m a -> m b
fmap' f ma = ma >>= return . f
join' :: Monad m => m (m b) -> m b
join' mma = mma >>= id

----------------------------------------------------------------------------------------------------

-- 6. Given the definition g >=> h = \x -> g x >>= h,
-- prove the equivalence of the above laws and the usual monad laws.

{-
R1: return a >>= k                  =  k a
R2: m        >>= return             =  m
R3: m        >>= (\x -> k x >>= h)  =  (m >>= k) >>= h

R4: return      >=> g       =  g
R5: g           >=> return  =  g
R6: (g >=> h)   >=> k       =  g >=> (h >=> k)

R1 = R4:
  k a
{R4}
= (return >=> k) a
= (\x -> return x >>= k) a
= return a >>= k

R2 = R5:
  m
= m >=> return
= \x -> m x >>= return
= m >>= return

R3 = R6:
  g >=> (h >=> k)
= \x -> g x >>= (\y -> h y >>= k)
{R3}
= \x -> ( (g x >>= h) >>= k)
{Take (g x >>= h) as a whole function}
= (\y -> g y >>= h) >>= k
= (g >>= h) >>= k
-}

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

{- Foldable Exercise -}

-- 1. Implement fold in terms of foldMap.
-- foldMap :: Monoid m => (a -> m) -> t a -> m

fold' :: (Monoid m, Foldable t) => t m -> m
fold' = foldMap id

-- >>> fold' $ [[3], [4, 5]]
-- [3,4,5]

----------------------------------------------------------------------------------------------------

-- 2. What would you need in order to implement foldMap in terms of fold?

{- fmap. -}
foldMap' :: (Monoid m, Foldable t, Functor t) => (a -> m) -> t a -> m
foldMap' am ta = fold' $ fmap am ta

-- >>> foldMap' id [[3], [4, 5]]
-- [3,4,5]

----------------------------------------------------------------------------------------------------

-- 3. Implement foldMap in terms of foldr.
-- foldr :: (a -> b -> b) -> b -> t a -> b

foldMap'' :: (Monoid m, Foldable t, Functor t) => (a -> m) -> t a -> m
foldMap'' f = foldr (mappend . f) mempty

-- >>> foldMap'' id [[3], [4, 5]]
-- [3,4,5]

----------------------------------------------------------------------------------------------------

-- 4. Implement foldr in terms of foldMap (hint: use the Endo monoid).

foldr'' :: (Foldable t) => (a -> m -> m) -> m -> t a -> m
foldr'' f z t = appEndo (foldMap (Endo . f) t) z

-- >>> foldr'' (+) 1 [2,3,4]
-- 10

----------------------------------------------------------------------------------------------------

-- 5. What is the type of foldMap . foldMap? Or foldMap . foldMap . foldMap, etc.? What do they do?

{-
-- >>> :t foldMap . foldMap
-- >>> :t foldMap . foldMap . foldMap
-- foldMap . foldMap :: (Monoid m, Foldable t1, Foldable t2) => (a -> m) -> t1 (t2 a) -> m
-- foldMap . foldMap . foldMap
--   :: (Monoid m, Foldable t1, Foldable t2, Foldable t3) =>
--      (a -> m) -> t1 (t2 (t3 a)) -> m

foldMap . foldMap , provided a function f, maps, for example, a [[a]] into a single a.
foldMap . foldMap . foldMap folds 3d lists into single element in similar style.
-}

----------------------------------------------------------------------------------------------------

-- 6. Implement
toList' :: Foldable f => f a -> [a]
-- in terms of either foldr or foldMap.
toList' = foldMap (: [])

-- >>> toList' $ Just 3
-- [3]

----------------------------------------------------------------------------------------------------

-- 7. Show how one could implement the generic version of foldr in terms of toList,
-- assuming we had only
foldrList :: (a -> b -> b) -> b -> [a] -> b
foldrList = foldr

foldrG :: Foldable t => (a -> b -> b) -> b -> t a -> b
foldrG abb b ta = foldrList abb b (toList' ta)

-- >>> foldrG (+) 1 [2, 3, 4]
-- 10

----------------------------------------------------------------------------------------------------

-- 8. Pick some of the following functions to implement: concat, concatMap,
-- and, or, any, all, sum, product, maximum(By), minimum(By), elem, notElem,
-- and find. Figure out how they generalize to Foldable and come up with elegant
-- implementations using fold or foldMap along with appropriate Monoid instances.

elem' :: (Eq a, Foldable t) => a -> t a -> Bool
elem' = any . (==)

notElem :: (Eq a, Foldable t) => a -> t a -> Bool
notElem a ta = not $ elem' a ta

----------------------------------------------------------------------------------------------------

-- 9. Implement traverse_ in terms of sequenceA_ and vice versa.
-- One of these will need an extra constraint. What is it?
-- sequenceA_   :: (Applicative f, Foldable t) => t (f a)       -> f ()
-- traverse_    :: (Applicative f, Foldable t) => (a -> f b)    -> t a -> f ()

sequenceA_' :: (Applicative f, Foldable t) => t (f a) -> f ()
sequenceA_' tfa = traverse_ id tfa

traverse_' :: (Applicative f, Foldable t, Functor t) => (a -> f b) -> t a -> f ()
traverse_' afb ta = sequenceA_ $ fmap afb ta

{- traverse_' needs an extra constraint that t must be a functor. -}

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

{- Traversable Exercise -}

-- 1. There are at least two natural ways to turn a tree of
-- lists into a list of trees. What are they, and why?

method1 :: Tree [a] -> [Tree a]
method1 = sequence

method2 :: Tree [a] -> [Tree a]
method2 = traverse id

----------------------------------------------------------------------------------------------------

-- 2. Give a natural way to turn a list of trees into a tree of lists.

ltTotl :: [Tree a] -> Tree [a]
ltTotl = traverse id

----------------------------------------------------------------------------------------------------

-- 3. What is the type of traverse . traverse? What does it do?

-- >>> :t traverse . traverse
-- traverse . traverse
--   :: (Applicative f, Traversable t1, Traversable t2) =>
--      (a -> f b) -> t1 (t2 a) -> f (t1 (t2 b))

-- traverse . traverse can be used for, for example, traversing a 2d list.

----------------------------------------------------------------------------------------------------

-- 4. Implement traverse in terms of sequenceA, and vice versa.

traverse' :: (Traversable t, Monad f) => (a -> f b) -> t a -> f (t b)
traverse' afb ta = sequenceA $ fmap afb ta

sequenceA' :: (Traversable t, Applicative f) => t (f a) -> f (t a)
sequenceA' = traverse id

----------------------------------------------------------------------------------------------------

-- 5.Implement fmap and foldMap using only the Traversable methods.
-- (Note that the Traversable module provides these implementations
--  as fmapDefault and foldMapDefault.)

-- traverse  :: Applicative f => (a -> f b) -> t a -> f (t b)
-- sequenceA :: Applicative f => t (f a) -> f (t a)

fmapT :: (Traversable t) => (a -> b) -> t a -> t b
fmapT f = out . traverse (Id . f)
  where
    out (Id a) = a

foldMapT :: (Traversable t, Monoid m) => (a -> m) -> t a -> m
foldMapT f = getConst . traverse (Const . f)

----------------------------------------------------------------------------------------------------

-- 6.Implement Traversable instances for [], Maybe, ((,) e), and Either e.

-- Maybe
instance Foldable M where
  foldr _ b N = b
  foldr abb b (J a) = abb a b

instance Traversable M where
  traverse _ N = pure N
  traverse afb (J a) = J <$> afb a

-- (e, )
instance Foldable (Tup e) where
  foldr abb b (T _ a) = abb a b

instance Traversable (Tup e) where
  traverse afb (T e a) = T e <$> afb a

-- Either
instance Foldable (Ei e) where
  foldr _ b (L _) = b
  foldr abb b (R a) = abb a b

instance Traversable (Ei e) where
  traverse _ (L e) = pure (L e)
  traverse afb (R a) = R <$> afb a

-- List
instance Foldable L where
  foldr _ b Lnil = b
  foldr abb b (Lcons a as) = abb a $ foldr abb b as

instance Traversable L where
  traverse _ Lnil = pure Lnil
  traverse afb (Lcons a as) = fmap Lcons (afb a) <*> traverse afb as

----------------------------------------------------------------------------------------------------

-- 7.Explain why Set is Foldable but not Traversable.

{- Foldable has no constraint, while Traversable type is required
to be a Functor. -}

----------------------------------------------------------------------------------------------------

-- 8.Show that Traversable functors compose: that is, implement an
-- instance for Traversable (Compose f g) given Traversable instances for f and g.

instance (Traversable f, Traversable g) => Foldable (Compose f g) where
  foldMap f (Compose t) = foldMap (foldMap f) t

instance (Traversable f, Traversable g) => Traversable (Compose f g) where
  traverse f (Compose t) = Compose <$> traverse (traverse f) t

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

{- Final part: implementation of several datatypes' classes-}

newtype Id a = Id a

-- We have already implemented Traversable, Foldable for Maybe and List.
-- what they need to be implemented is Semigroup and Monoid, plus Arbitary.

{- Identity -}

instance Functor Id where
  fmap f (Id a) = Id (f a)

instance Applicative Id where
  pure = Id
  (Id g) <*> (Id a) = Id (g a)

instance (Semigroup a) => Semigroup (Id a) where
  (Id a) <> (Id b) = Id (a <> b)

instance (Monoid a) => (Monoid (Id a)) where
  mempty = mempty
  mappend = (<>)

instance Monad Id where
  (Id a) >>= f = f a

instance Foldable Id where
  foldr abb b (Id a) = abb a b

instance Traversable Id where
  traverse afb (Id a) = Id <$> afb a

instance (Arbitrary a) => Arbitrary (Id a) where
  arbitrary = do Id <$> arbitrary

-- a <- arbitrary
-- return (Id a)

{- Maybe -}

instance (Semigroup a) => Semigroup (M a) where
  N <> N = N
  N <> (J b) = J b
  (J a) <> N = J a
  (J a) <> (J b) = J $ a <> b

instance Monad M where
  N >>= _ = N
  (J a) >>= f = f a

instance (Monoid a) => Monoid (M a) where
  mempty = N
  mappend = (<>)

instance (Arbitrary a) => Arbitrary (M a) where
  arbitrary = do
    a <- arbitrary
    oneof [return N, return $ J a]

{- List -}

instance (Semigroup a) => Semigroup (L a) where
  Lnil <> Lnil = Lnil
  Lnil <> x = x
  x <> Lnil = x
  x <> y = x <> y

instance (Monoid a) => (Monoid (L a)) where
  mempty = Lnil
  mappend = (<>)

-- duplicated declaration
-- instance (Arbitrary a) => Arbitrary [a] where
--   arbitrary = do
--       a1 <- arbitrary
--       a2 <- arbitrary 
--       a3 <- arbitrary
--       oneOf [return [], return [a1], return [a1, a2], return [a1, a2, a3]]

main :: IO ()
main = return ()
