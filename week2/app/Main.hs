module Main (main) where

-- import Lib

import Control.Monad.Trans.Class (MonadTrans (lift))

import Test.QuickCheck (Arbitrary (arbitrary), frequency, oneof)

import Control.Applicative (Alternative (empty, (<|>)), liftA2)

import Control.Comonad (Comonad(extract))

{- MonadT Exercises -}

{- 1.1. What is the kind of t in the declaration of MonadTrans?

The kind of a monad m is (* -> *). As the transformed monad is represented by (t m) a,
the kind of t is (* -> *) -> * -> *.

-}

{- 2.1. Implement join :: M (N (M (N a))) -> M (N a), given distrib :: N (M a) -> M (N a) and
    assuming M and N are instances of Monad. -}

{- NOTE:  This exercise is partially collaborated with Amirhossein -}

joinD :: (Monad m, Monad n) => m (n (m (n a))) -> m (n a)
joinD x = x >>= distrib >>= (return . join)
  where
    distrib :: n (m a) -> m (n a)
    distrib = undefined

    join :: (Monad n) => n (n a) -> n a
    join a = a >>= id

{- Implementation Exercises -}

newtype IdentityT m a = IdentityT (m a) deriving (Show)

instance MonadTrans IdentityT where
  lift = IdentityT

testIdListInt :: IdentityT [] Int
testIdListInt = IdentityT [0]

instance (Monad m) => Functor (IdentityT m) where
  fmap f (IdentityT m) = lift $ fmap f m

-- >>> fmap (+1 ) testIdListInt
-- IdentityT [1]

instance (Monad m) => Applicative (IdentityT m) where
  pure x = lift $ pure x
  (IdentityT g) <*> (IdentityT x) = lift $ g <*> x

-- >>> (IdentityT [(+1)]) <*> testIdListInt
-- IdentityT [1]

instance (Monad m, Semigroup (m a)) => Semigroup (IdentityT m a) where
  IdentityT a <> IdentityT b = lift $ a <> b

-- >>> testIdListInt <> testIdListInt
-- IdentityT [0,0]

instance (Monad m, Monoid (m a)) => Monoid (IdentityT m a) where
  mempty = lift mempty

-- mappend = (<>)

instance (Monad m) => Monad (IdentityT m) where
  return = lift . return
  (IdentityT m) >>= f = IdentityT (m >>= (unlift . f))
    where
      unlift (IdentityT x) = x

-- >>> testIdListInt >>= (\x -> IdentityT $ [x+1])
-- IdentityT [1]

instance (Monad m, Foldable m) => Foldable (IdentityT m) where
  foldr abb b (IdentityT m) = foldr abb b m

instance (Monad m, Traversable m) => Traversable (IdentityT m) where
  -- traverse afb (IdentityT a) = traverse afb a
  traverse afb (IdentityT ma) = IdentityT <$> traverse afb ma

instance (Monad m, Arbitrary (m a)) => Arbitrary (IdentityT m a) where
  arbitrary = do IdentityT <$> arbitrary

---------------------------------------------------------------------------------------------------

data MaybeT m a = JustT (m a) | NothingT deriving (Show)

instance MonadTrans MaybeT where
    lift = JustT

instance (Functor m) => Functor (MaybeT m) where
    fmap _ NothingT = NothingT
    fmap f (JustT x) = JustT $ fmap f x

instance (Applicative m) => Applicative (MaybeT m) where
    pure a = JustT (pure a)
    NothingT <*> _ = NothingT
    _ <*> NothingT = NothingT
    (JustT f) <*> (JustT x) = JustT $ f <*> x

instance (Semigroup (m a)) => Semigroup (MaybeT m a) where
    NothingT <> x = x
    x <> NothingT = x
    (JustT x) <> (JustT y) = JustT $ x <> y

instance (Monoid (m a)) => Monoid (MaybeT m a) where
    mempty = NothingT

instance (Foldable m) => Foldable (MaybeT m) where
    foldMap _ NothingT = mempty
    foldMap f (JustT x) = foldMap f x

instance (Traversable m) => Traversable (MaybeT m) where
    traverse _ NothingT = pure NothingT
    traverse afb (JustT x) = fmap JustT (traverse afb x)

instance (Arbitrary (m a)) => Arbitrary (MaybeT m a) where
  arbitrary = do
    a <- arbitrary
    oneof [return NothingT, return $ JustT a]

---------------------------------------------------------------------------------------------------

data ListT m a = ConsT (m a) (ListT m a) | NilT 
    deriving (Show)
    -- deriving (Foldable, Traversable, Show)

instance Functor m => Functor (ListT m) where
    fmap _ NilT = NilT
    fmap f (ConsT ma l) = ConsT (fmap f ma) (fmap f l)

-- >>> fmap (+1) (ConsT [1] NilT)
-- ConsT [2] NilT

instance Applicative m => Applicative (ListT m) where
    pure x = ConsT (pure x) NilT
    NilT <*> _ = NilT
    _ <*> NilT = NilT
    (ConsT mf l1) <*> (ConsT mx l2) = ConsT (mf <*> mx) (l1 <*> l2)

-- >>> (ConsT [(+1)] NilT) <*> (pure 1)
-- ConsT [2] NilT

instance Semigroup (m a) => Semigroup (ListT m a) where
    NilT <> x = x
    x <> NilT = x
    (ConsT ma l1) <> (ConsT mb l2) = ConsT (ma <> mb) (l1 <> l2)

test2 :: ListT Maybe [Int]
test2 = pure [2]

test3 :: ListT Maybe [Int]
test3 = pure [3]

-- >>> test2 <> test3
-- ConsT (Just [2,3]) NilT

concatLT :: ListT m a -> ListT m a -> ListT m a
concatLT l1 l2 = case l1 of
      NilT -> l2
      ConsT ma ml -> ConsT ma (concatLT ml l2)

-- The only instance that I need a comonad...
instance (Monad m, Comonad m) => Monad (ListT m) where
    return x = ConsT (return x) NilT
    NilT >>= _ = NilT
    (ConsT ma lm) >>= almb = extract $ do
                a <- ma
                return (concatLT (almb a) (lm >>= almb))

{-
-- >>> extract [0]
-- Could not deduce (Comonad []) arising from a use of ‘extract’
-- from the context: Num a
--   bound by the inferred type of it :: Num a => a
--   at C:\Users\hilov\Desktop\week_project\week2\app\Main.hs:160:2-12

For the implementation above, I'll assume that, for example, m is a list. then we can see that
(almb a) will wrap up the result into a list. extract should provide some functionality to extract
a single value from the list and return the correct result. In our case, since the do block 
eventually returns a single wrapped value, we should be safe to make the assertion that we can extract a 
value from the monad m.

-}

instance (Foldable m) => Foldable (ListT m) where
    foldMap _ NilT = mempty
    foldMap f (ConsT x ls) = mappend (foldMap f x) (foldMap f ls)

instance (Traversable m) => Traversable (ListT m) where
    traverse _ NilT = pure NilT
    traverse afb (ConsT ma ls) = ConsT <$> traverse afb ma <*> traverse afb ls

test0 :: ListT Maybe Int
test0 = ConsT (Just 0) NilT

test1 :: ListT Maybe Int
test1 = ConsT (Just 1) NilT

-- >>> foldMap (:[]) test0
-- [0]

-- >>> traverse (:[]) test0
-- [ConsT (Just 0) NilT]

instance Arbitrary (m a) => Arbitrary (ListT m a) where
    arbitrary = do
        elm <- arbitrary
        more <- arbitrary -- potential infinite list...
        frequency
            [ (6, return NilT),
              (1, return $ ConsT elm more)
            ]

---------------------------------------------------------------------------------------------------

{- For this version of implementation I have referenced to
https://github.com/Gabriel439/Haskell-List-Transformer-Library/blob/main/src/List/Transformer.hs 
It also works fine
-}

-- newtype ListT m a = ListT {next :: m (Step m a)}
--   deriving (Foldable, Traversable)

-- data Step m a = Cons a (ListT m a) | Nil
--   deriving (Foldable, Traversable)

-- test0 :: ListT Maybe Int
-- test0 = ListT $ Just Nil

-- test1 :: ListT Maybe Int
-- test1 = ListT $ Just $ Cons 1 test0

-- instance (Monad m, Show a, Show (ListT m a)) => Show (Step m a) where
--   show Nil = "Nil"
--   show (Cons a l) = "Cons " ++ show a ++ " " ++ show l

-- instance (Monad m, Show (m (Step m a))) => Show (ListT m a) where
--   show (ListT m) = "ListT (" ++ show m ++ ")"

-- -- >>> test0
-- -- ListT (Just Nil)

-- -- >>> test1
-- -- ListT (Just Cons 1 ListT (Just Nil))

-- instance Monad m => Functor (Step m) where
--   fmap _ Nil = Nil
--   fmap k (Cons x l) = Cons (k x) (fmap k l)

-- instance Monad m => Alternative (ListT m) where
--   empty = ListT (return Nil)
--   ListT m <|> l =
--     ListT $ do
--       s <- m
--       case s of
--         Nil -> next l
--         Cons x l' -> return (Cons x (l' <|> l))

-- instance MonadTrans ListT where
--   lift m =
--     ListT $ do
--       x <- m
--       return (Cons x (ListT (return Nil)))

-- instance Monad m => Functor (ListT m) where
--   fmap k (ListT m) =
--     ListT $ do
--       s <- m
--       return (fmap k s)

-- instance Monad m => Applicative (ListT m) where
--   pure x = ListT (return (Cons x (ListT (return Nil))))
--   ListT m <*> l =
--     ListT $ do
--       s <- m
--       case s of
--         Nil -> return Nil
--         Cons f l' -> next (fmap f l <|> (l' <*> l))

-- instance (Monad m, Semigroup a) => Semigroup (ListT m a) where
--   (<>) = liftA2 (<>)

-- instance (Monad m, Semigroup a, Monoid a) => Monoid (ListT m a) where
--   mempty = pure mempty

-- instance Monad m => Monad (ListT m) where
--   return = pure
--   ListT m >>= k =
--     ListT $ do
--       s <- m
--       case s of
--         Nil -> return Nil
--         Cons x l' -> next (k x <|> (l' >>= k))

-- instance (Monad m, Arbitrary a, Monoid a) => Arbitrary (m (Step m a)) where
--   arbitrary = do
--     a <- arbitrary
--     more <- arbitrary -- potential infinite list...
--     frequency
--       [ (10, return $ pure $ mempty)
--       , (1, return $ pure $ Cons a more)
--       ]

-- listTGen :: (Arbitrary (m (Step m a))) => Gen (ListT m a)
-- listTGen = do
--   m <- arbitrary
--   return $ ListT m

-- instance (Monad m, Arbitrary (m (Step m a))) => Arbitrary (ListT m a) where
--   arbitrary = listTGen

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

{- Plutus Exercises -}

{-

(4) explain some of the ways hashing functions enable blockchain technology

PoW relies heavily on hashing functions.
The Merkle Root of a block is based on hashing the whole block.

(5) briefly explain Bitcoin's UTXO model of transaction validation (separate from POW)

A transaction consists of two parts: input side and output side. The input side will provide the
datum, the redeemer and the validator to consume the UTXOs. Otherwise, they can only be referred
to through script addresses, which is what output side only be allowed.

Every time a node received a new transaction, it will use a validator to validate the transaction,
checking conditions such as in correct time range, legal coin holders, and so on. If the
transaction has been validated, the node will try to consume UTXOs for the transaction to be
complete.

Before a UTXO is going to be spent, a redeemer, consists of arbitrary scripts, is going to verify
it so that the UTXO can be spent. Usually, this means the holder of the UTXO has to sign up for
the spending. After the redeemer verified the UTXO, the UTXO will be sent to a transaction to be
consumed.

During the verification process, the redeemer is allowed to see all transactions' inputs and
outputs, along with the current transaction's all inputs, and all these are the context of the
redeemer.

When a UTXO is consumed, it is allowed to be associated with a datum representing arbitrary data,
providing potential useful information to be used in redeemers.

(6) what is the structure of a Block in bitcoin and how does it relate to the 'blockchain' (merkle
tree vs merkle list of merkle trees)

A block in blockchain consists of a block header, recording critical information to identify the
block's validity; and followed by a list of transaction records being the major part of the block.

Within the block header, two critical entries are "previous block hash" and "MerkleRoot". By
providing the hash to the previous block, the current block is "linked" to the previous block like
a chain, hence the name blockchain.

Merkle root for a single block is two SHA256 hash that pick up every two entries in transaction
records or one duplicated record, and get the list of hash values; by repeating this process,
there will eventually be only one hash left, and this is the merkle root, representing the
"uniqueness" of data being "organized" into a merkle tree.

(7) what problem/s are POW/POS trying to solve? discuss/compare (byzantine fault tolerance,
reaching a single consensus on a p2p network)

PoW sets up a difficult-enough goal for every node to compute on, and the first node that produces
the correct result will be decided as the producer of a new block.

Byzantine fault is a situation that fault happens and it's hard to completely get rid of the fault.
In the context of blockchain, byzantine fault means some adversarial nodes trying to modify the
record of transactions and affect the whole network.

If an adversary can produce a valid answer easily, the adversary will have the chance to modify
transactions in the history and affect the whole nodes. With PoW it will be hard for the adversary
to produce a valid answer for even a single block. Therefore, all nodes are encouraged to compute
on the newest block only.

PoS gives every node a stake value based on the coins they have, and the more a node stores coins,
the higher chance for the node to produce a new block.

Comparing to PoW, it largely reduces the amount of computation to produce a new block. However,
it is vulnerable to 51% attack.

-}

main :: IO ()
main = return ()
