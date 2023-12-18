{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}

module Phylo(targets, joiners, duplicateAt, naiveToVec,
    naiveToVec', phylovecdomain, insertAt, naiveToTree, vecToTree,
    roundTripNaiveVec, roundTripTreeVec, roundTripVecTree, PhyloVec(..), treeToVec, vecToNaive,
    treeToNaive, treeToNaiveValid, Tree(..), (/\), findAllCherries, joinCherry,
    defaultTreeEq, NaiveVec(..), Tree'(..), treeInternalNodes, roundTripVecNaive, genTree) where



import Data.List (foldl', maximumBy, sort)

import Data.IntSet (IntSet)
import qualified Data.IntSet as S

import Data.IntMap (IntMap)
import qualified Data.IntMap as M
import Data.Set (Set)
import qualified Data.Set as Set
import Test.QuickCheck
import Debug.Trace
import Data.Ord (comparing)


duplicateAt :: Int -> [Int] -> [Int]
duplicateAt _ [] = []
duplicateAt _ [x] = [x,x]
duplicateAt n (x : xs)
  | n <= 0 = x : x : xs
  | otherwise = x : duplicateAt (n - 1) xs

insertAt :: Int -> Int -> [Int] -> [Int]
insertAt _ x [] = [x]
insertAt n x (y : ys)
  | n <= 0 = x : y : ys
  | otherwise = y : insertAt (n - 1) x ys

insertAt' :: Int -> Int -> [Int] -> [Int]
insertAt' n x ys = take n ys ++ x : drop n ys


targets' :: Int -> [Int] -> [Int]
targets' initLen v
  | initLen <= 0 = []
  | initLen == 1 = [0]
  | lastElt < initLen = lastElt : remainingTargets
  | otherwise = duplicateAt (numWaits - 1) remainingTargets
      where
        lastElt = last v
        remainingTargets = targets' (pred initLen) (init v)
        numWaits = lastElt - initLen + 1

targets :: [Int] -> [Int]
targets v = targets' (length v - 1) v

joiners' :: Int -> [Int] -> [Int]
joiners' initLen v
  | initLen <= 0 = []
  | initLen == 1 = [1]
  | lastElt < initLen = initLen : remainingJoiners
  | otherwise = insertAt numWaits initLen remainingJoiners
      where
        lastElt = last v
        remainingJoiners = joiners' (pred initLen) (init v)
        numWaits = lastElt - initLen + 1

joiners :: [Int] -> [Int]
joiners v = joiners' (length v - 1) v

data Tree a = Leaf a | Node (Tree a) (Tree a) deriving (Functor, Foldable, Traversable)

--Delete element x from the list, if it exists
delete :: Int -> [Int] -> [Int]
delete _ [] = []
delete x (y : ys)
  | x == y = ys
  | otherwise = y : delete x ys



-- This generator takes a number of leaves n, and generates a tree with n leaves
-- It does so by randomly pairing them up and then pairing up the pairs, and so on
genTree :: Int -> IntMap (Tree Int) -> Gen (Tree Int)
genTree n m
  | n <= 0 = error "genTree called with n <= 0"
  | n == 1 = return $ m M.! 0
  | otherwise = do
    i <- elements (M.keys m)
    j <- elements . delete i $ M.keys m
    let (i', j') = (min i j, max i j)
    let (i'', j'') = (m M.! i', m M.! j')
    genTree (n - 1) (M.insert i' (Node j'' i'') (M.delete j' m))

instance a ~ Int => Arbitrary (Tree a) where
  arbitrary = sized $ \n' -> let n = max n' 1 in genTree n (M.fromList $ zip [0..n-1] $ map Leaf [0..n-1])

defaultTreeEq :: Tree Int -> Tree Int -> Bool
defaultTreeEq (Leaf x) (Leaf y) = x == y
defaultTreeEq (Node l r) (Node l' r') = defaultTreeEq l l' && defaultTreeEq r r'

-- Create a generator of naive vectors of length n - 1 based on the join pairs (i', j') from genTree
-- The naive vector contains a sequence of join pairs (i,j) where i is the index of the joiner and j is the index of the target
-- The naive vector is valid if its fst elements are a permutation of [1..n-1] and for all (i,j) in the naive vector, i > j.
-- The naive vector is valid if and only if the tree it represents is valid

data Tree' a b = Leaf' b | Node' a (Tree' a b) (Tree' a b) deriving (Eq, Foldable) 

treeInternalNodes :: Tree' a b -> [a]
treeInternalNodes (Leaf' _) = []
treeInternalNodes (Node' x l r) = x : treeInternalNodes l ++ treeInternalNodes r

genTree' :: Int -> IntMap (Tree' (Int,Int) Int) -> Gen (Tree' (Int,Int) Int)
genTree' n m
  | n <= 0 = error "genTree called with n <= 0"
  | n == 1 = return $ m M.! 0
  | otherwise = do
    i <- elements (M.keys m)
    j <- elements . delete i $ M.keys m
    let (i', j') = (min i j, max i j)
    let (i'', j'') = (m M.! i', m M.! j')
    genTree' (n - 1) (M.insert i' (Node' (j',i') j'' i'') (M.delete j' m))

instance (a ~ (Int,Int), b ~ Int) => Arbitrary (Tree' a b) where
  arbitrary = sized $ \n' -> let n = max n' 1 in genTree' n (M.fromList $ zip [0..n-1] $ map Leaf' [0..n-1])

instance (Show a, Show b) => Show (Tree' a b) where
  show (Leaf' x) = "_"
  show (Node' x (Leaf' _) (Leaf' _)) = show x
  show (Node' x l r) = show x ++ "[" ++ show l ++ "|" ++ show r ++ "]"

genNaive :: Int -> IntSet -> Gen [(Int, Int)]
genNaive n s
  | n <= 0 = error "genNaive called with n <= 0"
  | n == 1 = return []
  | otherwise = do
    i <- elements (S.elems s)
    j <- elements . S.elems $ S.delete i s
    let (i', j') = (min i j, max i j)
    xs <- genNaive (n - 1) (S.delete j' s)
    return $ (j', i') : xs

newtype NaiveVec = NaiveVec {unNaive :: [(Int, Int)]} deriving (Show, Eq)

{-
instance Arbitrary NaiveVec where
  arbitrary = sized $ \n' -> let n = max n' 1 in do
    xs <- genNaive n (S.fromList [0..n-1])
    return $ NaiveVec xs

-}

instance Arbitrary NaiveVec where
  arbitrary = sized $ \n' -> let n = max n' 1 in do
    xs <- reverse . treeInternalNodes <$> genTree' n (M.fromList $ zip [0..n-1] $ map Leaf' [0..n-1])
    return $ NaiveVec xs


instance Num a => Num (Tree a) where
  (+) = undefined
  (*) = Node
  abs = fmap abs
  signum = fmap signum
  fromInteger = Leaf . fromInteger
  negate = fmap negate

intSetToSet :: IntSet -> Set Int
intSetToSet = Set.fromList . S.elems

getCladeSet' :: Tree Int -> (Set IntSet, IntSet)
getCladeSet' (Leaf x) = (Set.singleton (S.singleton x), S.singleton x)
getCladeSet' (Node l r) = (Set.insert newClade (Set.union cladesL cladesR), newClade)
  where
    (cladesL, cladeL) = getCladeSet' l
    (cladesR, cladeR) = getCladeSet' r
    newClade = S.union cladeL cladeR

getCladeSet :: Tree Int -> Set IntSet
getCladeSet = fst . getCladeSet'

instance (a ~ Int) => Eq (Tree a) where
  l == l' = getCladeSet l == getCladeSet l'




(/\) :: Tree a -> Tree a -> Tree a
(/\) = Node

instance Show a => Show (Tree a) where
  show (Leaf x) = show x
  show (Node l r) = "(" ++ show l ++ " , " ++ show r ++ ")"


findAllCherries :: Tree Int -> [(Int, Int)]
findAllCherries (Leaf _) = []
findAllCherries (Node (Leaf l) (Leaf r)) = [(l,r)]
findAllCherries (Node l r) = findAllCherries l ++ findAllCherries r

joinCherry :: (Int,Int) -> Tree Int -> Tree Int
joinCherry _ (Leaf x) = Leaf x
joinCherry (j,t) tr@(Node (Leaf l) (Leaf r))
  | max l r == max j t && min l r == min j t = Leaf (min l r)
  | otherwise = tr
joinCherry (j,t) (Node l r) = Node (joinCherry (j,t) l) (joinCherry (j,t) r)

safeMaximumBy :: (a -> a -> Ordering) -> [a] -> Maybe a
safeMaximumBy _ [] = Nothing
safeMaximumBy f xs = Just $ maximumBy f xs

getMaxCherry :: Tree Int -> Maybe (Int, Int)
getMaxCherry = safeMaximumBy (comparing $ uncurry max) . findAllCherries

unfoldCherries :: Tree Int -> [(Int, Int)]
unfoldCherries tr = case getMaxCherry tr of
  Nothing -> []
  Just (j, t) -> (max j t, min j t) : unfoldCherries (joinCherry (j,t) tr)

treeToNaive :: Tree Int -> [(Int, Int)]
treeToNaive = unfoldCherries

{-
-- Check whether the parent of a leaf labelled n's other child is a leaf labelled m, if so return a pair of the pair (n,m) and the tree with 
-- the parent node replaced by a leaf labelled by the minimum of n and m.
-- If not, return Nothing
makeCherry :: Int -> Tree Int -> Maybe ((Int, Int), Tree Int)
makeCherry _ (Leaf _) = Nothing
makeCherry n (Node (Leaf l) (Leaf r))
  | max l r == n = Just ((n, min l r), Leaf (min l r))
  | otherwise = Nothing
makeCherry n (Node l r) = case makeCherry n l of
  Just ((_, m), l') -> Just ((n, m), Node l' r)
  Nothing -> case makeCherry n r of
    Just ((_, m), r') -> Just ((n, m), Node l r')
    Nothing -> Nothing

data CherryResult = CherryResult IntSet (Int, Int) (Tree Int) | Done | Err deriving (Show)

-- Given a maximum leaf label and an IntSet of labels already seen, return the next successful call to makeCherry or Nothing if there are no more
-- successful calls
getNextCherry :: Int -> IntSet -> Tree Int -> CherryResult
getNextCherry (-1) _ _ = Err
getNextCherry _ _ (Leaf 0) = Done
getNextCherry _ _ (Leaf _) = Err
getNextCherry n seen t
  | S.member n seen = getNextCherry (n - 1) seen t
  | otherwise = case makeCherry n t of
    Just ((_, m), t') -> CherryResult (S.insert (max n m) seen) (n, m) t'
    Nothing -> getNextCherry (n - 1) seen t

-- Given a maximum leaf label, a seen labels set, and a tree, return a list of all successful calls to makeCherry
getAllCherries :: Int -> IntSet -> Tree Int -> [(Int, Int)]
getAllCherries n seen t = case getNextCherry n seen t of
  Done -> []
  Err -> error "Missing leaf in tree"
  CherryResult seen' nextCherry t' -> nextCherry : getAllCherries (n - 1) seen' t'

-- Given a tree, return it's list of cherries, this is it's naive vector form.
treeToNaive :: Tree Int -> [(Int, Int)]
treeToNaive t = getAllCherries (maxLeaf t) S.empty t
  where
    maxLeaf (Leaf x) = x
    maxLeaf (Node l r) = max (maxLeaf l) (maxLeaf r)
-}

naiveToTree' :: [(Int,Int)] -> IntMap (Tree Int) -> Tree Int
naiveToTree' [] m = m M.! 0
naiveToTree' ((j,t):xs) m = naiveToTree' xs (M.insert (min j t) (Node (m M.! j) (m M.! t)) m)

naiveToTree :: [(Int,Int)] -> Tree Int
naiveToTree xs = naiveToTree' xs (M.fromList $ zip [0..len] $ map Leaf [0..len])
  where
    len = length xs

naiveTreeRoundtrip :: Tree Int -> Property
naiveTreeRoundtrip t = withMaxSuccess 10000 (naiveToTree (treeToNaive t) == t)

-- Note: fst . split x returns the subset of elements < x
numberSmallerThan :: Int -> IntSet -> Int
numberSmallerThan x = S.size . fst . S.split x

naiveToVecLoop :: (IntSet, IntSet, IntMap Int) -> (Int, Int) -> (IntSet, IntSet, IntMap Int)
naiveToVecLoop (seenJoiners, seenTargets, v) (j, t) = (S.insert j seenJoiners, updateSeenTargets seenTargets, M.insert j val v)
  where
    waits = numberSmallerThan j seenJoiners

    tUnseen = S.notMember t seenTargets

    val | tUnseen || waits == 0 = t
        | otherwise             = waits + j - 1

    updateSeenTargets | tUnseen   = S.insert t
                      | otherwise = id

naiveToVecLoopAlt :: IntMap Int -> (Int, Int) -> IntMap Int
naiveToVecLoopAlt v (j, t) = M.insert j val v
  where
    waits = numberSmallerThan j (M.keysSet v)

    val | waits == 0 = t
        | otherwise  = waits + j - 1

naiveToVecAlt' :: [(Int, Int)] -> IntMap Int
naiveToVecAlt' = foldl' naiveToVecLoopAlt M.empty

naiveToVecAlt :: [(Int, Int)] -> [Int]
naiveToVecAlt = (0:) . M.elems . naiveToVecAlt'

naiveToVec' :: [(Int, Int)] -> IntMap Int
naiveToVec' = thrd . foldl' naiveToVecLoop (S.empty, S.empty, M.empty)
  where
    thrd (_, _, x) = x

naiveToVec :: [(Int, Int)] -> [Int]
naiveToVec = (0:) . M.elems . naiveToVec'

vecToNaive :: [Int] -> [(Int,Int)]
vecToNaive v = zip (joiners v) (targets v)

-- A generator for vectors of length n such that at index i, the element is in the range [0..2(i-1)]
phyloVecGen :: Int -> Gen [Int]
phyloVecGen n = sequence $ return 0 : [choose (0, 2 * (i - 1)) | i <- [1..n - 1]]

newtype PhyloVec = PhyloVec {unPhylo :: [Int]} deriving (Show, Eq)

instance Arbitrary PhyloVec where
  arbitrary = sized $ \n -> do
    xs <- phyloVecGen (max n 1)
    return $ PhyloVec xs

treeToVec :: Tree Int -> PhyloVec
treeToVec = PhyloVec . naiveToVec . treeToNaive

vecToTree :: PhyloVec -> Tree Int
vecToTree = naiveToTree . vecToNaive . unPhylo

naiveValid :: [(Int, Int)] -> Bool
naiveValid naiv = all (uncurry (>)) naiv && sort (map fst naiv) == [1..length naiv]

-- Check that the naive vector form of a tree is valid
treeToNaiveValid :: Tree Int -> Bool
treeToNaiveValid = naiveValid . treeToNaive

roundTripNaiveVec :: PhyloVec -> Bool
roundTripNaiveVec (PhyloVec v) = naiveToVec (vecToNaive v) == v

roundTripVecNaive :: NaiveVec -> Bool
roundTripVecNaive (NaiveVec v) = vecToNaive (naiveToVec v) == v

roundTripTreeVec :: Tree Int -> Bool
roundTripTreeVec t = vecToTree (treeToVec t) == t

roundTripVecTree :: PhyloVec -> Bool
roundTripVecTree v = treeToVec (vecToTree v) == v

phylovecdomain :: Int -> [[Int]]
phylovecdomain n = sequence $ [0] : [ [0..2*(i-1)] | i <- [1..n-1] ]



{-

def phylovecdomain(n) :
    ls = [list(range(2*(i-1) + 1)) for i in list(range(1, n))]
    return sequence([[0]] + ls)



#result = [[0,0,x,y,z,w,u,v] for x in range(3) for y in range(5) for z in range(7) for w in range(9) for u in range(11) for v in range(13)  ]
for n in range(2, 15):
    print(n)
    domain = phylovecdomain(n)

    dblfact = reduce(int.__mul__, range(2*(n) - 3, 0, -2))
    print("factcheck:" + str(len(domain) == dblfact))
    bool = True
    for ls in domain:
        bool = bool and looprev(ls)
        # if looprev(ls) == False:
        #     tmp = ls
        #     print(str(ls) + ", " + str(list(zip(joiners(tmp),targets(tmp)))) + ", " + str(naivetovec(list(zip(joiners(tmp),targets(tmp))))))
    print("Did it work: " + str(bool))

-}


{-
def loop(nai):
    tmp = naivetovec(nai)
    return list(zip(joiners(tmp),targets(tmp))) == nai

-}

{-
def naivetovec(vnaiv): 
    seenJoiners = []
    seenTargets = []
    v = [0]*(len(vnaiv) + 1)
    for j,t in vnaiv:
        if t in seenTargets:
            waits = len(list(filter(lambda x: x < j, seenJoiners)))
            if waits == 0:
                v[j] = t
            else:
                v[j] = waits + j - 1
                #print(j)
        else:
            v[j] = t
            seenTargets += [t]
          #  print(str(v))
        seenJoiners += [j]
    return v

-}


-- def joiners(v):
--    i = len(v) - 1 
--    if len(v) == 2:
--        return [1]
--    if v[i] < i:
 --       return [i] + joiners(v[:-1])
--    else:
 --       waits = v[i] - i + 1
 --       temp = joiners(v[:-1])
 --       return (temp[0 : waits] + [i] + temp[waits:])


{- 
Convert this phython pseudocode to haskell
def targets(v):
    i = len(v) - 1
    if len(v) == 2:
        return [0]
    if v[i] < i:
        ret = [v[i]] + targets(v[:-1])
        return ret
    else:
        waits = v[i] - i + 1 
        temp = targets(v[:-1])
        target = temp[waits-1]
        return (temp[0:waits-1] + [target] + temp[waits-1:])
-}