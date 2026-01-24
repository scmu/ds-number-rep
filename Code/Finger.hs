{- Experiments relating finger trees to a binary representation
   where digits are fractions.  -}

import Prelude hiding (head, tail)
import qualified Prelude as L (head, tail, init, last)

import Data.Ratio
import Test.QuickCheck hiding (Some)

type List a = [a]
type Nat = Int

data Seq a = Nil | Unit a
           | More (Some a) (Seq (Tuple a)) (Some a)
  deriving Eq

data Some a = One a | Two a a
  deriving Eq

data Tuple a = P a a | T a a a
  deriving Eq

-- Basic queue operations

head :: Seq a -> a
head (Unit x) = x
head (More (One x) _ _) = x
head (More (Two x _) _ _) = x

cons :: a -> Seq a -> Seq a
cons x Nil = Unit x
cons x (Unit y) = More (One x) Nil (One y)
cons x (More (One y) q z) = More (Two x y) q z
cons x (More (Two y z) q w) = More (One x) (cons (P y z) q) w

snoc :: Seq a -> a -> Seq a
snoc Nil z = Unit z
snoc (Unit x) z = More (One x) Nil (One z)
snoc (More x q (One y)) z = More x q (Two y z)
snoc (More x q (Two y w)) z = More x (snoc q (P y w)) (One z)

tail :: Seq a -> Seq a
tail (Unit _) = Nil
tail (More (One _) q z) =  more0 q z
tail (More (Two _ y) q z) = More (One y) q z

more0 :: Seq (Tuple a) -> Some a -> Seq a
more0 Nil (One z) = Unit z
more0 Nil (Two y z) =  More (One y) Nil (One z)
more0 q z   = case head q of
  P x y -> More (Two x y) (tail q) z
  T x y w -> More (One x) (mapHd rm q) z
 where rm (T _ y w) = P y w

mapHd :: (a -> a) -> Seq a -> Seq a
mapHd f Nil = Nil
mapHd f (Unit x) = (Unit (f x))
mapHd f (More (One x) q y) = More (One (f x)) q y
mapHd f (More (Two x y) q z) = More (Two (f x) y) q z

--- concatentation

cat :: Seq a -> Seq a -> Seq a
cat xs ys = glue xs [] ys

glue :: Seq a -> [a] -> Seq a -> Seq a
glue Nil xs q = foldr cons q xs
glue (Unit x) xs q = cons x (foldr cons q xs)
glue r xs Nil = foldl snoc r xs
glue r xs (Unit y) = snoc (foldl snoc r xs) y
glue (More x r y) xs (More z q w) =
    More x (glue r (group (sToL y ++ xs ++ sToL z)) q) w

  --- for testing

glue' :: forall a. Show a => Seq a -> [a] -> Seq a -> [String] -- [(Seq a, [a], Seq a)]
glue' Nil xs q = [show (Nil :: Seq a, xs, q)]
glue' (Unit x) xs q = [show (Unit x, xs, q)]
glue' r xs Nil = [show (r, xs, Nil :: Seq a)]
glue' r xs (Unit y) = [show (r, xs, Unit y)]
glue' (More x r y) xs (More z q w) =
    show (More x r y, xs, More z q w) :
    glue' r (group (sToL y ++ xs ++ sToL z)) q

sToL (One x)  = [x]
sToL (Two x y) = [x,y]

group :: [a] -> [Tuple a]
group []  = []  -- impossible
group [x,y] = [P x y]
group [x,y,z,w] = [P x y, P z w]
group (x:y:z:xs) = T x y z : group xs

-- Size calculation

type Q = Ratio Int

class QCarry a where
  qcarry :: a -> Q

instance QCarry a => QCarry (Tuple a) where
  qcarry (P x y)   = (qcarry x + qcarry y) / 2
  qcarry (T x y z) = 1 % 2 + (qcarry x + qcarry y + qcarry z) / 2

instance QCarry Int where
  qcarry _ = 0

size :: QCarry a => Seq a -> Q
size Nil = 0
size (Unit x) = 1 + qcarry x
size (More x q y) = sTN x + 2 * size q + sTN y
  where sTN (One x)   = 1 + qcarry x
        sTN (Two x y) = 2 + qcarry x + qcarry y

--- test queue creation, and checking that the size calculation is correct.

mkQ l r = foldr cons Nil [l..r]

 -- mkQWith creates a queue according to a stream of instructions,
 -- where a False denotes using cons, and True denotes using snoc.
mkQWith :: List a -> List Bool
        -> Seq a
mkQWith [] _ = Nil
mkQWith xs (False:bs) = cons (L.head xs) (mkQWith (L.tail xs) bs)
mkQWith xs (True :bs) = snoc (mkQWith (L.init xs) bs) (L.last xs)

propSizeCorrect :: List Int -> InfiniteList Bool
                -> List Int -> InfiniteList Bool
                -> Bool
propSizeCorrect xs (InfiniteList bxs _) ys (InfiniteList bys _) =
       size (qxs `cat` qys) == (length xs + length ys) % 1
  where qxs = mkQWith xs bxs
        qys = mkQWith ys bys

--- Number representation

data QNat = QZero | QUnit | QMore QDig QNat QDig
data QDig = QOne [Int] | QTwo [Int]

toQ :: QNat -> Q
toQ QZero = 0
toQ QUnit = 1
toQ (QMore x q y) = digToQ x + 2 * toQ q + digToQ y
  where digToQ (QOne fs) = 1 + sum (zipWith otimes fs [1..])
        digToQ (QTwo fs) = 2 + sum (zipWith otimes fs [1..])
        f `otimes` i = f % (2^i)



--- Show Instances

instance Show a => Show (Seq a) where
  showsPrec d Nil      = ("[]" ++)
  showsPrec d (Unit x) = ('[' :) . showsPrec 0 x . (']' :)
  showsPrec d (More x q y) =
    ('⟨':) . shows x . (',':) . showsPrec 0 q . (',':) . shows y . ('⟩':)

instance Show a => Show (Tuple a) where
  showsPrec d (P x y) =
      ('(':) . showsPrec 0 x . (',':) . showsPrec 0 y . (')':)
  showsPrec d (T x y z) =
      ('(':) . showsPrec 0 x . (',':) . showsPrec 0 y .
               (',':) . showsPrec 0 z . (")⁺"++)

instance Show a => Show (Some a) where
  showsPrec d (One x) = showParen (d > 10) $
             ("𝟙 " ++) . showsPrec 11 x
  showsPrec d (Two x y) = showParen (d > 10) $
             ("𝟚 " ++) . showsPrec 11 x . (' ':) . showsPrec 11 y
