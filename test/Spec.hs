import Prop
import Test.QuickCheck

prop_prop2nnf_is_nnf :: Prop -> Bool
prop_prop2nnf_is_nnf f = is_nnf (prop2nnf f)

is_nnf :: Prop -> Bool
is_nnf T = True
is_nnf F = True
is_nnf (Var _) = True
is_nnf (Neg T) = True
is_nnf (Neg F) = True
is_nnf (Neg (Var _)) = True
is_nnf (f1 `Conj` f2) = is_nnf f1 && is_nnf f2
is_nnf (f1 `Disj` f2) = is_nnf f1 && is_nnf f2
is_nnf _ = False

main :: IO ()
main = do
    quickCheck prop_prop2nnf_is_nnf
