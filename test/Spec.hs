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

prop_prop2dnf_is_dnf :: Prop -> Bool
prop_prop2dnf_is_dnf f = is_dnf (prop2dnf f)

is_dnf :: Prop -> Bool
is_dnf (Var _) = True
is_dnf (Neg (Var _)) = True
is_dnf (f1 `Disj` f2) = is_dnf f1 && is_dnf f2
is_dnf (f1 `Conj` f2) = is_dnf' f1 && is_dnf' f2
is_dnf _ = False

is_dnf' (Var _) = True
is_dnf' (Neg (Var _)) = True
is_dnf' (f1 `Conj` f2) = is_dnf' f1 && is_dnf' f2
is_dnf' _ = False

prop_prop2cnf_is_cnf :: Prop -> Bool
prop_prop2cnf_is_cnf f = is_cnf (prop2cnf f)

is_cnf :: Prop -> Bool
is_cnf f = is_dnf (swapnnfOps f)

prop_prop2nnf_idemp :: Prop -> Bool
prop_prop2nnf_idemp f = (prop2nnf f) == prop2nnf (prop2nnf f)

prop_prop2dnf_idemp :: Prop -> Bool
prop_prop2dnf_idemp f = (prop2dnf f) == prop2dnf (prop2dnf f)

prop_prop2cnf_idemp :: Prop -> Bool
prop_prop2cnf_idemp f = (prop2cnf f) == prop2cnf (prop2cnf f)

main :: IO ()
main = do
    quickCheck prop_prop2nnf_is_nnf
    quickCheck prop_prop2dnf_is_dnf
    quickCheck prop_prop2cnf_is_cnf
    quickCheck prop_prop2nnf_idemp
    quickCheck prop_prop2dnf_idemp
    quickCheck prop_prop2cnf_idemp
