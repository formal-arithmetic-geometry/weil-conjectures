import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Flat.Basic

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory

/-!
# Surjectivity on first Tor after a flat intermediate base change

Source: Stacks Project, Algebra, Lemma Tag 00MM (lemma-surjective-on-tor-one,
lines 23846--23880) (blueprint: lem-weil-pbc-tor-one-surjective-flat-middle).
-/

/-- Let `R → A → B` be commutative-ring maps and `M` an `R`-module. If
`M ⊗[R] A` is flat over `A`, the natural base-change morphism from the first
Tor module over `R` with `A`, tensored with `B`, to the first Tor module over
`R` with `B` is an epimorphism.

The proof chooses a free resolution of `M`, factors its first differential at
its image, applies flat-quotient tensor injectivity and tensor right exactness,
and descends the resulting surjection through the first Tor quotient
(def-weil-pbc-tor-modules, def-weil-pbc-exact-sequence,
def-weil-pbc-flat-ring-map, lem-weil-pbc-flat-quotient-tensor-injective,
lem-weil-pbc-tensor-right-exact).
(blueprint: lem-weil-pbc-tor-one-surjective-flat-middle) -/
theorem torOne_surjective_flat_middle
    (R : Type u) (A : Type u) (B : Type u) (M : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Module R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module R M]
    [Module A (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R A))]
    [IsScalarTower R A (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R A))]
    (hflat : Module.Flat A (A ⊗[R] M)) :
    ∃ φ :
        ModuleCat.of R
            ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
              (ModuleCat.of R A)) ⊗[A] B) ⟶
        ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R B),
      Epi φ := by
  sorry

end CategoryTheory
