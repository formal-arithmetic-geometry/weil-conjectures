module

public import Sheaf.CategoryTheory.DgHomogeneousBasis
public import Mathlib.Data.Countable.Defs
import Sheaf.Paper.DerivedTotalResolutionQuasiIso
import Mathlib.Data.Set.Countable

/-!
# Countable semi-free resolutions of right DG modules

Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, proof (2) to (1),
and Tags 09KN and 09KP (blueprint: lem-sfb-dg-countable-semi-free-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- A DG module with countable cohomology over a countable DG algebra has a countable
semi-free resolution. The zero coordinates at heights at least `height j` say that the
differential of the generator `j` is a finite sum of strictly lower generators.
The coefficients have degree `degree j + 1 - degree k` by their coordinate types.
Consequently the spans of heights at most `r` are exhaustive DG submodules. Deleting
higher coordinates gives graded right-linear retractions, and each successive layer
is a direct sum of shifts of `A`: modulo lower heights its generator differential is
zero and Leibniz gives the differential on its coefficients.
Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, proof (2) to (1),
Tags 09KN, lemma-good-quotient, and 09KP, lemma-resolve
(blueprint: lem-sfb-dg-countable-semi-free-resolution).

Proof:
1. Use lem-sfb-dg-countable-submodule-representative to choose a countable DG submodule
   of `N` whose inclusion is a quasi-isomorphism.
2. Repeatedly apply lem-sfb-dg-countable-free-cover to this submodule and then the kernels.
   The covers are countable, and their augmented sequence is exact both degreewise and
   on cocycles, since each cover is surjective on cocycles.
3. Totalize the covers, putting `Q_i^b` in degree `b-i` and using differential
   `f_i + (-1)^i d`. The horizontal maps commute with the internal differential and
   compose to zero, so the mixed terms cancel. The Leibniz sign is `(-1)^(b-i)`.
   Augment by the cover map on `Q_0` and zero on the other summands.
4. Apply lem-pc-derived-total-resolution-quasi-iso to the underlying complexes over
   the integers. Its exactness hypotheses are those in step 2. Compose the resulting
   quasi-isomorphism with the submodule inclusion of step 1.
5. The two basis layers `U_i,V_i` of the covers give the total homogeneous basis.
   Assign heights `2i` and `2i+1`, respectively. The internal differential lowers the
   layer, and the horizontal differential lands in `Q_(i-1)`, of height at most `2i-1`.
   All coordinate expressions have finite support. This also gives the stated
   exhaustive graded-split DG filtration and its free shifted layers.
6. By def-sfb-countable-set and lem-trf-countable-unions the union of these countable
   basis sets is countable. Finite lists in the product of this basis set and the
   countable set of homogeneous coefficients encode every element, so the disjoint
   union of the homogeneous components of the total module is countable.
-/
theorem exists_countable_semiFree_resolution
    (A : Algebra.{u}) (N : RightModule A)
    (hA : Countable (Σ n : ℤ, A.X.X n))
    (hN : ∀ n : ℤ, Countable (((underlying A).obj N).homology n)) :
    ∃ (P : RightModule A) (q : P ⟶ N) (b : HomogeneousBasis A P)
      (height : b.Index → ℕ),
      quasiIsomorphisms A q ∧ Countable b.Index ∧
      Countable (Σ n : ℤ, ((underlying A).obj P).X n) ∧
      ∀ j k : b.Index, height j ≤ height k →
        b.coordinate (b.degree j + 1)
          ((((underlying A).obj P).d (b.degree j) (b.degree j + 1)) (b.generator j)) k = 0 := by
  sorry

end CategoryTheory.DgAlgebra
