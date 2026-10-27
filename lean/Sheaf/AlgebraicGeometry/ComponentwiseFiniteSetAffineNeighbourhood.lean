module

public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.Irreducible
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import WeilConjectures.AlgebraicGeometry.IsAffineOfFiniteClosedCover
import Mathlib.RingTheory.Ideal.Operations

/-!
# Affine neighbourhoods assembled from irreducible components

Source: Stacks Project, varieties.tex, Tag 09NM,
`lemma-finite-set-codim-1-points-in-affine-per-component`.
(blueprint: lem-trf-componentwise-finite-set-affine-neighbourhood).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A finite set has a common affine neighbourhood if it has one on each reduced
irreducible component and there are finitely many components.

Source: Stacks Project, varieties.tex, Tag 09NM,
`lemma-finite-set-codim-1-points-in-affine-per-component`.
(blueprint: lem-trf-componentwise-finite-set-affine-neighbourhood).

Proof, following the six steps of the node:
1. Pass to the reduction using lem-weil-pbc-reduction-universal-homeomorphism.
   The radical ideals defining the reduced components are unchanged, by
   lem-weil-pbc-reduced-induced-closed-subscheme. An affine open of the reduction
   lifts to an affine open of X by lem-weil-pbc-thickening-affine-scheme and
   def-weil-closed-immersion. It suffices to work with X reduced.
2. Induct on the finite set of components, giving each partial union its reduced
   induced structure. The empty union is affine by lem-sc-closed-affine-union-affine;
   the single-component case is the hypothesis. Write the induction step as A union B,
   with affine opens U in A and V in B containing the respective parts of T.
3. The closed subset (U intersection B) minus V of U misses T. Use the radical
   ideal description of lem-weil-pbc-reduced-induced-closed-subscheme and
   lem-weil-pbc-prime-avoidance to choose f vanishing there and nonvanishing on
   T intersection U. If there are no such points, take f = 0. Replace U by D(f),
   using lem-weil-pbc-affine-open-section-vanishing-prime; then U intersection B
   lies in V and W = U intersection B = U intersection V is closed in U.
4. Apply the same argument in V to (V intersection A) minus U, obtaining a
   principal affine open V_h containing T intersection B and with V_h intersection A
   contained in U. Thus V_h intersection A = W intersection D(h). This is the
   symmetric shrinking; the printed formula for the discarded subset in 09NM is a typo.
5. Write U = Spec R and W = Spec (R/I), by def-weil-closed-immersion.
   The reduced structures on W agree by uniqueness in
   lem-weil-pbc-reduced-induced-closed-subscheme: realize U and V as restrictions
   of ambient opens and W as a closed subset of their intersection.
   Apply lem-trf-quotient-lift-finite-prime-avoidance to lift h on W to g in R
   avoiding the primes of (T intersection U) minus W. On T intersection W,
   nonvanishing follows from h. Hence U_g contains T intersection A and
   U_g intersection B = V_h intersection A, by
   lem-weil-pbc-affine-open-section-vanishing-prime.
6. The complement of O = U_g union V_h is the union of the closed subsets
   A minus U_g and B minus V_h, so O is open in A union B. Its restrictions
   to A and B are the affine closed subschemes U_g and V_h; uniqueness of
   reduced induced structures identifies these restrictions. Apply
   lem-sc-closed-affine-union-affine. This completes the induction, and step 1
   lifts its result from the reduction to X. Empty X and empty T are allowed. -/
theorem exists_isAffineOpen_of_componentwise_finite_set
    (X : Scheme.{u}) (hcomponents : (irreducibleComponents X).Finite)
    (T : Set X) (hT : T.Finite)
    (hlocal : ∀ C : TopologicalSpace.Closeds X,
      (C : Set X) ∈ irreducibleComponents X →
        ∃ U : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Opens,
          IsAffineOpen U ∧
            (Scheme.IdealSheafData.vanishingIdeal C).subschemeι ⁻¹' T ⊆ (U : Set _)) :
    ∃ V : X.Opens, IsAffineOpen V ∧ T ⊆ (V : Set X) := by
  sorry

end AlgebraicGeometry
