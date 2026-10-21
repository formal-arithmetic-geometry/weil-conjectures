/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.CategoryTheory.DerivedCategory.ExactFunctorCoproducts
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Proper direct image preserves coproducts of classical complexes

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, Étale statements and Transfer
(blueprint: lem-sfb-finite-proper-classical-coproducts).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Proper direct image preserves the ambient coproduct of any small family with
classical cohomology. Both cofans are ambient derived coproducts, and the comparison
is their universal map with components `Rf_*(ι_s)`. The common site/coefficient/index
universe contains the entire family; no boundedness is imposed on its members.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, Étale statements and Transfer
(blueprint: lem-sfb-finite-proper-classical-coproducts).

Proof plan:
1. Ringed-site module categories are Grothendieck and have enough injectives
   (lem-weil-pbc-ring-sheaves-grothendieck, lem-sp-grothendieck-enough-injectives).
   Properness gives qcqs. The finite-discrete coefficient comparisons identify the
   given coefficient sheaf with constant coefficients
   (lem-weil-pbc-finite-discrete-condensed-ring-constant,
   lem-weil-pbc-finite-discrete-scheme-ring-constant).
2. Ambient sums are termwise derived sums (lem-kun-grothendieck-derived-coproducts).
   Exactness of sums gives their cohomology and good-truncation compatibilities
   (lem-weil-pbc-exact-functor-complex-cohomology, def-kun-truncations).
3. Classical sheaves are the image of exact comparison inverse image, a left adjoint.
   Thus sums and good truncations retain classical cohomology
   (det-pe-classical-sheaves-modules, lem-weil-pbc-left-adjoint-preserves-colimits,
   lem-pur-exact-derived-coproducts).
4. The unbounded derived adjunction makes G = Rf_* preserve products. It is
   triangulated and preserves lower bounds, computed by bounded-below injective
   representatives (def-weil-pbc-proetale-operations,
   lem-weil-pbc-right-adjoint-preserves-limits,
   lem-pc-right-derived-functor-triangulated, lem-weil-pbc-dplus-injective-representative).
5. Finite A kills all its modules by a nonzero integer. The proper torsion bound
   gives etale cohomological dimension c = 2e; forgetting coefficients transfers this
   to A-modules. Hence etale direct image preserves arbitrary unbounded sums
   (lem-kun-proper-torsion-cd-bound, lem-sbc-higher-direct-image-forget-comparison,
   lem-weil-pbc-module-sheaves-colimits-forgetful, lem-exc-direct-image-coproducts).
6. Bounded-below comparison applied to a classical heart sheaf transports this
   upper bound to G of that sheaf in degree zero
   (sk-thm-pe-direct-image-comparison, src-right-derived-functor-plus-compatibility,
   lem-sp-derived-functor-single-identification).
7. Exact countable products and left completeness extend the heart bound to
   classical complexes: L <= b implies GL <= b+c (det-pe-products-exact,
   det-pe-left-complete-iso, lem-weil-derived-countable-products-core,
   lem-sfb-left-complete-heart-upper-bound).
8. On any common finite interval, bounded-below classical equivalence, direct-image
   comparison, and the etale sum theorem make the canonical comparison invertible
   (sk-prop-sf-comparison, det-pe-classical-derived-equivalence).
   Naturality identifies this map on every coprojection.
9. Fix m. Set U_s = truncLE m K_s. The removed upper tail maps into degrees >= m+1,
   so H^m(GU_s) -> H^m(GK_s) is invertible by the truncation long exact sequence
   (def-sbc-standard-tstructure-derived-category, lem-sf-derived-homology-long-exact).
10. Set V_s = truncGE (m-c) U_s. Its removed tail is <= m-c-1; Step 7 maps it to
    degrees <= m-1. Thus H^m(GU_s) -> H^m(GV_s) is invertible, and Step 8 applies
    to the common interval [m-c,m].
11. Steps 2-3 give the same truncation identifications and cohomology isomorphisms
    for the ambient sum and for the sums of the image maps.
12. The comparison is natural in families, as checked on each coprojection.
    Apply H^m to the two truncation squares and cancel the vertical isomorphisms.
    Step 8 makes H^m of the comparison invertible; the cohomology criterion
    (lem-weil-pbc-unbounded-derived-iso-cohomology) finishes for every m.
    For the empty family both sums are zero and additive G sends zero to zero. -/
theorem finiteCoefficientDerivedDirectImage_classical_coproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (he : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞))
    (I : Type (u + 1)) (K : I → FiniteCoefficientDerivedCategory X A)
    (hK : ∀ s : I, IsClassicalModuleComplex (K s)) :
    ∃ (c : Cofan K) (_ : IsColimit c)
      (c' : Cofan (fun s ↦ (finiteCoefficientDerivedDirectImage f A).obj (K s)))
      (hc' : IsColimit c'),
      IsIso (hc'.desc (Cofan.mk ((finiteCoefficientDerivedDirectImage f A).obj c.pt)
        (fun s ↦ (finiteCoefficientDerivedDirectImage f A).map (c.inj s)))) := by
  sorry

end AlgebraicGeometry.ProEtale
