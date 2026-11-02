/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.AffineSpace

public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude

import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceAmbientAdjunction
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionAbelianDirectImageVanishing
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.LowerShriek.Formalism.Compactification
import WeilConjectures.AlgebraicGeometry.Finite.Etale.FiniteEtaleOpenUniformTorImage
import WeilConjectures.AlgebraicGeometry.Etale.EtalePullbackLineFlatModel
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeDirectImageConstructibility

/-!
# Exceptional interval estimate on one affine closed/smooth chart

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/sk-lem-sf-kunneth-star/
sk-rem-sf-typing.md, Rf^! row, the single affine chart sub-step; and
literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ctf-finite-geometric-restriction/sk-prop-sf-rf-shriek-preservation/
sk-prop-sf-rf-shriek-preservation.proof.md,
closed-support, affine-projection and composition paragraphs
(blueprint: lem-sf-finite-ring-affine-exceptional-window).

The two clauses concern ordinary unbounded derived categories of étale module sheaves.
The ring need not be a field or regular, and the coefficient zero ring is included.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The ordinary exceptional right adjoint on one affine chart carries constructible
cohomology and Tor intervals `[a,b]` to `[a-2r,b+2e+1]`.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/sk-lem-sf-kunneth-star/
sk-rem-sf-typing.md, Rf^! row, the single affine chart sub-step; and the closed-support,
affine-projection and composition paragraphs of
literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ctf-finite-geometric-restriction/sk-prop-sf-rf-shriek-preservation/
sk-prop-sf-rf-shriek-preservation.proof.md
(blueprint: lem-sf-finite-ring-affine-exceptional-window).

Proof:
1. Put `P = A^r_V` and let `j` be the open complement of the image of `i`.
   Every field extension has `dim V_L ≤ e`, by invariance of dimension under field
   extension. The Noetherian polynomial dimension formula gives `dim P_L ≤ r+e`,
   and open monotonicity gives the same bound for the complement. The relative torsion
   direct-image dimension bound therefore gives `cd(j) ≤ 2(r+e)`. The uniform open
   direct-image theorem gives vanishing for all coefficient module sheaves above this
   bound, and Tor amplitude `[a,b+2(r+e)]` for bounded constructible inputs of Tor
   amplitude `[a,b]`. Finite-type direct-image constructibility gives constructible
   higher images of every constructible sheaf, including sheaves without finite Tor
   amplitude. Thus both clauses of the open-complement condition hold.
2. The closed-support amplitude lemma gives constructible cohomology in
   `[a,b+2(r+e)+1]`. For Tor amplitude use the support triangle
   `i_* Ri^! K → K → Rj_* j^* K → (i_* Ri^! K)[1]` and the preceding open Tor bound.
   Exact closed pushforward and its restriction recover the same Tor interval for
   `Ri^! K`. The closed ambient adjoint agreement identifies this functor with the
   ordinary compact-support right adjoint of `i`.
3. The ordinary affine-space adjunction identifies the right adjoint of the projection
   with `pi^*(-)(r)[2r]`. Exact pullback preserves constructibility, and the Tate twist
   is locally free of rank one. Cohomology therefore has interval `[a-2r,b-2r]`.
   For the Tor assertion, represent the input by flat constructible sheaves supported
   in `[a,b]`; pullback, flat rank-one tensor, and shift give the interval
   `[a-2r,b-2r]` as well. The compact-support composition comparison and uniqueness of
   composed right adjoints identify `G` with the closed right adjoint composed with
   this projection right adjoint, for every supplied compactification. Apply step 2
   to get `[a-2r,b-2r+2(r+e)+1] = [a-2r,b+2e+1]`. Empty schemes and the zero
   coefficient ring give zero objects; the same formulas apply when `r=0` or `e=0`.
-/
theorem finiteRingAffineExceptionalWindow
    (ell p : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hk : Finite k ∨ IsAlgClosed k)
    (_hne : p ≠ ell)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 1 ≤ n ∧ (ell : A) ^ n = 0)
    {U V : Scheme.{u}}
    [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [IsAffine U] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsAffine V] [IsSeparated (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    (r e : ℕ) (he : topologicalKrullDim V ≤ (e : WithBot ℕ∞))
    (i : U ⟶ AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) V)
    [IsClosedImmersion i]
    (π : AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) V ⟶ V)
    (hπ : π = (AlgebraicGeometry.AffineSpace.over (ULift.{u} (Fin r)) V).hom)
    (c : Compactification (i ≫ π))
    (G : DerivedCategoryModule A V ⥤ DerivedCategoryModule A U)
    (hG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (a b : ℤ) (hab : a ≤ b) :
    (∀ L : DerivedCategoryModule A V,
      AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A V L ∧
        DerivedCategory.homologyConcentratedIn a b L →
      AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A U (G.obj L) ∧
        DerivedCategory.homologyConcentratedIn (a - 2 * r) (b + 2 * e + 1) (G.obj L)) ∧
    (∀ K : DerivedCategoryModule A V,
      AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A V K ∧
        AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn A V a b K →
      AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A U (G.obj K) ∧
        AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn A U
          (a - 2 * r) (b + 2 * e + 1) (G.obj K)) := by
  sorry

end AlgebraicGeometry.Etale
