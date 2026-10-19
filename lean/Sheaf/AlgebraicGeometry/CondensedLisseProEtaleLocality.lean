/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.CondensedScalarRealization
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Sheaf.CategoryTheory.DualizableJointlyConservativeLocality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Pro-etale locality and pullback of dualizable condensed complexes

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Section 3,
pullback paragraph before (3.1), Definition 3.3 and Lemma 4.5
(blueprint: lem-zl-condensed-lisse-proetale-locality).

The ordinary unbounded derived categories and their ordinary derived tensor are the
published internal-module constructions. Lisse means `Nonempty (HasRightDual K)`;
`HasRightDual` includes an exact evaluation/coevaluation pairing with both triangle identities.
No quasi-compactness or condition on irreducible components is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Register the existing Koszul braiding of the ordinary derived tensor on internal modules.
This is the generic published construction specialized to the coefficient module category;
it selects no arbitrary braiding or new tensor structure.
Source: HRS Section 3, ordinary symmetric derived tensor
(blueprint: lem-zl-condensed-lisse-proetale-locality). -/
noncomputable instance condensedDerivedBraiding
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    BraidedCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :=
  DerivedCategory.braidedCategory' _

/-- Inverse image along any scheme morphism, using the canonical coefficient identification,
is exact and strong symmetric monoidal. Between symmetric categories, `Functor.Braided`
is exactly strong symmetric monoidality, including invertible tensor and unit comparisons.
Source: HRS Section 3, paragraph before (3.1)
(blueprint: lem-zl-condensed-lisse-proetale-locality).

Proof (DAG step 1): `condensedPullbackHom` is the component at Λ of the monoidal comparison
`upperStarFromPointComp`, hence a ring isomorphism. The published module inverse image
extends scalars along this exact map and is exact. Its termwise derived functor is
triangulated. The canonical derived tensor comparison is invertible by
lem-weil-pbc-ringed-topoi-derived-tensor-pullback; the associator, unit and symmetry
compatibilities are lem-sfb-ringed-derived-monoidal-comparisons, giving the strong
symmetric monoidal structure for the ordinary derived tensor. -/
theorem condensed_derivedPullback_exact_symmetricMonoidal
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T X : Scheme.{u}} (f : T ⟶ X) :
    (CondensedRing.upperStar Λ.X f).mapDerivedCategory.IsTriangulated ∧
      Nonempty (CondensedRing.upperStar Λ.X f).mapDerivedCategory.Braided := by
  sorry

/-- Arbitrary scheme inverse image preserves lisse (dualizable) condensed complexes.
Source: HRS Definition 3.3 and the Section 3 pullback paragraph
(blueprint: lem-zl-condensed-lisse-proetale-locality).

Proof (DAG step 2): apply the strong symmetric monoidal functor of step 1 to a dual,
its evaluation and its coevaluation. Compose with the invertible tensor and unit
comparisons. Their coherence transports both triangle identities, so the image is dualizable. -/
theorem condensed_derivedPullback_preserves_dualizable
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :
    Nonempty (HasRightDual K) →
      Nonempty (HasRightDual ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K)) := by
  sorry

/-- Inverse image commutes naturally with scalar realization from R = Γ(*,Λ).
The realization is the actual derived extension along the constant-section ring map,
with no flatness or boundedness hypothesis on the scalar complex.
Source: HRS Section 3, (3.1) and Remark 3.2
(blueprint: lem-zl-condensed-lisse-proetale-locality).

Proof (DAG step 1, scalar clause): write scalar realization on X as D(p_X^*)(N_P), where
N_P is constant realization on the point, derived extension along its constant-section
map, and the sectionwise/internal module equivalence. This N_P is independent of X.
The natural monoidal comparison f^* p_X^* ≅ p_T^* has coefficient component α_f.
Naturality on the module action shows it respects the transported module structure.
All these inverse images are exact, so termwise localization gives the natural
comparison D(p_X^*) ⋙ D(f^*) ≅ D(p_T^*). Precompose with the functor P ↦ N_P. -/
theorem condensed_scalarRealization_pullback
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T X : Scheme.{u}} (f : T ⟶ X) :
    Nonempty (condensedScalarRealization Λ.X X ⋙
      (CondensedRing.upperStar Λ.X f).mapDerivedCategory ≅
        condensedScalarRealization Λ.X T) := by
  sorry

/-- Dualizability is local for every pro-etale covering family, including empty and
infinite families. The index universe is independent of the universe of schemes.
Source: HRS Definition 3.3 and Lemma 4.5, lisse assertion
(blueprint: lem-zl-condensed-lisse-proetale-locality).

Proof (DAG steps 3--5): the derived inverse images along a covering family are jointly
conservative by lem-zl-condensed-cover-restriction-conservative. Pro-etale localization
identifies the site of each member with the corresponding slice site.
Clause 1 of lem-sfb-proetale-object-inverse-image-restriction identifies inverse image
of every sheaf of rings, not just constant rings, with slice restriction. Transport
its module action along α_u to identify the exact derived inverse image with restriction.
Each restriction is strong symmetric monoidal by step 1. Its internal-Hom comparison
is the exact slice comparison of lem-weil-pbc-ringed-internal-hom-exact-restriction.
The second identity in lem-weil-pbc-ringed-slice-evaluation-transpose preserves transposes;
the third gives symmetry compatibility. Apply
lem-zl-dualizable-jointly-conservative-locality with these comparisons and joint
conservativity. It gives both directions, without any geometric finiteness assumption. -/
theorem condensed_dualizable_iff_proetale_cover
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :
    Nonempty (HasRightDual K) ↔
      ∀ i : 𝒰.I₀, Nonempty
        (HasRightDual ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale
