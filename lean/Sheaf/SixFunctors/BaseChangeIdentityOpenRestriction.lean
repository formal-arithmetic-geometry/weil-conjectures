/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison
import Sheaf.Paper.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Base change and identity on an open restriction

Source: `literature/stacks-project/sites-cohomology.tex`, Tag 0D6G, label
`lemma-restrict-direct-image-open`; Tag 08FI, label `lemma-restrict-K-injective-to-open`;
and the restriction clause of `remark-base-change`
(blueprint: lem-sfb-base-change-identity-open-restriction).

The statement uses the ordinary unbounded module-object derived categories and the canonical
mate of the derived pullback square.  The two restriction isomorphisms are required to be the
canonical K-injective, sectionwise identity comparisons; the displayed equality records their
normalization after the two canonical pullback composition comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ]

/-- The module-object category on a pro-etale scheme. Source: sk-def-sfb-module-derived-pushpull
(blueprint: lem-sfb-base-change-identity-open-restriction). -/
abbrev moduleObjectCategory (X : Scheme.{u}) :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)

/-- The total derived inverse image used in the statement.
Source: Stacks Project, `remark-base-change`, and sk-def-sfb-module-derived-pushpull
(blueprint: lem-sfb-base-change-identity-open-restriction). -/
noncomputable abbrev derivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar Λ f).leftDerivedFunctor

/-- The total derived direct image used in the statement.
Source: Stacks Project, Tag 0D6G, and sk-def-sfb-module-derived-pushpull
(blueprint: lem-sfb-base-change-identity-open-restriction). -/
noncomputable abbrev derivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.rightDerivedFunctor (lowerStar Λ f)

/-- Derived pullback comparison attached to a commutative square of schemes.
Source: the canonical termwise pullback comparison in the restriction clause of
`remark-base-change` (blueprint: lem-sfb-base-change-identity-open-restriction). -/
noncomputable def derivedPullbackSquareIso
    {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (w : g' ≫ f = f' ≫ g) :
    (upperStar Λ g).leftDerivedFunctor ⋙
        (upperStar Λ f').leftDerivedFunctor ≅
      (upperStar Λ f).leftDerivedFunctor ⋙
        (upperStar Λ g').leftDerivedFunctor := by
  exact (leftDerivedUpperStarComp Λ f' g).symm ≪≫
    eqToIso (congrArg (fun a ↦ (upperStar Λ a).leftDerivedFunctor) w.symm) ≪≫
    leftDerivedUpperStarComp Λ g' f

/-- The canonical restriction comparison, defined without choosing an isomorphism.
It is the pullback composition `j^* = i^* h^*` at `Rh_*`, followed by `i^*` of the
specified derived counit. Under the open identity-locus hypotheses the theorem below
asserts that it is invertible. Step 6 of the node identifies this precise comparison
with the K-injective sectionwise restriction of Stacks Project, Tags 0D6G and 08FI.
Source: `lemma-restrict-direct-image-open` and the node's proof, steps 4--6
(blueprint: lem-sfb-base-change-identity-open-restriction). -/
noncomputable def derivedIdentityOpenRestrictionComparison
    {D Z U : Scheme.{u}} (h : D ⟶ Z) (i : U ⟶ D) (j : U ⟶ Z)
    (hi : i ≫ h = j) :
    derivedLowerStar (Λ := Λ) h ⋙ derivedUpperStar (Λ := Λ) j ⟶
      derivedUpperStar (Λ := Λ) i :=
  Functor.whiskerLeft (derivedLowerStar (Λ := Λ) h)
      ((eqToIso (congrArg (fun a ↦ derivedUpperStar (Λ := Λ) a) hi)).inv ≫
        (leftDerivedUpperStarComp Λ i h).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedUpperStarLowerStarAdjunction Λ h).counit
      (derivedUpperStar (Λ := Λ) i) ≫
    (Functor.leftUnitor _).hom

/-- The specified derived mate
`v^* Rh_* K ⟶ Rh'_* w^* K` of the derived pullback square.
Source: the mate construction in `remark-base-change`
(blueprint: lem-sfb-base-change-identity-open-restriction). -/
noncomputable def derivedBaseChangeIdentityMate
    {D Z D' Z' : Scheme.{u}}
    (h : D ⟶ Z) (h' : D' ⟶ Z') (v : Z' ⟶ Z) (w : D' ⟶ D)
    (comm : w ≫ h = h' ≫ v)
    (K : DerivedCategory (moduleObjectCategory (Λ := Λ) D)) :
    (upperStar Λ v).leftDerivedFunctor.obj
        ((Functor.rightDerivedFunctor (lowerStar Λ h)).obj K) ⟶
      (Functor.rightDerivedFunctor (lowerStar Λ h')).obj
        ((upperStar Λ w).leftDerivedFunctor.obj K) := by
  let mate :=
    (mateEquiv
      (derivedUpperStarLowerStarAdjunction Λ h)
      (derivedUpperStarLowerStarAdjunction Λ h')
      (TwoSquare.mk _ _ _ _
        (derivedPullbackSquareIso (Λ := Λ) w h' h v comm).hom)).natTrans
  exact mate.app K

/-- Base change restricts to the identity on the open where the vertical map is the identity.
Source: Stacks Project, Tag 0D6G, label `lemma-restrict-direct-image-open`; Tag 08FI,
label `lemma-restrict-K-injective-to-open`; and `remark-base-change`, restriction clause
(blueprint: lem-sfb-base-change-identity-open-restriction).

Proof (the node's eight steps).
1. Pass to the ringed-site module model using the weakly-etale localization and internal-module
   transport, and use the cartesian coefficient comparison for exact pullback.
2. The underived direct-image restriction is the sectionwise identity on the slice over the open;
   the pullback comparison is its adjunction conjugate, with tensor-unit normalization.
3. The underived unit and counit equations follow from the tensor adjunction and the sectionwise
   identity, for the unprimed and primed diagrams.
4. Compute on a K-injective resolution; exact restriction and K-injective localization give the
   canonical derived restriction isomorphisms for unbounded complexes.
5. The exact restriction comparison is itself a right-derived functor comparison, so it preserves
   the derived adjunction units and counits.
6. Apply the derived adjoint-square comparison to both diagrams, retaining the normalized units,
   counits, and restriction isomorphisms.
7. The two canonical pullback composition comparisons satisfy the displayed reassociation identity
   by their sectionwise fibre-product normalization.
8. Expand the mate, use naturality and the two unit/counit equations, and cancel the source and
   target restriction isomorphisms. This gives the displayed identity for every unbounded K.
-/
theorem baseChangeIdentityOpenRestriction
    {k : Type u} [Field k] {p ell : ℕ} [Fact ell.Prime] [CharP k p]
    (hp : 0 < p) (hple : p ≠ ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {D Z U D' Z' U' : Scheme.{u}}
    [D.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [D'.Over (Spec (.of k))] [Z'.Over (Spec (.of k))] [U'.Over (Spec (.of k))]
    [LocallyOfFiniteType (D ↘ Spec (.of k))] [QuasiCompact (D ↘ Spec (.of k))]
    [IsSeparated (D ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (D' ↘ Spec (.of k))] [QuasiCompact (D' ↘ Spec (.of k))]
    [IsSeparated (D' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z' ↘ Spec (.of k))] [QuasiCompact (Z' ↘ Spec (.of k))]
    [IsSeparated (Z' ↘ Spec (.of k))]
    [LocallyOfFiniteType (U' ↘ Spec (.of k))] [QuasiCompact (U' ↘ Spec (.of k))]
    [IsSeparated (U' ↘ Spec (.of k))]
    (h : D ⟶ Z) [h.IsOver (Spec (.of k))]
    (j : U ⟶ Z) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (i : U ⟶ D) [i.IsOver (Spec (.of k))] (hi : i ≫ h = j)
    (hU : IsPullback i (𝟙 U) h j)
    (v : Z' ⟶ Z) [v.IsOver (Spec (.of k))]
    (h' : D' ⟶ Z') [h'.IsOver (Spec (.of k))]
    (w : D' ⟶ D) [w.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare w h' h v)
    (j' : U' ⟶ Z') [j'.IsOver (Spec (.of k))]
    (i' : U' ⟶ D') [i'.IsOver (Spec (.of k))]
    (vU : U' ⟶ U) [vU.IsOver (Spec (.of k))]
    (hi' : i' ≫ h' = j') (hU' : IsPullback i' (𝟙 U') h' j')
    (hbaseU : vU ≫ j = j' ≫ v)
    (hOpen : IsPullback vU j' j v)
    (hbaseD : i' ≫ w = vU ≫ i) :
    IsIso (derivedIdentityOpenRestrictionComparison (Λ := Λ) h i j hi) ∧
      IsIso (derivedIdentityOpenRestrictionComparison (Λ := Λ) h' i' j' hi') ∧
      ∀ (K : DerivedCategory (moduleObjectCategory (Λ := Λ) D)),
        (derivedPullbackSquareIso (Λ := Λ) vU j' j v hbaseU).hom.app
            ((derivedLowerStar (Λ := Λ) h).obj K) ≫
          (derivedUpperStar (Λ := Λ) vU).map
            ((derivedIdentityOpenRestrictionComparison (Λ := Λ) h i j hi).app K) =
        (derivedUpperStar (Λ := Λ) j').map
            (derivedBaseChangeIdentityMate (Λ := Λ) h h' v w sq.w K) ≫
          (derivedIdentityOpenRestrictionComparison (Λ := Λ) h' i' j' hi').app
            ((derivedUpperStar (Λ := Λ) w).obj K) ≫
          (derivedPullbackSquareIso (Λ := Λ) i' vU w i hbaseD).inv.app K := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
