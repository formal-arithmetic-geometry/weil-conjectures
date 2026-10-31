/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-!
# Normalized finite coefficient comparison data

Source: Bhatt--Scholze, Sections 6.5 and 6.7; Stacks Tags 03DI, 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars).

(blueprint: def-sf-compact-support-restriction-data).

All comparisons are normalized before choosing them: realization preserves sections,
extension by zero uses the adjunction unit, and derived direct image uses its
K-injective comparison. Thus the compactification and coefficient map enter the actual
functors and maps.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

/-- Fixed scalar restriction on the pro-etale site. Source: Stacks Tag 03DA
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable abbrev sfFixedRestriction (T : Scheme.{u}) (φ : A →+* B) :=
  sheafCompose (ProEt.topology T) (ModuleCat.restrictScalars.{u + 1} φ.ulift)

/-- Realization commutes with scalar restriction by the identity on the sheafified
underlying abelian presheaf. Source: Stacks Tags 00YV and 03DA
(blueprint: lem-sf-compact-support-restriction-of-scalars).
Proof: the two input abelian presheaves agree. Module sheafification has precisely
abelian sheafification as its underlying sheaf. The actions agree on constant scalar
sections by naturality of the coefficient unit and hence on all locally constant
sections. Identity is therefore linear and natural, and sectionwise identity is unique. -/
theorem sfRealizationRestriction_existsUnique (T : Scheme.{u}) (φ : A →+* B) :
    ∃! e : (sfIntrinsicModuleEquivalence T B).functor ⋙
        proEtaleCoefficientRestrictScalars T φ ≅
      sfFixedRestriction T φ ⋙ (sfIntrinsicModuleEquivalence T A).functor,
      ∀ (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
        (U : T.ProEtᵒᵖ)
        (x : (((sfIntrinsicModuleEquivalence T B).functor.obj M).val.obj U)),
        (e.hom.app M).val.app U x = x := by
  let φ' : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B := φ.ulift
  let δ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ'))
  apply realization_restrict_existsUnique (ProEt.topology T) _ _
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
    (ProEtale.finiteCoefficientIntrinsicScalarMap T B) φ' δ
  exact (congrArg (fun k ↦ Functor.whiskerRight k
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (toSheafify_naturality (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ')))).symm

/-- The sectionwise normalized realization comparison. Source: Stacks Tag 00YV
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfRealizationRestriction (T : Scheme.{u}) (φ : A →+* B) :=
  (sfRealizationRestriction_existsUnique T φ).exists.choose

/-- The inverse-equivalence coefficient square, obtained by unit and counit from the
normalized realization square. Source: Stacks Tag 00YV
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfInverseRealizationRestriction (T : Scheme.{u}) (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars T φ ⋙ (sfIntrinsicModuleEquivalence T A).inverse ≅
      (sfIntrinsicModuleEquivalence T B).inverse ⋙ sfFixedRestriction T φ :=
  Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence T B).counitIso.symm
      (proEtaleCoefficientRestrictScalars T φ ⋙ (sfIntrinsicModuleEquivalence T A).inverse) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T B).inverse
      (Functor.isoWhiskerRight (sfRealizationRestriction T φ)
        (sfIntrinsicModuleEquivalence T A).inverse) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence T B).inverse ⋙ sfFixedRestriction T φ)
      (sfIntrinsicModuleEquivalence T A).unitIso.symm

/-- Fixed-scalar extension by zero commutes with restriction: both sides are left
adjoint to the same objectwise composite of open restriction and coextension.
The left-adjoint uniqueness map is normalized by the adjunction units.
Source: Stacks Tag 03DI (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfFixedOpenRestriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    sfFixedRestriction X φ ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ≅
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j ⋙
        sfFixedRestriction Z φ :=
  ((Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) φ.ulift).comp
      (ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).leftAdjointUniq
    ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).comp
      (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) φ.ulift))

/-- The intrinsic extension-by-zero coefficient square, transported by the canonical
realization equivalences. Source: Stacks Tags 03DI and 00YV
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfOpenRestriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars X φ ⋙ sfIntrinsicExtensionByZero j A ≅
      sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ :=
  Functor.isoWhiskerRight (sfInverseRealizationRestriction X φ)
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence Z A).functor) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X B).inverse
      (Functor.isoWhiskerRight (sfFixedOpenRestriction j φ)
        (sfIntrinsicModuleEquivalence Z A).functor) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence X B).inverse ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
      (sfRealizationRestriction Z φ).symm

/-- Derived direct-image coefficient comparison selected with the full K-injective
normalization of the recorded direct-image theorem. That normalization determines the
natural isomorphism on every K-injective representative and hence after localization.
Source: Stacks Tags 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfDerivedImageRestriction {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (φ : A →+* B) :
    (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory ⋙
        proEtaleConstantDerivedDirectImage g A ≅
      proEtaleConstantDerivedDirectImage g B ⋙
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory :=
  (proEtaleDerivedDirectImage_restrictScalars g φ).choose

/-- The specified compact-support comparison is the extension-by-zero square followed
by the direct-image square, with no change of compactification. Source: Bhatt--Scholze,
Lemma 6.7.7; Stacks Tags 03DI and 0D6E
(blueprint: lem-sf-compact-support-restriction-of-scalars).
(blueprint: def-sf-compact-support-restriction-data). -/
noncomputable def sfCompactSupportRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (φ : A →+* B) :
    (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory ⋙
        sfAmbientCompactSupportCandidate A c ≅
      sfAmbientCompactSupportCandidate B c ⋙
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory :=
  Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ))
      (proEtaleConstantDerivedDirectImage c.g A) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
      (sfDerivedImageRestriction c.g φ)

/-- The normalized scalar-restriction composition map, using the shared sectionwise
identity comparison for commutative ring sheaves. Source: Stacks Tag 03DA
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfCoefficientRestrictionComp (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C) :
    proEtaleCoefficientRestrictScalars T ψ ⋙ proEtaleCoefficientRestrictScalars T φ ≅
      proEtaleCoefficientRestrictScalars T (ψ.comp φ) :=
  pbcRestrictComp
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom ψ.ulift))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (ψ.comp φ).ulift))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp _ _).symm

/-- The termwise derived scalar composition map. Source: Stacks Tag 015F
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfDerivedCoefficientRestrictionComp (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfCoefficientRestrictionComp T φ ψ)

end AlgebraicGeometry.Scheme
