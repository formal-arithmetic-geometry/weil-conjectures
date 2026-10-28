/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.SfCompactSupportRestrictionData
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionData
import all Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionAux
import all Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionRealizationAux
import Sheaf.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Coherent scalar restriction for open extension by zero

Source: Stacks Project, Tags 03DI and 03CY; derived.tex, Tag 015F; categories.tex,
Tag 04VG (blueprint: lem-sf-open-extension-scalar-restriction-coherence).

The comparisons are the published `sfOpenRestriction` and its exact termwise
localization. Normalization is expressed on the open adjunction unit: on each
nonzero summand of the defining extension presheaf it is the identity; maps from
all remaining values, which are zero, are unique. Thus this unit equation is
precisely the pre-sheafification normalization, without a choice of stalks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Scheme


variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

attribute [local irreducible] ProEtale.openImmersionLowerShriekAdjunction
attribute [local irreducible] sfIntrinsicModuleEquivalence

/-- The published comparison is the unique comparison inducing identity on the
extension presheaves, equivalently satisfying the displayed open-unit equation.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: the fixed-scalar comparison is the uniqueness isomorphism between two
composite left adjoints. Evaluate its unit equation on a section and at 1 in the
coextended module to get the open-unit normalization. Its adjunction mate is thus
the identity restriction square. The realization comparisons are also mates, so
compatibility of mates with pasting identifies the intrinsic comparison's mate
with the inverse coefficient square. The mate unit equation gives normalization.
The open adjunction hom equivalence and cancellation of the coefficient-square
isomorphism give uniqueness. -/
theorem sfOpenRestriction_normalized_unique {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    SfOpenRestrictionNormalized j φ (sfOpenRestriction j φ) ∧
      ∀ e : proEtaleCoefficientRestrictScalars U φ ⋙ sfIntrinsicExtensionByZero j A ≅
          sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ,
        SfOpenRestrictionNormalized j φ e → e = sfOpenRestriction j φ := by
  refine ⟨open_normalized j φ, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((sfIntrinsicExtensionByZeroAdjunction j A).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply (cancel_mono ((sfOpenRestrictionCoefficientSquare j φ).hom.app
    ((sfIntrinsicExtensionByZero j B).obj M))).mp
  simpa only [Category.assoc] using (he M).trans ((open_normalized j φ) M).symm

/-- The sheaf comparison cocycle, including both canonical scalar associators.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: the fixed-scalar cocycle follows from its unit normalization and
injectivity of the open adjunction hom equivalence. The realization comparison
preserves sections, so its composition agrees with the prescribed intrinsic scalar
compositor. Taking adjunction mates gives the corresponding inverse-realization
composition law. Expand the published open comparison, apply these composition
laws, and use naturality to obtain the stated cocycle. -/
theorem sfOpenRestriction_coefficient_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules U (proEtaleConstantRing U C)) :
    (sfIntrinsicExtensionByZero j A).map
        ((sfCoefficientRestrictionComp U φ ψ).hom.app M) ≫
      (sfOpenRestriction j (ψ.comp φ)).hom.app M =
    (sfOpenRestriction j φ).hom.app ((proEtaleCoefficientRestrictScalars U ψ).obj M) ≫
      (proEtaleCoefficientRestrictScalars Z φ).map
        ((sfOpenRestriction j ψ).hom.app M) ≫
      (sfCoefficientRestrictionComp Z φ ψ).hom.app
        ((sfIntrinsicExtensionByZero j C).obj M) := by
  let N := (sfIntrinsicModuleEquivalence U C).inverse.obj M
  have hn₁ := (sfRealizationRestriction Z φ).inv.naturality
    ((ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).map
        ((sfInverseRealizationRestriction U ψ).hom.app M))
  have hn₂ := (sfRealizationRestriction Z φ).inv.naturality
    ((sfFixedOpenRestriction j ψ).hom.app N)
  have hn₃ := (sfFixedOpenRestriction j φ).hom.naturality
    ((sfInverseRealizationRestriction U ψ).hom.app M)
  simp only [Functor.comp_map] at hn₁ hn₂ hn₃
  simp only [sfOpenRestriction, sfIntrinsicExtensionByZero,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj] at hn₁ hn₂ hn₃ ⊢
  slice_rhs 3 4 => exact hn₁.symm
  slice_rhs 4 5 => exact hn₂.symm
  slice_rhs 5 7 => exact realization_inv_comp Z φ ψ _
  simp only [← (sfIntrinsicModuleEquivalence Z A).functor.map_comp_assoc]
  congr 2
  slice_rhs 2 3 => exact hn₃.symm
  simp only [Category.assoc]
  slice_rhs 3 4 => exact (fixed_open_comp j φ ψ N).symm
  simp only [← Functor.map_comp_assoc]
  rw [inverse_realization_comp]


/-- The identity coefficient law on module sheaves, with canonical identifications.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: the canonical identity restriction comparison preserves each section,
by the realization normalization and the equivalence counit identity. Specialize
the coefficient cocycle to two identity homomorphisms, use naturality, and cancel
its first invertible open-comparison component. Equality on sections identifies
the resulting scalar-restricted equation with the required identity equation. -/
theorem sfOpenRestriction_coefficient_id {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (R : Type u) [CommRing R] [Finite R]
    (M : proEtaleRingModules U (proEtaleConstantRing U R)) :
    (sfOpenRestriction j (RingHom.id R)).hom.app M ≫
        (sfOpenCoefficientRestrictionId Z R).hom.app
          ((sfIntrinsicExtensionByZero j R).obj M) =
      (sfIntrinsicExtensionByZero j R).map
        ((sfOpenCoefficientRestrictionId U R).hom.app M) := by
  have hc := sfOpenRestriction_coefficient_comp j (RingHom.id R) (RingHom.id R) M
  have hn := (sfOpenRestriction j (RingHom.id R)).hom.naturality
    ((sfOpenCoefficientRestrictionId U R).hom.app M)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [restriction_id_comp, restriction_id_comp] at hc
  change (sfIntrinsicExtensionByZero j R).map
      ((proEtaleCoefficientRestrictScalars U (RingHom.id R)).map
        ((sfOpenCoefficientRestrictionId U R).hom.app M)) ≫
      (sfOpenRestriction j (RingHom.id R)).hom.app M = _ at hc
  rw [hn] at hc
  have hmap := (cancel_epi ((sfOpenRestriction j (RingHom.id R)).hom.app
    ((proEtaleCoefficientRestrictScalars U (RingHom.id R)).obj M))).mp hc
  rw [← Functor.map_comp] at hmap
  ext V x
  exact congrArg (fun f ↦ f.val.app V x) hmap.symm

/-- The same cocycle on all cochain complexes, without a boundedness condition.
Source: Stacks Tag 015F, with Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: apply the sheaf comparisons in every degree. Their naturality makes these
maps and their inverses chain maps. The sheaf cocycle in each degree proves the
chain-map equation; it does not depend on the range of nonzero degrees. -/
theorem sfOpenRestriction_cochain_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (K : CochainComplex (proEtaleRingModules U (proEtaleConstantRing U C)) ℤ) :
    ((sfIntrinsicExtensionByZero j A).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (sfCoefficientRestrictionComp U φ ψ)
          (.up ℤ)).hom.app K) ≫
      (NatIso.mapHomologicalComplex (sfOpenRestriction j (ψ.comp φ))
        (.up ℤ)).hom.app K =
    (NatIso.mapHomologicalComplex (sfOpenRestriction j φ) (.up ℤ)).hom.app
        (((proEtaleCoefficientRestrictScalars U ψ).mapHomologicalComplex (.up ℤ)).obj K) ≫
      ((proEtaleCoefficientRestrictScalars Z φ).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (sfOpenRestriction j ψ) (.up ℤ)).hom.app K) ≫
      (NatIso.mapHomologicalComplex (sfCoefficientRestrictionComp Z φ ψ)
        (.up ℤ)).hom.app
        (((sfIntrinsicExtensionByZero j C).mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact sfOpenRestriction_coefficient_comp j φ ψ (K.X n)

/-- The identity coefficient law for arbitrary cochain complexes.
Source: Stacks Tag 015F, with Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: the sheaf identity law holds in each degree, hence it is equality of the
termwise natural chain maps. Naturality also supplies their inverse chain maps. -/
theorem sfOpenRestriction_cochain_id {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (R : Type u) [CommRing R] [Finite R]
    (K : CochainComplex (proEtaleRingModules U (proEtaleConstantRing U R)) ℤ) :
    (NatIso.mapHomologicalComplex (sfOpenRestriction j (RingHom.id R))
        (.up ℤ)).hom.app K ≫
      (NatIso.mapHomologicalComplex (sfOpenCoefficientRestrictionId Z R)
        (.up ℤ)).hom.app
        (((sfIntrinsicExtensionByZero j R).mapHomologicalComplex (.up ℤ)).obj K) =
    ((sfIntrinsicExtensionByZero j R).mapHomologicalComplex (.up ℤ)).map
      ((NatIso.mapHomologicalComplex (sfOpenCoefficientRestrictionId U R)
        (.up ℤ)).hom.app K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact sfOpenRestriction_coefficient_id j R (K.X n)

/-- The prescribed comparison on unbounded derived categories: exact termwise
localization of the already normalized sheaf comparison, with the exact-functor
composition identifications at its endpoints.
Source: Stacks Tag 015F and categories.tex Tag 04VG
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenRestrictionDerived {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    (proEtaleCoefficientRestrictScalars U φ).mapDerivedCategory ⋙
        (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      (sfIntrinsicExtensionByZero j B).mapDerivedCategory ⋙
        (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)

/-- Canonical identification of derived identity coefficient restriction with the
identity functor, localized from the sectionwise identity comparison.
Source: Stacks Tag 015F
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenDerivedCoefficientRestrictionId (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R] :
    (proEtaleCoefficientRestrictScalars T (RingHom.id R)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (sfOpenCoefficientRestrictionId T R) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The prescribed coefficient cocycle on the entire unbounded derived category.
Source: Stacks Tag 015F and categories.tex Tag 04VG
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: all functors are additive and exact by the existing scalar-restriction
and extension-by-zero instances. Cancel the scalar compositors in the sheaf cocycle
to put it in the orientation of the existing exact derived-square composition
theorem. Apply that theorem, take its component at the arbitrary derived object,
and cancel the invertible derived scalar compositors. This uses unbounded exact
localization, with no resolution or degree bounds. -/
theorem sfOpenRestriction_derived_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (K : proEtaleDerivedCategory U C) :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
        ((sfDerivedCoefficientRestrictionComp U φ ψ).hom.app K) ≫
      (sfOpenRestrictionDerived j (ψ.comp φ)).hom.app K =
    (sfOpenRestrictionDerived j φ).hom.app
        ((proEtaleCoefficientRestrictScalars U ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory.map
        ((sfOpenRestrictionDerived j ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Z φ ψ).hom.app
        ((sfIntrinsicExtensionByZero j C).mapDerivedCategory.obj K) := by
  have hq (M : proEtaleRingModules U (proEtaleConstantRing U C)) :
      (sfIntrinsicExtensionByZero j A).map
          ((sfCoefficientRestrictionComp U φ ψ).inv.app M) ≫
        (sfOpenRestriction j φ).hom.app
          ((proEtaleCoefficientRestrictScalars U ψ).obj M) ≫
        (proEtaleCoefficientRestrictScalars Z φ).map
          ((sfOpenRestriction j ψ).hom.app M) =
      (sfOpenRestriction j (ψ.comp φ)).hom.app M ≫
        (sfCoefficientRestrictionComp Z φ ψ).inv.app
          ((sfIntrinsicExtensionByZero j C).obj M) := by
    have h := congrArg (fun t ↦
      (sfIntrinsicExtensionByZero j A).map
        ((sfCoefficientRestrictionComp U φ ψ).inv.app M) ≫ t ≫
      (sfCoefficientRestrictionComp Z φ ψ).inv.app
        ((sfIntrinsicExtensionByZero j C).obj M))
      (sfOpenRestriction_coefficient_comp j φ ψ M)
    simp only [Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app] at h
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h.symm
  have hd := Functor.mapDerivedCategorySquareIso_comp
    (proEtaleCoefficientRestrictScalars U ψ) (proEtaleCoefficientRestrictScalars U φ)
    (proEtaleCoefficientRestrictScalars U (ψ.comp φ))
    (proEtaleCoefficientRestrictScalars Z ψ) (proEtaleCoefficientRestrictScalars Z φ)
    (proEtaleCoefficientRestrictScalars Z (ψ.comp φ))
    (sfIntrinsicExtensionByZero j C) (sfIntrinsicExtensionByZero j B)
    (sfIntrinsicExtensionByZero j A)
    (sfOpenRestriction j ψ) (sfOpenRestriction j φ)
    (sfOpenRestriction j (ψ.comp φ))
    (sfCoefficientRestrictionComp U φ ψ).symm
    (sfCoefficientRestrictionComp Z φ ψ).symm hq
  have hk := congrArg (fun e ↦ e.hom.app K) hd
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.mapDerivedCategoryNatIso_symm] at hk
  change (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
        ((sfDerivedCoefficientRestrictionComp U φ ψ).inv.app K) ≫
      (sfOpenRestrictionDerived j φ).hom.app
        ((proEtaleCoefficientRestrictScalars U ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory.map
        ((sfOpenRestrictionDerived j ψ).hom.app K) =
    (sfOpenRestrictionDerived j (ψ.comp φ)).hom.app K ≫
      (sfDerivedCoefficientRestrictionComp Z φ ψ).inv.app
        ((sfIntrinsicExtensionByZero j C).mapDerivedCategory.obj K) at hk
  have h := congrArg (fun t ↦
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
      ((sfDerivedCoefficientRestrictionComp U φ ψ).hom.app K) ≫ t ≫
    (sfDerivedCoefficientRestrictionComp Z φ ψ).hom.app
      ((sfIntrinsicExtensionByZero j C).mapDerivedCategory.obj K)) hk
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app] at h
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  erw [Category.comp_id] at h
  exact h.symm

/-- The identity coefficient comparison on all unbounded derived objects.
Source: Stacks Tag 015F and categories.tex Tag 04VG
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: localize the cochain identity equation with the exact factorization
isomorphisms. Precomposition with the localization functor is faithful on natural
transformations, so its equality on every complex proves the derived equation. -/
theorem sfOpenRestriction_derived_id {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (R : Type u) [CommRing R] [Finite R]
    (K : proEtaleDerivedCategory U R) :
    (sfOpenRestrictionDerived j (RingHom.id R)).hom.app K ≫
        (sfOpenDerivedCoefficientRestrictionId Z R).hom.app
          ((sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj K) =
      (sfIntrinsicExtensionByZero j R).mapDerivedCategory.map
        ((sfOpenDerivedCoefficientRestrictionId U R).hom.app K) := by
  have hi (M : proEtaleRingModules U (proEtaleConstantRing U R)) :
      (sfOpenRestriction j (RingHom.id R)).inv.app M ≫
        (sfIntrinsicExtensionByZero j R).map
          ((sfOpenCoefficientRestrictionId U R).hom.app M) =
      (sfOpenCoefficientRestrictionId Z R).hom.app
        ((sfIntrinsicExtensionByZero j R).obj M) := by
    rw [← sfOpenRestriction_coefficient_id j R M]
    simp
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_id
    (sfOpenRestriction j (RingHom.id R)).symm
    (sfOpenCoefficientRestrictionId U R) (sfOpenCoefficientRestrictionId Z R) hi K
  have hs : Functor.mapDerivedCategorySquareIso
        (sfOpenRestriction j (RingHom.id R)).symm =
      (sfOpenRestrictionDerived j (RingHom.id R)).symm := by
    apply Iso.ext
    simp only [sfOpenRestrictionDerived, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hs] at hd
  rw [← cancel_epi ((sfOpenRestrictionDerived j (RingHom.id R)).inv.app K)]
  simpa only [sfOpenDerivedCoefficientRestrictionId, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.symm_hom] using hd.symm

end AlgebraicGeometry.Scheme
