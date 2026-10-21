/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Mathlib.CategoryTheory.Localization.Predicate

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

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

/-- The sectionwise coefficient square for restriction to an open, transported by
exactly the canonical realization equivalences used to define extension by zero.
Its fixed-scalar middle square is the identity: precomposition with the open site
functor commutes with restriction of scalars.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenRestrictionCoefficientSquare {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars Z φ ⋙ sfIntrinsicOpenRestriction j A ≅
      sfIntrinsicOpenRestriction j B ⋙ proEtaleCoefficientRestrictScalars U φ :=
  Functor.isoWhiskerRight (sfInverseRealizationRestriction Z φ)
      (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence U A).functor) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Z B).inverse
      (Functor.isoWhiskerRight (Iso.refl
        (sfFixedRestriction Z φ ⋙
          ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j))
        (sfIntrinsicModuleEquivalence U A).functor) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence Z B).inverse ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
      (sfRealizationRestriction U φ).symm

/-- Identity coefficient restriction in fixed-scalar coordinates, with the identity
on every section. Source: Stacks Tag 03DA
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenFixedRestrictionId (T : Scheme.{u}) (R : Type u) [CommRing R] :
    sfFixedRestriction T (RingHom.id R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦
    (fullyFaithfulSheafToPresheaf (ProEt.topology T) _).preimageIso
      (Functor.isoWhiskerLeft M.obj
        (ModuleCat.restrictScalarsId' (RingHom.id R).ulift rfl)))
    (fun f ↦ by ext V x; rfl)

/-- The canonical identity coefficient comparison in intrinsic coordinates. It is
transported from the sectionwise identity, using the already section-normalized
realization comparison and the realization counit.
Source: Stacks Tags 03CY and 03DA
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenCoefficientRestrictionId (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R] :
    proEtaleCoefficientRestrictScalars T (RingHom.id R) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence T R).counitIso.symm
      (proEtaleCoefficientRestrictScalars T (RingHom.id R)) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T R).inverse
      (sfRealizationRestriction T (RingHom.id R)) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T R).inverse
      (Functor.isoWhiskerRight (sfOpenFixedRestrictionId T R)
        (sfIntrinsicModuleEquivalence T R).functor) ≪≫
    (sfIntrinsicModuleEquivalence T R).counitIso

/-- The identity on the extension presheaf, expressed by its generators over the
open. The unit of the recorded adjunction is the sheafification map on those
generators. Every other presheaf value is zero, so this equation includes all its
components. The coefficient square uses only the canonical realization maps.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def SfOpenRestrictionNormalized {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B)
    (e : proEtaleCoefficientRestrictScalars U φ ⋙ sfIntrinsicExtensionByZero j A ≅
      sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ) : Prop :=
  ∀ M : proEtaleRingModules U (proEtaleConstantRing U B),
    (sfIntrinsicExtensionByZeroAdjunction j A).unit.app
        ((proEtaleCoefficientRestrictScalars U φ).obj M) ≫
      (sfIntrinsicOpenRestriction j A).map (e.hom.app M) ≫
      (sfOpenRestrictionCoefficientSquare j φ).hom.app
        ((sfIntrinsicExtensionByZero j B).obj M) =
    (proEtaleCoefficientRestrictScalars U φ).map
      ((sfIntrinsicExtensionByZeroAdjunction j B).unit.app M)

/-- The published comparison is the unique comparison inducing identity on the
extension presheaves, equivalently satisfying the displayed open-unit equation.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: for an object factoring through the open, the two extension presheaves have
exactly the same module with its restricted action. Otherwise both are zero. The
identity commutes with restrictions and module maps. Sheafification of the common
abelian presheaf extends the restricted action uniquely, so its identity is linear
and invertible. The open-unit equation says exactly that this map induces those
identities before sheafification. Unique factorization through sheafification proves
uniqueness and naturality. Transport through the section-normalized realization
squares identifies this isomorphism with `sfOpenRestriction`. -/
theorem sfOpenRestriction_normalized_unique {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    SfOpenRestrictionNormalized j φ (sfOpenRestriction j φ) ∧
      ∀ e : proEtaleCoefficientRestrictScalars U φ ⋙ sfIntrinsicExtensionByZero j A ≅
          sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ,
        SfOpenRestrictionNormalized j φ e → e = sfOpenRestriction j φ := by
  sorry

/-- The sheaf comparison cocycle, including both canonical scalar associators.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: precompose both sides with the extension-presheaf sheafification unit.
The normalization gives the same identity on every nonzero value, with action
`a • m = ψ(φ(a)) • m`, and the unique map out of zero elsewhere. The sectionwise
identity restriction comparison is exactly `sfCoefficientRestrictionComp`.
Uniqueness of sheafification factorization proves the equation. -/
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
  sorry

/-- The identity coefficient law on module sheaves, with canonical identifications.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: the canonical identity restriction comparisons preserve every section. Both
sides therefore induce the identity on the extension presheaf. The unique
factorization through its sheafification gives equality. -/
theorem sfOpenRestriction_coefficient_id {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (R : Type u) [CommRing R] [Finite R]
    (M : proEtaleRingModules U (proEtaleConstantRing U R)) :
    (sfOpenRestriction j (RingHom.id R)).hom.app M ≫
        (sfOpenCoefficientRestrictionId Z R).hom.app
          ((sfIntrinsicExtensionByZero j R).obj M) =
      (sfIntrinsicExtensionByZero j R).map
        ((sfOpenCoefficientRestrictionId U R).hom.app M) := by
  sorry

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
  sorry

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
  sorry

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

Proof: restriction is additive and exact by the ordinary coefficient adjunction;
extension by zero is exact by `sfIntrinsicExtensionByZero_exact`. Their termwise
functors preserve quasi-isomorphisms and factor through the unbounded derived
categories. Under those factorization isomorphisms, the localized comparisons,
including both scalar associators, are the chain-level comparisons above.
Precomposition with localization therefore makes the two sides equal by the
cochain cocycle. Faithfulness of precomposition with localization gives equality
on every derived object. No resolution or boundedness restriction is needed. -/
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
  sorry

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
  sorry

end AlgebraicGeometry.Scheme
