/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullback
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.EssentialImage

/-!
# The category of bounded below complexes with a retained etale origin

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
`def-weil-compact-support-candidate`, order 1472, and the retained witness of
`def-weil-pbc-etale-origin-witness`, order 1289
(blueprint: def-sf-etale-origin-subcategory).

Objects retain the pro-etale complex and the complete etale-origin witness. Morphisms
are all morphisms between the pro-etale complexes; no map of witnesses is required.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The category of triples `(K, L, alpha)` with `K` bounded below on the pro-etale site,
`L` bounded below on the etale site, and `alpha : nu^* L ≅ K`. The sigma type retains
`K` and the recorded `EtaleOriginWitness`, hence both `L` and `alpha`. The induced
category has precisely the ambient derived morphisms between the underlying `K`s,
with the ambient identities and composition.
Source: Weil blueprint, `def-weil-compact-support-candidate`, order 1472, and
`def-weil-pbc-etale-origin-witness`, order 1289
(blueprint: def-sf-etale-origin-subcategory). -/
noncomputable abbrev EtaleOriginDerivedCategory (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :=
  InducedCategory (FiniteCoefficientDerivedCategoryPlus T Λ)
    (fun P : Σ K : FiniteCoefficientDerivedCategoryPlus T Λ, EtaleOriginWitness T Λ K ↦ P.1)

/-- Forget the retained witness and keep `K` in the bounded below pro-etale category.
On morphisms this is the identity under `InducedCategory.homEquiv`.
Source: Weil blueprint, `def-weil-compact-support-candidate`, order 1472
(blueprint: def-sf-etale-origin-subcategory). -/
noncomputable def etaleOriginForgetfulPlus (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    EtaleOriginDerivedCategory T Λ ⥤ FiniteCoefficientDerivedCategoryPlus T Λ :=
  inducedFunctor
    (fun P : Σ K : FiniteCoefficientDerivedCategoryPlus T Λ, EtaleOriginWitness T Λ K ↦ P.1)

/-- The forgetful functor is fully faithful by the induced-category construction.
Source: Weil blueprint, `def-weil-compact-support-candidate`, order 1472;
Mathlib, `CategoryTheory.fullyFaithfulInducedFunctor`
(blueprint: def-sf-etale-origin-subcategory). -/
noncomputable def etaleOriginForgetfulPlusFullyFaithful (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (etaleOriginForgetfulPlus T Λ).FullyFaithful :=
  fullyFaithfulInducedFunctor
    (fun P : Σ K : FiniteCoefficientDerivedCategoryPlus T Λ, EtaleOriginWitness T Λ K ↦ P.1)

/-- The essential image consists exactly of the bounded below complexes admitting an
etale-origin witness. Source: Weil blueprint, `def-weil-compact-support-candidate`,
order 1472, and `def-weil-pbc-etale-origin-witness`, order 1289
(blueprint: def-sf-etale-origin-subcategory).

Proof: an object in the essential image is isomorphic to the underlying `K` of a
triple. Retain that triple's `L` and compose its comparison isomorphism with the
essential-image isomorphism to give a witness for the new object. Conversely a
witness for `K` gives the triple `(K, L, alpha)`, whose forgetful image is `K`;
the identity isomorphism proves essential-image membership. -/
theorem etaleOriginForgetfulPlus_essImage (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : FiniteCoefficientDerivedCategoryPlus T Λ) :
    (etaleOriginForgetfulPlus T Λ).essImage K ↔ Nonempty (EtaleOriginWitness T Λ K) := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    exact ⟨⟨P.2.L, P.2.alpha ≪≫ e⟩⟩
  · rintro ⟨W⟩
    exact ⟨⟨K, W⟩, ⟨Iso.refl K⟩⟩

/-- Regard the witness-retaining category as a full subcategory of the unbounded
pro-etale derived category through the bounded below inclusion.
Source: Weil blueprint, `def-weil-compact-support-candidate`, order 1472
(blueprint: def-sf-etale-origin-subcategory). -/
noncomputable def etaleOriginForgetful (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    EtaleOriginDerivedCategory T Λ ⥤ FiniteCoefficientDerivedCategory T Λ :=
  etaleOriginForgetfulPlus T Λ ⋙ DerivedCategory.Plus.ι

/-- Restrict an ambient derived functor by precomposition with the forgetful functor.
Source: Weil blueprint, `def-weil-compact-support-candidate`, order 1472
(blueprint: def-sf-etale-origin-subcategory). -/
noncomputable def restrictToEtaleOrigin (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    {C : Type v} [Category.{w} C] (F : FiniteCoefficientDerivedCategory T Λ ⥤ C) :
    EtaleOriginDerivedCategory T Λ ⥤ C :=
  etaleOriginForgetful T Λ ⋙ F

end AlgebraicGeometry.ProEtale
