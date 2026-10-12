/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons

/-! # Coefficient compatibility of derived étale adjunctions -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The canonical coefficient comparisons preserve the unit and counit of a single
bounded below inverse-image/direct-image adjunction.

Source: Stacks Project, Remark 21.19.3, Tag 07A7 (adjunction construction), and
Lemma 21.20.7(3), Tag 0D6J (natural derived direct-image comparison).
Proof: before derivation, direct image commutes with restriction sectionwise. The
inverse-image comparison is the uniqueness isomorphism of the two left adjoints
to direct image followed by coextension. Transpose through the restriction/coextension
adjunction: the unit and counit identities of leftAdjointUniq give precisely the two
identities for inverse image and direct image. Derive those identities on bounded below
complexes. The exact-functor composition isomorphisms transport the inverse-image
comparison; the right-derived direct-image comparison is characterized by its
compatibility with the right-derived units. On an injective resolution, restriction
produces a direct-image-acyclic complex, so this comparison is invertible and the
underived identities give the asserted identities after localization. Every bounded
below object is isomorphic to such a resolution. Naturality transports the identities
to the given objects. This argument concerns one adjunction, without any square or
base-change morphism.
(blueprint: lem-sbc-restrict-scalars-derived-adjunction-identities) -/
theorem derivedRestrictScalars_adjunction_identities
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (∀ M : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ')),
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
          ((Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryPlus.obj M) ≫
        (derivedBaseChangeTargetRestrictScalarsIso φ f f M).hom =
      (Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ') f).unit.app M)) ∧
    (∀ N : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ')),
      (derivedBaseChangeSourceRestrictScalarsIso φ f f N).hom ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus.map
          ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ') f).counit.app N) =
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
        ((Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus.obj N)) := by sorry

end AlgebraicGeometry.Etale
