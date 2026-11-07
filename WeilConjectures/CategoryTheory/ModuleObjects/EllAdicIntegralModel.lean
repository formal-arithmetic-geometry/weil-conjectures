/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!

# Integral models of bounded constructible `ℓ`-adic complexes

Let `X` be a topologically noetherian scheme, `ℓ` a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of
`ℚ_ℓ` with ring of integers `𝒪_E`. The derived extension of scalars
`E ⊗ᴸ_{𝒪_E} - : D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, E)`
(`ProEtale.boundedConstructibleExtendScalars`) is a localization functor at the morphisms whose
mapping cone is killed by a power of `ℓ`
(`ProEtale.isLocalization_boundedConstructibleExtendScalars`,
blueprint `sk-thm-sfb-rationalization-comparison`). This file draws the consequences used by the
rational model of Frobenius correspondences (blueprint `sk-lem-tf-rational-model`):

* every bounded constructible `E`-complex has an *integral model*: it is isomorphic to `E ⊗ᴸ K₀`
  for a bounded constructible `𝒪_E`-complex `K₀`
  (`ProEtale.exists_boundedConstructibleExtendScalars_obj_iso`);
* every morphism `E ⊗ᴸ K₀ ⟶ E ⊗ᴸ L₀` becomes integral after multiplication by a power of `ℓ`:
  `ℓ^N • ψ = E ⊗ᴸ θ` for a morphism `θ : K₀ ⟶ L₀`
  (`ProEtale.exists_pow_smul_eq_boundedConstructibleExtendScalars_map`);
* combined with the descent of `ℚ̄_ℓ`-complexes to a finite subextension (blueprint
  `sk-thm-sfb-qlbar-two-colimit`, `ProEtale.constructibleCocone_essSurjObj`), every bounded
  constructible `ℚ̄_ℓ`-complex is isomorphic to `ℚ̄_ℓ ⊗ᴸ_{E} (E ⊗ᴸ_{𝒪_E} K₀)` for some finite `E`
  and some bounded constructible `𝒪_E`-complex `K₀`
  (`ProEtale.exists_padicAlgCl_iso_integralModel`).

The `Hom` statement holds for every localization functor at the morphisms with torsion mapping
cone (`CategoryTheory.Rationalization.exists_smul_eq_map_of_isLocalization`): a morphism of the
localization is a left fraction `f ≫ s⁻¹`, and a morphism `s` with `m`-torsion cone has an
inverse up to `m` (`CategoryTheory.Rationalization.exists_comp_eq_smul_id`).

-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] [TopologicalSpace.NoetherianSpace X]

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} -` on bounded constructible complexes is
additive: it is isomorphic to the localization functor to the rationalization followed by an
equivalence (`ProEtale.rationalizationQCompEquivalenceIso`), and an equivalence of triangulated,
hence additive, categories preserves binary products. -/
instance additive_boundedConstructibleExtendScalars (E : FiniteIntermediateField ℓ) :
    (boundedConstructibleExtendScalars X ℓ E).Additive := by
  -- the instances on the rationalization and the equivalence are given explicitly: searching
  -- for them unfolds `rationalizationEquivalence` against the instances of the six functors
  have : HasBinaryBiproducts (Rationalization (Submonoid.powers (ℓ : ℤ))
      (BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :=
    Pretriangulated.instHasBinaryBiproducts
  have : HasBinaryProducts (Rationalization (Submonoid.powers (ℓ : ℤ))
      (BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :=
    hasBinaryProducts_of_hasBinaryBiproducts
  have := (rationalizationEquivalence X ℓ E).toAdjunction.isLeftAdjoint
  have : (rationalizationEquivalence X ℓ E).functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : PreservesLimitsOfShape (Discrete WalkingPair) (rationalizationEquivalence X ℓ E).functor :=
    (rationalizationEquivalence X ℓ E).symm.toAdjunction.rightAdjoint_preservesLimits
      |>.preservesLimitsOfShape
  have : (rationalizationEquivalence X ℓ E).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact Functor.additive_of_iso (rationalizationQCompEquivalenceIso X ℓ E)

/-- **Integral models of objects** (blueprint `sk-lem-tf-rational-model`, from
`sk-thm-sfb-rationalization-comparison`): every bounded constructible `E`-complex `K` on a
topologically noetherian scheme is isomorphic to `E ⊗ᴸ_{𝒪_E} K₀` for a bounded constructible
`𝒪_E`-complex `K₀`, the extension of scalars being a localization functor. -/
lemma exists_boundedConstructibleExtendScalars_obj_iso (E : FiniteIntermediateField ℓ)
    (K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) :
    ∃ K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X),
      Nonempty ((boundedConstructibleExtendScalars X ℓ E).obj K₀ ≅ K) :=
  have := Localization.essSurj (boundedConstructibleExtendScalars X ℓ E)
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)
  ⟨_, ⟨(boundedConstructibleExtendScalars X ℓ E).objObjPreimageIso K⟩⟩


/-- **Integral models of `ℚ̄_ℓ`-complexes** (blueprints `sk-thm-sfb-qlbar-two-colimit` and
`sk-lem-tf-rational-model`): every bounded constructible `ℚ̄_ℓ`-complex `K` on a topologically
noetherian scheme is isomorphic to `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for a finite subextension `E` and a
bounded constructible `𝒪_E`-complex `K₀`: `K` descends to some `E`, and the descended complex has
an integral model. -/
lemma exists_padicAlgCl_iso_integralModel (K : PadicAlgClConstructible X ℓ) :
    ∃ (E : FiniteIntermediateField ℓ)
      (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)),
      Nonempty ((constructibleToPadicAlgCl X ℓ E).obj
        ((boundedConstructibleExtendScalars X ℓ E).obj K₀) ≅ K) := by
  obtain ⟨E, K_E, ⟨e⟩⟩ := constructibleCocone_essSurjObj X ℓ K
  obtain ⟨K₀, ⟨e₀⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso X ℓ E K_E
  exact ⟨E, K₀, ⟨(constructibleToPadicAlgCl X ℓ E).mapIso e₀ ≪≫ e⟩⟩

end AlgebraicGeometry.ProEtale
