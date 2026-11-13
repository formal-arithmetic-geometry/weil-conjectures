/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingCore
import WeilConjectures.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingStalkBijective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# A generic embedding of an ideal multiple into an ideal sum

Stacks Project, Tag 01YL.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The geometric preparation for ideal patching, independent of any property of modules.
The positive sum of an ideal pushforward is either zero, or contains an ideal multiple
of the given coherent module, with a bijective generic stalk map.
(Stacks, Tag 01YL). -/
theorem coherent_ideal_patching_generic_embedding
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (ξ : X) (hclosure : closure ({ξ} : Set X) = Set.range i.base)
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hsupport : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base)
    (hkill : ∀ g : X.presheaf.stalk ξ,
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G,
        g ∈ IsLocalRing.maximalIdeal _ → g • m = 0)
    (I : Z.IdealSheafData) :
    ∃ (r : ℕ), 1 ≤ r ∧
      let M := @biproduct (Fin r) X.Modules _ _
        (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
        (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules))
      (IsZero M ∨
        ∃ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf),
          Mono ι ∧ J.IsQuasicoherent ∧
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom ∧
          ∃ (τ : idealModuleProduct ι G ⟶ M), Mono τ ∧
            Function.Bijective
              ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map τ).hom) := by
  obtain ⟨r, hr, h⟩ :=
    coherent_ideal_patching_generic_embedding_core X Z i ξ hclosure G hG hsupport hkill I
  refine ⟨r, hr, ?_⟩
  let M := @biproduct (Fin r) X.Modules _ _
    (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
    (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules))
  change IsZero M ∨ _
  rcases h with hzero | ⟨J, ι, hιmono, hJqc, hιsurj, τ, hτmono, hτsurj⟩
  · exact Or.inl hzero
  · have hbij := coherent_ideal_patching_generic_embedding_stalk_bijective
      X Z i ξ hclosure G hG hsupport hkill I r M J ι τ hτmono hτsurj hιsurj
    exact Or.inr ⟨J, ι, hιmono, hJqc, hιsurj, τ, hτmono, hbij⟩

end AlgebraicGeometry.Scheme.Modules
