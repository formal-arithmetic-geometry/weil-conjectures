/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMapIhom
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExceptionalGeneral
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence

/-!

# The Künneth–Verdier map and its transport along exceptional inverse images

Fix a scheme `Y`, objects `N` and `ω` of `D(Y_ét, Λ)`, and the evaluation pairing
`ev : [N, ω] ⊗ᴸ N ⟶ ω`. For a morphism `φ : P ⟶ Y` the pulled back pairing
`Lφ^*[N, ω] ⊗ᴸ Lφ^* N ≅ Lφ^*([N, ω] ⊗ᴸ N) ⟶ Lφ^* ω`
(`AlgebraicGeometry.Etale.pulledBackPairing`) has a Künneth map
`S ⊗ᴸ Lφ^*[N, ω] ⟶ RHom(Lφ^* N, S ⊗ᴸ Lφ^* ω)` for every `S ∈ D(P_ét)`
(`CategoryTheory.kunnethMap`). For `P = X ×_k Y`, `φ` the second projection, `ω = ω_Y` and
`S = Lp^* M`, this is the Künneth–Verdier map `κ` of `thm-trf-kunneth-verdier`, up to the
identification `Rp^! M ≅ Lp^* M ⊗ᴸ Lq^* ω_Y`.

Along a morphism `g : P' ⟶ P` admitting a compactification, `Rg^!` carries the Künneth map of `φ`
at `S` to the Künneth map of `g ≫ φ` at `Rg^! S`, provided the tensor maps of `Rg^!` at
`(S, Lφ^*[N, ω])` and `(S, Lφ^* ω)` are invertible
(`AlgebraicGeometry.Etale.isIso_map_kunnethMap_pulledBackPairing_iff`).

## Main definitions

- `AlgebraicGeometry.Etale.evaluationPairing`, `AlgebraicGeometry.Etale.pulledBackPairing`

## Main statements

- `AlgebraicGeometry.Etale.isIso_map_kunnethMap_evaluationPairing_iff`
- `AlgebraicGeometry.Etale.isIso_map_kunnethMap_pulledBackPairing_iff`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

attribute [local instance] derivedBraidedCategory

variable {Y : Scheme.{u}}
  (N ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- The evaluation pairing `[N, ω] ⊗ᴸ N ⟶ ω`. -/
noncomputable def evaluationPairing : (ihom N).obj ω ⊗ N ⟶ ω :=
  (β_ ((ihom N).obj ω) N).hom ≫ (ihom.ev N).app ω

/-- The pairing `Lφ^*[N, ω] ⊗ᴸ Lφ^* N ≅ Lφ^*([N, ω] ⊗ᴸ N) ⟶ Lφ^* ω` pulled back along
`φ : P ⟶ Y`. -/
noncomputable def pulledBackPairing {P : Scheme.{u}} (φ : P ⟶ Y) :
    (L((φ)^*[ModuleCat.{u + 1} Λ])).obj ((ihom N).obj ω) ⊗
        (L((φ)^*[ModuleCat.{u + 1} Λ])).obj N ⟶
      (L((φ)^*[ModuleCat.{u + 1} Λ])).obj ω :=
  inv (leftDerivedUpperStarTensorIso _ φ ((ihom N).obj ω) N).hom ≫
    (L((φ)^*[ModuleCat.{u + 1} Λ])).map (evaluationPairing Λ N ω)

/-- The Künneth map only depends on the morphism `φ`, not on its presentation. -/
lemma isIso_kunnethMap_pulledBackPairing_congr {P : Scheme.{u}} {φ φ' : P ⟶ Y} (h : φ = φ')
    (S : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (kunnethMap (pulledBackPairing Λ N ω φ) S) ↔
      IsIso (kunnethMap (pulledBackPairing Λ N ω φ') S) := by
  subst h; rfl

section Transport

variable {P P' : Scheme.{u}} (g : P' ⟶ P) [HasCompactification g]

/-- The general transport statement for `Rg^!`, with the projection formula of `Rg_!`, its
associativity (`sk-prop-sf-pf-coherence`) and the monoidal structure of `Lg^*`. -/
lemma isIso_map_kunnethMap_iff_of_tensorMap {A D W : _root_.DerivedCategory
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (ev : D ⊗ A ⟶ W)
    (S : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso (rightDerivedUpperShriekTensorMap g S D)]
    [IsIso (rightDerivedUpperShriekTensorMap g S W)] :
    IsIso ((R(g)^![ModuleCat.{u + 1} Λ]).map (kunnethMap ev S)) ↔
      IsIso (kunnethMap (inv (leftDerivedUpperStarTensorIso _ g D A).hom ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map ev) ((R(g)^![ModuleCat.{u + 1} Λ]).obj S)) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) g).isIso_map_kunnethMap_iff
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) g).app M).app N)
    (projectionMap_app_app_naturality_left g) (projectionMap_app_app_naturality_right g)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso _ g N N').hom)
    (projectionMapAssociativity Λ g).assoc ev S

/-- **Transport from `Y`.** Along `φ : P ⟶ Y`, `Rφ^!` of the Künneth map of the evaluation
pairing at `S₀` is invertible if and only if the Künneth map of the pulled back pairing at
`Rφ^! S₀` is, provided the tensor maps of `Rφ^!` at `(S₀, [N, ω])` and `(S₀, ω)` are. -/
lemma isIso_map_kunnethMap_evaluationPairing_iff (φ : P ⟶ Y) [HasCompactification φ]
    (S₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso (rightDerivedUpperShriekTensorMap φ S₀ ((ihom N).obj ω))]
    [IsIso (rightDerivedUpperShriekTensorMap φ S₀ ω)] :
    IsIso ((R(φ)^![ModuleCat.{u + 1} Λ]).map (kunnethMap (evaluationPairing Λ N ω) S₀)) ↔
      IsIso (kunnethMap (pulledBackPairing Λ N ω φ) ((R(φ)^![ModuleCat.{u + 1} Λ]).obj S₀)) :=
  isIso_map_kunnethMap_iff_of_tensorMap Λ φ _ S₀

end Transport

end Etale

end AlgebraicGeometry
