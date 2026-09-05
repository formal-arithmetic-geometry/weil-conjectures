/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-!
# The coefficient sheaf of rings on the pro-étale site

For a topological ring `R` and a scheme `Y`, this file constructs the sheaf of rings
`U ↦ C(U, R)` on the small pro-étale site `Y_proét`, and its functoriality in `R`.

This is the coefficient object of the `ℓ`-adic formalism. Two instances matter:

* `R = 𝒪` a complete discrete valuation ring finite over `ℤ_[ℓ]`. Since `𝒪` carries the
  `ℓ`-adic topology, `C(U, 𝒪) = lim_n C(U, 𝒪/ℓⁿ)`, so this really is the *completed*
  coefficient sheaf `lim_n (𝒪/ℓⁿ)_Y` of the reference, and **not** the constant sheaf on
  the discrete ring `𝒪`.
* `R = 𝒪/ℓⁿ` finite discrete, where `C(U, 𝒪/ℓⁿ)` is the usual constant sheaf.

The reduction maps `𝒪 → 𝒪/ℓⁿ` are continuous, so they induce the reduction morphisms of
sheaves of rings via `constRingSheafMap`.

This is the ring-valued analogue of `AlgebraicGeometry.Scheme.ellAdicSheaf`, which is the
special case `R = ℤ_[ℓ]` viewed only as a sheaf of abelian groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ContinuousMap

variable {X R R' : Type*} [TopologicalSpace X] [TopologicalSpace R] [TopologicalSpace R']
  [Ring R] [Ring R'] [IsTopologicalRing R] [IsTopologicalRing R']

/-- Postcomposition with a continuous ring homomorphism, as a ring homomorphism
`C(X, R) →+* C(X, R')`. -/
@[simps]
def postcompRingHom (φ : R →+* R') (hφ : Continuous φ) : C(X, R) →+* C(X, R') where
  toFun g := ⟨fun x ↦ φ (g x), hφ.comp g.continuous⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

end ContinuousMap

namespace AlgebraicGeometry

variable (R R' : Type u) [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
  [TopologicalSpace R'] [Ring R'] [IsTopologicalRing R']

/-- A continuous ring homomorphism `R →+* R'` induces a morphism of presheaves of rings
`U ↦ C(U, R)` on schemes. -/
@[simps]
def continuousMapPresheafRingMap (φ : R →+* R') (hφ : Continuous φ) :
    continuousMapPresheafRing.{u, u} R ⟶ continuousMapPresheafRing.{u, u} R' where
  app _ := RingCat.ofHom (ContinuousMap.postcompRingHom φ hφ)
  naturality _ _ _ := rfl

namespace Scheme.ProEt

variable (Y : Scheme.{u})

/-- The sheaf of rings `U ↦ C(U, R)` on the small pro-étale site of `Y`, for a topological
ring `R`. For `R = 𝒪` complete with the `ℓ`-adic topology this is the completed
coefficient sheaf `lim_n (𝒪/ℓⁿ)_Y`. -/
noncomputable def constRingSheaf : Sheaf (ProEt.topology Y) RingCat.{u} :=
  ((ProEt.forget Y ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafRing.{u, u} R, .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafRing _⟩

/-- A continuous ring homomorphism induces a morphism of coefficient sheaves. In
particular the reductions `𝒪 → 𝒪/ℓⁿ` induce the reduction morphisms of the coefficient
tower. -/
noncomputable def constRingSheafMap (φ : R →+* R') (hφ : Continuous φ) :
    constRingSheaf R Y ⟶ constRingSheaf R' Y :=
  ((ProEt.forget Y ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).map
    ⟨continuousMapPresheafRingMap R R' φ hφ⟩

lemma constRingSheafMap_comp {R'' : Type u} [TopologicalSpace R''] [Ring R'']
    [IsTopologicalRing R''] (φ : R →+* R') (hφ : Continuous φ) (ψ : R' →+* R'')
    (hψ : Continuous ψ) :
    constRingSheafMap R R'' Y (ψ.comp φ) (hψ.comp hφ) =
      constRingSheafMap R R' Y φ hφ ≫ constRingSheafMap R' R'' Y ψ hψ := by
  rw [constRingSheafMap, constRingSheafMap, constRingSheafMap, ← CategoryTheory.Functor.map_comp]
  congr 1

end Scheme.ProEt

end AlgebraicGeometry
