/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic

/-! # A representation limit with prescribed underlying projections

The equivariance of normalized module projections lifts an underlying module limit
to a representation limit. (blueprint: new-e7-normalized-representation-limit-cone).
-/

@[expose] public section

set_option autoImplicit false
universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace Rep

/-- Equivariant normalized projections give the prescribed representation as a limit.
Source: the integral inverse-limit construction in Weil II (1.1.1) b), (1.1.6), and
Stanford Weil II seminar L19, Proposition 1.1.9.
(blueprint: new-e7-normalized-representation-limit-cone).

The maps obtained by the fibre isomorphism, the module limit projections and the
inverse diagram comparison are equivariant by hypothesis.  Regard them as
representation morphisms.  Naturality of the diagram comparison proves the cone
identities.  After forgetting the action and postcomposing with the comparison,
this cone is isomorphic to the module limit cone.  Forgetting representations
reflects limits, so the cone is limiting.  Its vertex is already the required
representation; the identity isomorphism gives exactly the normalized projections. -/
theorem normalized_limit_cone
    {R : Type u} [CommRing R] {G : Type v} [Monoid G]
    (V : ℕᵒᵖ ⥤ Rep.{w} R G) (D : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (α : V ⋙ forget₂ (Rep R G) (ModuleCat R) ≅ D)
    (W : Rep.{w} R G)
    (τ : (forget₂ (Rep R G) (ModuleCat R)).obj W ≅ limit D)
    (h : ∀ (n : ℕ) (g : G) (z : W.V),
      α.inv.app (op n) ((τ.hom ≫ limit.π D (op n)) (W.ρ g z)) =
        (V.obj (op n)).ρ g (α.inv.app (op n) ((τ.hom ≫ limit.π D (op n)) z))) :
    ∃ C : Cone V, ∃ e : C.pt ≅ W, Nonempty (IsLimit C) ∧
      ∀ n : ℕ, (forget₂ (Rep R G) (ModuleCat R)).map
        (e.inv ≫ C.π.app (op n)) ≫ α.hom.app (op n) = τ.hom ≫ limit.π D (op n) := by
  let U := forget₂ (Rep.{w} R G) (ModuleCat.{w} R)
  let q (j : ℕᵒᵖ) : U.obj W ⟶ U.obj (V.obj j) :=
    τ.hom ≫ limit.π D j ≫ α.inv.app j
  have hq (j : ℕᵒᵖ) (g : G) (z : W.V) :
      q j (W.ρ g z) = (V.obj j).ρ g (q j z) := h j.unop g z
  let p (j : ℕᵒᵖ) : W ⟶ V.obj j :=
    Rep.ofHom
      { toLinearMap := (q j).hom
        isIntertwining' := fun g ↦ LinearMap.ext (hq j g) }
  have hp (j : ℕᵒᵖ) : U.map (p j) = q j := rfl
  let C : Cone V :=
    { pt := W
      π :=
        { app := p
          naturality := by
            intro j k f
            apply U.map_injective
            change U.map (𝟙 W ≫ p k) = U.map (p j ≫ V.map f)
            simp only [Category.id_comp, Functor.map_comp, hp]
            symm
            have hn : D.map f ≫ α.inv.app k = α.inv.app j ≫ U.map (V.map f) :=
              α.inv.naturality f
            dsimp [q]
            rw [Category.assoc, Category.assoc, ← hn]
            simp only [← Category.assoc, limit.w] } }
  have he : (Cone.postcompose α.hom).obj (U.mapCone C) ≅ limit.cone D :=
    Cone.ext τ (by
      intro j
      change q j ≫ α.hom.app j = τ.hom ≫ limit.π D j
      simp [q])
  have hc : IsLimit (U.mapCone C) :=
    (IsLimit.postcomposeHomEquiv α _)
      ((limit.isLimit D).ofIsoLimit he.symm)
  let : ReflectsLimitsOfSize.{0, 0} U := reflectsSmallestLimits_of_reflectsLimits U
  refine ⟨C, Iso.refl W, ⟨isLimitOfReflects U hc⟩, ?_⟩
  intro n
  change U.map (𝟙 W ≫ p (op n)) ≫ α.hom.app (op n) = _
  simp only [Category.id_comp, hp]
  simp [q]

end Rep
