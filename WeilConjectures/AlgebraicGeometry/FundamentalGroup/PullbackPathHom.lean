/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport

/-!
# The map of fundamental groups induced by a morphism, on automorphisms of fibre functors

A morphism `f : X ⟶ Y` carries a path `τ : F_y ≅ F_z` between fibre functors on `FÉt(X)` to the
path `F_{y ≫ f} ≅ F_{z ≫ f}` on `FÉt(Y)` (`AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathIso`).
On loops this is a group homomorphism `π₁(X, y) = Aut F_y → Aut F_{y ≫ f} = π₁(Y, y ≫ f)`
(`AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathHom`). If the base change of a finite étale
`Y`-scheme `P` along `f` is connected, the image of this homomorphism acts transitively on the
fibre of `P` at `y ≫ f` (`AlgebraicGeometry.Scheme.FiniteEtale.exists_pullbackPathHom_apply_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The homomorphism `Aut F_y → Aut F_{y ≫ f}` of automorphism groups of fibre functors induced
by a morphism `f : X ⟶ Y`, through base change of finite étale schemes along `f`. -/
noncomputable def pullbackPathHom (f : X ⟶ Y) (y : Spec (.of Ω) ⟶ X) :
    Aut (fiber y) →* Aut (fiber (y ≫ f)) where
  toFun τ := pullbackPathIso f τ
  map_one' := pullbackPathIso_refl f y
  map_mul' τ τ' := by
    rw [Aut.Aut_mul_def, Aut.Aut_mul_def, pullbackPathIso_trans]

lemma pullbackPathHom_apply (f : X ⟶ Y) (y : Spec (.of Ω) ⟶ X) (τ : Aut (fiber y)) :
    pullbackPathHom f y τ = pullbackPathIso f τ :=
  rfl

/-- If the base change `P ×_Y X` of a finite étale `Y`-scheme along `f : X ⟶ Y` is connected, the
automorphisms of the fibre functor at `y` act transitively on the fibre of `P` at `y ≫ f`, through
`pullbackPathHom`. -/
lemma exists_pullbackPathHom_apply_eq [ConnectedSpace X] (f : X ⟶ Y) (y : Spec (.of Ω) ⟶ X)
    (P : Y.FiniteEtale) [IsConnected ((pullback f).obj P)] (a b : (fiber (y ≫ f)).obj P) :
    ∃ τ : Aut (fiber y), (pullbackPathHom f y τ).hom.app P a = b := by
  have key (a' : (fiber y).obj ((pullback f).obj P)) :
      ∃ τ : Aut (fiber y), τ.hom.app _ a' = (pullbackFiberIso f y).inv.app P b :=
    MulAction.exists_smul_eq _ a' _
  obtain ⟨τ, hτ⟩ := key ((pullbackFiberIso f y).inv.app P a)
  refine ⟨τ, ?_⟩
  have h : (pullbackPathHom f y τ).hom.app P a = (pullbackFiberIso f y).hom.app P
      (τ.hom.app _ ((pullbackFiberIso f y).inv.app P a)) := rfl
  rw [h, hτ]
  exact ConcreteCategory.congr_hom ((pullbackFiberIso f y).inv_hom_id_app P) b

end AlgebraicGeometry.Scheme.FiniteEtale
