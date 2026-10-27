/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback

/-!

# The Künneth map of nearby cycles and retracts

Let `ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P` be morphisms of models compatible with
`φ₁ : P ⟶ M`, `φ₂ : P ⟶ N` and `φ₁' : P' ⟶ M'`, `φ₂' : P' ⟶ N'`. The pullback of the Künneth
map `Lρ'^* Π_{A,B}` and the Künneth map `Π' = Π_{Lρ_M^* A, Lρ_N^* B}` fit into the square of
`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`, whose vertical maps are built from the
pullback exchanges `α_{ρ_M}`, `α_{ρ_N}`, `α_{ρ_P}`.

When the exchanges are not invertible, but `α_{ρ_N}` is and `α_{ρ_M}`, `α_{ρ_P}` are split
monomorphisms whose retractions are compatible with `Π'`, the map `Lρ'^* Π_{A,B}` is still a
retract of `Π'`, hence invertible if `Π'` is
(`NearbyCyclesModel.isIso_map_kunnethMap_of_isKunnethRetract`). This is the shape of the
generic-slicing step of Gabber's Künneth formula (blueprint `sk-prop-tf-nearby-external-kunneth`,
"Finite support"): there `α_{ρ_M}` and `α_{ρ_P}` are the inclusions of the invariants under a
pro-`p` group `P` acting trivially on the nearby cycles of `N'`, the retractions are the averaging
projections, and their compatibility with `Π'` is the projection formula for invariants (blueprint
`det-nearby-kunneth-invariants`).

## Main statements

* `CategoryTheory.isIso_of_comp_eq_tensorHom_of_retraction`: the abstract retract argument.
* `NearbyCyclesModel.IsKunnethRetract`: the retraction data.
* `NearbyCyclesModel.isIso_map_kunnethMap_of_isKunnethRetract`: the pullback of the Künneth map
  is invertible if `Π'` and `α_{ρ_N}` are and the retraction data exist.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- **A retract of an isomorphism along split monomorphisms**: if `x ≫ a = w ≫ π` with `π`
invertible, `a` and `w` split monomorphisms with retractions `ρ`, `w'`, and the idempotents are
compatible with `π` (`w' ≫ w ≫ π = π ≫ ρ ≫ a`), then `x` is invertible, with inverse
`a ≫ π⁻¹ ≫ w'`. -/
lemma isIso_of_comp_eq_of_retraction {C : Type*} [Category C] {U V U' V' : C} {x : U ⟶ V}
    {a : V ⟶ V'} {w : U ⟶ U'} {π : U' ⟶ V'} [IsIso π] {ρ : V' ⟶ V} {w' : U' ⟶ U}
    (ha : a ≫ ρ = 𝟙 V) (hw : w ≫ w' = 𝟙 U) (hsq : x ≫ a = w ≫ π)
    (hc : w' ≫ w ≫ π = π ≫ ρ ≫ a) : IsIso x := by
  have hx : x = w ≫ π ≫ ρ := by rw [← reassoc_of% hsq, ha, Category.comp_id]
  refine ⟨a ≫ inv π ≫ w', ?_, ?_⟩
  · rw [reassoc_of% hsq, IsIso.hom_inv_id_assoc, hw]
  · rw [hx, Category.assoc, Category.assoc, reassoc_of% hc, IsIso.inv_hom_id_assoc,
      reassoc_of% ha, ha]

/-- A *retract structure* on a commutative square `x ≫ a = δ ≫ t ≫ π`: retractions `t'` of `t`
and `ρ` of `a` such that `π` carries the idempotent `t' ≫ t` to the idempotent `ρ ≫ a`. -/
def IsSquareRetract {C : Type*} {_ : Category C} {U V V' S T : C} {x : U ⟶ V} {a : V ⟶ V'}
    {δ : U ⟶ S} {t : S ⟶ T} {π : T ⟶ V'} (_ : x ≫ a = δ ≫ t ≫ π) : Prop :=
  ∃ (t' : T ⟶ S) (ρ : V' ⟶ V), t ≫ t' = 𝟙 S ∧ a ≫ ρ = 𝟙 V ∧ t' ≫ t ≫ π = π ≫ ρ ≫ a

/-- **A retract of an isomorphism along an isomorphism is an isomorphism**: given a retract
structure on `x ≫ a = δ ≫ t ≫ π` with `δ` and `π` invertible, `x` is invertible. -/
lemma IsSquareRetract.isIso {C : Type*} {_ : Category C} {U V V' S T : C} {x : U ⟶ V}
    {a : V ⟶ V'} {δ : U ⟶ S} [IsIso δ] {t : S ⟶ T} {π : T ⟶ V'} [IsIso π]
    {hsq : x ≫ a = δ ≫ t ≫ π} (h : IsSquareRetract hsq) : IsIso x := by
  obtain ⟨t', ρ, ht, ha, hc⟩ := h
  refine isIso_of_comp_eq_of_retraction (w := δ ≫ t) (w' := t' ≫ inv δ) ha ?_
    (by rw [hsq, Category.assoc]) ?_
  · rw [Category.assoc, reassoc_of% ht, IsIso.hom_inv_id]
  · rw [Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hc]

/-- A *tensor retract structure* on a commutative square `x ≫ a = δ ≫ (u₁ ⊗ u₂) ≫ π`: retractions
`r₁` of `u₁` and `ρ` of `a` such that `π` carries the idempotent `(r₁ ≫ u₁) ⊗ 𝟙` to the idempotent
`ρ ≫ a`. -/
def IsTensorRetract {C : Type*} {_ : Category C} {_ : MonoidalCategory C}
    {U V V' S₁ S₂ T₁ T₂ : C} {x : U ⟶ V} {a : V ⟶ V'} {δ : U ⟶ S₁ ⊗ S₂} {u₁ : S₁ ⟶ T₁}
    {u₂ : S₂ ⟶ T₂} {π : T₁ ⊗ T₂ ⟶ V'} (_ : x ≫ a = δ ≫ (u₁ ⊗ₘ u₂) ≫ π) : Prop :=
  ∃ (r₁ : T₁ ⟶ S₁) (ρ : V' ⟶ V), u₁ ≫ r₁ = 𝟙 S₁ ∧ a ≫ ρ = 𝟙 V ∧
    ((r₁ ≫ u₁) ▷ T₂) ≫ π = π ≫ ρ ≫ a

/-- A tensor retract structure with `u₂` invertible gives a retract structure, with the retraction
`r₁ ⊗ u₂⁻¹` of `u₁ ⊗ u₂`. -/
lemma IsTensorRetract.isSquareRetract {C : Type*} {_ : Category C} {_ : MonoidalCategory C}
    {U V V' S₁ S₂ T₁ T₂ : C} {x : U ⟶ V} {a : V ⟶ V'} {δ : U ⟶ S₁ ⊗ S₂} {u₁ : S₁ ⟶ T₁}
    {u₂ : S₂ ⟶ T₂} [IsIso u₂] {π : T₁ ⊗ T₂ ⟶ V'} {hsq : x ≫ a = δ ≫ (u₁ ⊗ₘ u₂) ≫ π}
    (h : IsTensorRetract hsq) : IsSquareRetract hsq := by
  obtain ⟨r₁, ρ, hr₁, ha, hc⟩ := h
  refine ⟨r₁ ⊗ₘ inv u₂, ρ, ?_, ha, ?_⟩
  · rw [tensorHom_comp_tensorHom, hr₁, IsIso.hom_inv_id, tensorHom_id, id_whiskerRight]
  · rw [← Category.assoc, tensorHom_comp_tensorHom, IsIso.inv_hom_id, tensorHom_id, hc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

set_option maxHeartbeats 800000 in
-- the Künneth maps of the two products are large terms
/-- **The pullback of the Künneth map is a retract of the Künneth map of the pullback models**:
for morphisms of models `ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P` compatible with
`φ₁`, `φ₂` and `φ₁'`, `φ₂'`, consider the square of the Künneth maps and pullbacks
(`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`)
```
Lρ'^* Π_{A,B} ≫ a = δ ≫ (u_M ⊗ u_N) ≫ Π',
```
where `a` is the pullback exchange `α_{ρ_P}(A ⊠ B)` followed by the tensor and pullback
comparison, `u_M`, `u_N` are the pullback exchanges `α_{ρ_M}(A)`, `α_{ρ_N}(B)` preceded by the
pullback comparisons, `δ` is the monoidal structure of `Lρ'^*` and `Π' = Π_{Lρ_M^* A, Lρ_N^* B}`
is the Künneth map of the pullback models. If `u_M ⊗ u_N` and `a` admit retractions whose
idempotents are compatible with `Π'` (`CategoryTheory.IsSquareRetract`), then `Lρ'^* Π_{A,B}` is
invertible as soon as `Π'` is. -/
theorem isIso_map_kunnethMap_of_isSquareRetract (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂')
    (ρM : MU.Hom M r₁ r₁') (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hR : IsSquareRetract (map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP htot₁
      hgen₁ htot₂ hgen₂ hb₁ hs₁ hb₂ hs₂ A B))
    [IsIso (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))] :
    IsIso (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) :=
  hR.isIso

set_option maxHeartbeats 800000 in
-- the Künneth maps of the two products are large terms
/-- **The pullback of the Künneth map is a retract of the Künneth map of the pullback models**,
tensor form: in the square of `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`, if the
pullback exchange `α_{ρ_N}(B)` is invertible and `u_M` and `a` admit retractions whose idempotents
are compatible with `Π'` (`CategoryTheory.IsTensorRetract`), then `Lρ'^* Π_{A,B}` is invertible as
soon as `Π'` is. -/
theorem isIso_map_kunnethMap_of_isTensorRetract (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂')
    (ρM : MU.Hom M r₁ r₁') (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hN : IsIso ((ρN.pullbackExchange Λ).app B))
    (hR : IsTensorRetract (map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP htot₁
      hgen₁ htot₂ hgen₂ hb₁ hs₁ hb₂ hs₂ A B))
    (hK : IsIso (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))) :
    IsIso (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) :=
  hR.isSquareRetract.isIso

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
