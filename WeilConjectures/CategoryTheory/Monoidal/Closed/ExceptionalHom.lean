/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.VerdierExchange

/-!

# Exceptional internal hom and classes of correspondences for an abstract adjunction

This file continues `WeilConjectures.CategoryTheory.Monoidal.Closed.VerdierExchange`, in the same
abstract setting: `C` (for `D(C)`) and `D` (for `D(Z)`) are braided monoidal closed categories,
`F : D ⥤ C` plays the role of `Lc^*`, `adj' : P ⊣ S` the role of `Rc_! ⊣ Rc^!` and
```
pf : (K, B) ↦ P K ⊗ B ⟶ (K, B) ↦ P (K ⊗ F B)
```
the role of the exceptional projection morphism `PF^!`, for a morphism `c : C ⟶ Z`.

## Main definitions

* `CategoryTheory.Verdier.leftProjection`: the projection morphism with the test object on the
  right, `M ⊗ P T ⟶ P (F M ⊗ T)`, obtained from `pf` by the braidings.
* `CategoryTheory.Verdier.exceptionalHomMap`: the exchange morphism
  `RHom(F M, S N) ⟶ S RHom(M, N)`, i.e. `RHom(c^* M, c^! N) ⟶ c^! RHom(M, N)`.
* `CategoryTheory.Verdier.correspondenceClassEquiv`: the bijection
  `Hom(P 𝟙, RHom(M, N)) ≃ Hom(F M, S N)`, i.e.
  `Hom(Rc_! Λ_C, RHom(M, N)) ≃ Hom(Lc^* M, Rc^! N)`, by tensor–hom adjunction, the projection
  formula and the exceptional adjunction.
* `CategoryTheory.Verdier.homMate`: the mate `𝟙 ⟶ RHom(A, B)` of a morphism `A ⟶ B`.

## Main results

* `CategoryTheory.Verdier.isIso_exceptionalHomMap_of_isIso`: the exchange morphism is an
  isomorphism if the projection morphisms `pf` at `(T, M)` are, by the Yoneda lemma.
* `CategoryTheory.Verdier.homMate_comp_exceptionalHomMap`: the exchange morphism sends the mate
  of `u : F M ⟶ S N` to the exceptional adjoint of its class.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonoidalClosed

namespace CategoryTheory

namespace Verdier

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

section Mate

variable [MonoidalClosed C]

/-- The *mate* `𝟙 ⟶ RHom(A, B)` of a morphism `u : A ⟶ B` in a monoidal closed category: the
transpose of `A ⊗ 𝟙 ≅ A --u--> B` under the tensor–hom adjunction. -/
noncomputable def homMate {A B : C} (u : A ⟶ B) : 𝟙_ C ⟶ (ihom A).obj B :=
  curry ((ρ_ A).hom ≫ u)

lemma uncurry_homMate {A B : C} (u : A ⟶ B) : uncurry (homMate u) = (ρ_ A).hom ≫ u :=
  uncurry_curry _

/-- The mate construction is a bijection `Hom(A, B) ≃ Hom(𝟙, RHom(A, B))`. -/
noncomputable def homMateEquiv (A B : C) : (A ⟶ B) ≃ (𝟙_ C ⟶ (ihom A).obj B) where
  toFun := homMate
  invFun g := (ρ_ A).inv ≫ uncurry g
  left_inv u := by simp [uncurry_homMate]
  right_inv g := by
    apply uncurry_injective
    simp [uncurry_homMate]

end Mate

variable [BraidedCategory C] [BraidedCategory D]
  {F : D ⥤ C} {P : C ⥤ D} {S : D ⥤ C} (adj' : P ⊣ S)
  (pf : curriedTensorInsertFunctor₁ P ⟶
    curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)

section LeftProjection

/-- The projection morphism with the test object on the right, `M ⊗ P T ⟶ P (F M ⊗ T)`, i.e.
`M ⊗ Rc_! T ⟶ Rc_! (Lc^* M ⊗ T)`: the projection morphism `pf` conjugated by the braidings. -/
noncomputable def leftProjection (M : D) (T : C) : M ⊗ P.obj T ⟶ P.obj (F.obj M ⊗ T) :=
  (β_ M (P.obj T)).hom ≫ (pf.app T).app M ≫ P.map (β_ T (F.obj M)).hom

/-- Naturality of `leftProjection` in the test object. -/
@[reassoc]
lemma leftProjection_naturality (M : D) {T T' : C} (u : T ⟶ T') :
    M ◁ P.map u ≫ leftProjection pf M T' = leftProjection pf M T ≫ P.map (F.obj M ◁ u) := by
  have h := congrArg (fun φ ↦ NatTrans.app φ M) (pf.naturality u)
  dsimp at h
  simp only [leftProjection, BraidedCategory.braiding_naturality_right_assoc, Category.assoc]
  rw [reassoc_of% h, ← P.map_comp, ← P.map_comp, BraidedCategory.braiding_naturality_left]

instance isIso_leftProjection (M : D) (T : C) [IsIso ((pf.app T).app M)] :
    IsIso (leftProjection pf M T) := by
  dsimp only [leftProjection]
  infer_instance

end LeftProjection

variable [MonoidalClosed C] [MonoidalClosed D]

section ExceptionalHom

/-- The pairing `M ⊗ P RHom(F M, S N) ⟶ N` whose transpose is the exceptional internal hom
exchange: the projection morphism `leftProjection`, the evaluation
`F M ⊗ RHom(F M, S N) ⟶ S N` and the counit `P S ⟶ 𝟭`. -/
noncomputable def exceptionalHomPairing (M N : D) :
    M ⊗ P.obj ((ihom (F.obj M)).obj (S.obj N)) ⟶ N :=
  leftProjection pf M _ ≫ P.map ((ihom.ev (F.obj M)).app (S.obj N)) ≫ adj'.counit.app N

/-- The **exceptional internal hom exchange** `RHom(F M, S N) ⟶ S RHom(M, N)`, i.e.
`RHom(Lc^* M, Rc^! N) ⟶ Rc^! RHom(M, N)`: the exceptional adjoint of the transpose of
`exceptionalHomPairing`. -/
noncomputable def exceptionalHomMap (M N : D) :
    (ihom (F.obj M)).obj (S.obj N) ⟶ S.obj ((ihom M).obj N) :=
  adj'.homEquiv _ _ (curry (exceptionalHomPairing adj' pf M N))

/-- Composing with the exceptional internal hom exchange, read through the adjunctions, is
precomposition with the projection morphism. -/
lemma exceptionalHomMap_comp_eq {T : C} (M N : D) (u : T ⟶ (ihom (F.obj M)).obj (S.obj N)) :
    u ≫ exceptionalHomMap adj' pf M N = adj'.homEquiv _ _
      (curry (leftProjection pf M T ≫ (adj'.homEquiv _ _).symm (uncurry u))) := by
  rw [exceptionalHomMap, ← Adjunction.homEquiv_naturality_left, ← curry_natural_left,
    exceptionalHomPairing, leftProjection_naturality_assoc, Adjunction.homEquiv_counit,
    uncurry_eq, Functor.map_comp, Category.assoc]

/-- **The exceptional internal hom exchange is an isomorphism** (blueprint
`lem-trf-exceptional-internal-hom-exchange`) as soon as the projection morphisms
`(pf.app T).app M` are, for every `T`: by the Yoneda lemma, composing with it is the chain of
bijections
```
Hom(T, RHom(F M, S N)) ≃ Hom(F M ⊗ T, S N) ≃ Hom(P (F M ⊗ T), N) ≃ Hom(M ⊗ P T, N)
  ≃ Hom(P T, RHom(M, N)) ≃ Hom(T, S RHom(M, N)),
```
the third one being precomposition with the isomorphism `leftProjection`. -/
theorem isIso_exceptionalHomMap_of_isIso (M N : D) [∀ T, IsIso ((pf.app T).app M)] :
    IsIso (exceptionalHomMap adj' pf M N) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  have e : (fun u : T ⟶ (ihom (F.obj M)).obj (S.obj N) ↦ u ≫ exceptionalHomMap adj' pf M N) =
      adj'.homEquiv _ _ ∘ curry ∘ (fun x ↦ leftProjection pf M T ≫ x) ∘
        (adj'.homEquiv _ _).symm ∘ uncurry := by
    funext u
    exact exceptionalHomMap_comp_eq adj' pf M N u
  rw [e]
  refine (Equiv.bijective _).comp (Function.Bijective.comp
    ⟨curry_injective, fun g ↦ ⟨uncurry g, curry_uncurry g⟩⟩
    (Function.Bijective.comp ⟨fun a b h ↦ (cancel_epi (leftProjection pf M T)).1 h,
      fun y ↦ ⟨inv (leftProjection pf M T) ≫ y, by simp⟩⟩ ((Equiv.bijective _).comp
        ⟨uncurry_injective, fun g ↦ ⟨curry g, uncurry_curry g⟩⟩)))

end ExceptionalHom

section CorrespondenceClass

/-- The bijection `Hom(P 𝟙, RHom(M, N)) ≃ Hom(F M, S N)`, i.e.
`Hom(Rc_! Λ_C, RHom(M, N)) ≃ Hom(Lc^* M, Rc^! N)`: the tensor–hom adjunction, the inverse of the
projection morphism `M ⊗ P 𝟙 ≅ P (F M ⊗ 𝟙)`, the right unitor and the exceptional adjunction
(blueprint `lem-trf-correspondence-class`). -/
noncomputable def correspondenceClassEquiv (M N : D) [IsIso ((pf.app (𝟙_ C)).app M)] :
    (P.obj (𝟙_ C) ⟶ (ihom M).obj N) ≃ (F.obj M ⟶ S.obj N) :=
  ((ihom.adjunction M).homEquiv _ _).symm.trans
    (((asIso (leftProjection pf M (𝟙_ C))).trans (P.mapIso (ρ_ (F.obj M)))).homCongr
      (Iso.refl N) |>.trans (adj'.homEquiv _ _))

omit [MonoidalClosed C] in
lemma correspondenceClassEquiv_apply (M N : D) [IsIso ((pf.app (𝟙_ C)).app M)]
    (g : P.obj (𝟙_ C) ⟶ (ihom M).obj N) :
    correspondenceClassEquiv adj' pf M N g = adj'.homEquiv _ _
      (P.map (ρ_ (F.obj M)).inv ≫ inv (leftProjection pf M (𝟙_ C)) ≫ uncurry g) := by
  simp [correspondenceClassEquiv, Iso.homCongr_apply, uncurry_eq]
  rfl

/-- **The exchange of the mate is the adjoint of the class** (blueprint
`lem-trf-trace-class-diagonal-pairing`, Step 1): for `u : F M ⟶ S N` with class
`[u] = correspondenceClassEquiv.symm u`, the exceptional internal hom exchange sends the mate
`𝟙 ⟶ RHom(F M, S N)` of `u` to the exceptional adjoint `𝟙 ⟶ S RHom(M, N)` of `[u]`. -/
theorem homMate_comp_exceptionalHomMap (M N : D) [IsIso ((pf.app (𝟙_ C)).app M)]
    (u : F.obj M ⟶ S.obj N) :
    homMate u ≫ exceptionalHomMap adj' pf M N =
      adj'.homEquiv _ _ ((correspondenceClassEquiv adj' pf M N).symm u) := by
  rw [exceptionalHomMap_comp_eq]
  congr 1
  apply (correspondenceClassEquiv adj' pf M N).injective
  rw [Equiv.apply_symm_apply, correspondenceClassEquiv_apply, uncurry_curry,
    IsIso.inv_hom_id_assoc, uncurry_homMate, Adjunction.homEquiv_counit, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_assoc, ← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]

end CorrespondenceClass

end Verdier

end CategoryTheory
