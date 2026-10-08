/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.CommShift
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Basic

/-!
# The Poincaré pairing of a pair of adjunctions

Let `C` and `D` be monoidal categories with shifts by `ℤ`, and consider the formal data of a
six-functor formalism attached to a morphism `a : X ⟶ Y`, with `C = D(X)` and `D = D(Y)`:

* an adjunction `adj : P ⊣ G` (in the example `La^* ⊣ Ra_*`),
* an adjunction `adj' : F ⊣ F'` (in the example `Ra_! ⊣ Ra^!`), with `F` commuting with shifts,
* for an object `K` of `C`, a projection map `pf : F K ⊗ - ⟶ F (K ⊗ P -)`,
* an object `T` of `C` and an isomorphism `γ : T⟦n⟧ ≅ F' 𝟙` (an orientation).

The *mixed cup product* `CategoryTheory.Adjunction.mixedCupProduct` is
`F K ⊗ G L ⟶ F (K ⊗ P G L) ⟶ F (K ⊗ L)`, and the *Poincaré pairing*
`CategoryTheory.Adjunction.poincarePairing` is the composite
```
F K ⊗ (G (K^∨ ⊗ T))⟦n⟧ ≅ (F K ⊗ G (K^∨ ⊗ T))⟦n⟧ ⟶ (F (K ⊗ (K^∨ ⊗ T)))⟦n⟧ ⟶ (F T)⟦n⟧
    ≅ F (T⟦n⟧) ≅ F (F' 𝟙) ⟶ 𝟙
```
of the mixed cup product, the twisted evaluation `K ⊗ (K^∨ ⊗ T) ⟶ T`
(`CategoryTheory.MonoidalClosed.twistedEvaluation`, with `K^∨ = [K, 𝟙]`), the orientation and
the counit of `adj'`.

## Main statements

- `CategoryTheory.Adjunction.isPerfectPairing_poincarePairing`: if `K` has a left dual and the
  projection map is an isomorphism, then the Poincaré pairing is perfect: its adjoint
  `(G (K^∨ ⊗ T))⟦n⟧ ⟶ [F K, 𝟙]` is an isomorphism.

The proof is the Yoneda argument of the blueprint: for every test object `Z`, maps
`Z⟦n⟧ ⟶ (G (K^∨ ⊗ T))⟦n⟧` correspond successively to maps `P Z ⟶ K^∨ ⊗ T` (adjunction
`P ⊣ G`), `K ⊗ P Z ⟶ T` (duality of `K`), `(K ⊗ P Z)⟦n⟧ ⟶ F' 𝟙` (orientation),
`F ((K ⊗ P Z)⟦n⟧) ⟶ 𝟙` (adjunction `F ⊣ F'`) and `(F K ⊗ Z)⟦n⟧ ⟶ 𝟙` (projection formula), and
the composite bijection is composition with the pairing.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory MonoidalClosed

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {P : D ⥤ C} {G : C ⥤ D} (adj : P ⊣ G) (F : C ⥤ D) {K : C}
  (pf : tensorLeft (F.obj K) ⟶ P ⋙ tensorLeft K ⋙ F)

/-- The *mixed cup product* `F K ⊗ G L ⟶ F (K ⊗ L)` attached to an adjunction `adj : P ⊣ G`
and a projection map `pf : F K ⊗ - ⟶ F (K ⊗ P -)`: the projection map followed by `F` of
`K ◁ ε_L`, for the counit `ε_L : P (G L) ⟶ L`. -/
noncomputable def mixedCupProduct (L : C) : F.obj K ⊗ G.obj L ⟶ F.obj (K ⊗ L) :=
  pf.app (G.obj L) ≫ F.map (K ◁ adj.counit.app L)

/-- The mixed cup product after `F K ◁ t`, for `t : Z ⟶ G L`, is the projection map at `Z`
followed by `F` of `K ◁ t♭`, for the adjoint `t♭ : P Z ⟶ L` of `t`:
```
              F K ◁ t                    mixedCupProduct
F K ⊗ Z ─────────────▶ F K ⊗ G L ───────────────▶ F (K ⊗ L)
   │                                                  ‖
   │ pf_Z                       F (K ◁ t♭)            ‖
   └──────────▶ F (K ⊗ P Z) ─────────────────────▶ F (K ⊗ L)
``` -/
@[reassoc]
lemma whiskerLeft_comp_mixedCupProduct {L : C} {Z : D} (t : Z ⟶ G.obj L) :
    F.obj K ◁ t ≫ adj.mixedCupProduct F pf L =
      pf.app Z ≫ F.map (K ◁ (adj.homEquiv _ _).symm t) := by
  have h := pf.naturality t
  dsimp at h
  rw [mixedCupProduct, reassoc_of% h, homEquiv_counit, MonoidalCategory.whiskerLeft_comp,
    Functor.map_comp]

variable [MonoidalClosed C] [HasShift C ℤ] [HasShift D ℤ] [F.CommShift ℤ]
  [(tensorLeft (F.obj K)).CommShift ℤ] {F' : D ⥤ C} (adj' : F ⊣ F') (n : ℤ) (T : C)
  (γ : T⟦n⟧ ≅ F'.obj (𝟙_ D))

/-- The *Poincaré pairing* `F K ⊗ (G (K^∨ ⊗ T))⟦n⟧ ⟶ 𝟙`, where `K^∨ = [K, 𝟙]`: the shift is
moved out of the tensor product, then come the mixed cup product, `F` of the twisted
evaluation, the shift compatibility of `F`, the orientation `γ` and the counit of
`adj' : F ⊣ F'`. -/
noncomputable def poincarePairing :
    F.obj K ⊗ (G.obj ((ihom K).obj (𝟙_ C) ⊗ T))⟦n⟧ ⟶ 𝟙_ D :=
  ((tensorLeft (F.obj K)).commShiftIso n).hom.app _ ≫
    (adj.mixedCupProduct F pf _ ≫ F.map (twistedEvaluation K T))⟦n⟧' ≫
      (F.commShiftIso n).inv.app T ≫ F.map γ.hom ≫ adj'.counit.app (𝟙_ D)

/-- The Poincaré pairing after `F K ◁ t⟦n⟧`, for `t : Z ⟶ G (K^∨ ⊗ T)`, is the shifted
projection map at `Z` followed by the `adj'`-adjoint of the shifted twisted evaluation of the
`adj`-adjoint `t♭ : P Z ⟶ K^∨ ⊗ T` of `t`, composed with the orientation `γ`:
```
                 F K ◁ t⟦n⟧                                   poincarePairing
F K ⊗ Z⟦n⟧ ───────────▶ F K ⊗ (G (K^∨ ⊗ T))⟦n⟧ ──────────────────▶ 𝟙
    │ ≅                                                                ‖
    ▼            (pf_Z)⟦n⟧                    ≅              (adj'-adjoint of g)
(F K ⊗ Z)⟦n⟧ ─────────▶ (F (K ⊗ P Z))⟦n⟧ ─────▶ F ((K ⊗ P Z)⟦n⟧) ─────────────▶ 𝟙
```
where `g = (K ◁ t♭ ≫ twistedEvaluation K T)⟦n⟧ ≫ γ : (K ⊗ P Z)⟦n⟧ ⟶ F' 𝟙`. -/
lemma whiskerLeft_shift_comp_poincarePairing {Z : D}
    (t : Z ⟶ G.obj ((ihom K).obj (𝟙_ C) ⊗ T)) :
    F.obj K ◁ t⟦n⟧' ≫ adj.poincarePairing F pf adj' n T γ =
      ((tensorLeft (F.obj K)).commShiftIso n).hom.app Z ≫ (pf.app Z)⟦n⟧' ≫
        (F.commShiftIso n).inv.app _ ≫ (adj'.homEquiv _ _).symm
          ((K ◁ (adj.homEquiv _ _).symm t ≫ twistedEvaluation K T)⟦n⟧' ≫ γ.hom) := by
  have h := ((tensorLeft (F.obj K)).commShiftIso n).hom.naturality t
  dsimp at h
  rw [poincarePairing, reassoc_of% h, homEquiv_counit]
  simp only [← Functor.map_comp_assoc, whiskerLeft_comp_mixedCupProduct_assoc]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_inv_naturality_assoc]

/-- **The Poincaré pairing is perfect.** If `K` has a left dual `L` and the projection map
`pf` is an isomorphism, the Poincaré pairing `F K ⊗ (G (K^∨ ⊗ T))⟦n⟧ ⟶ 𝟙` is perfect. -/
theorem isPerfectPairing_poincarePairing [MonoidalClosed D] (L : C) [ExactPairing L K]
    (hpf : ∀ Z, IsIso (pf.app Z)) :
    IsPerfectPairing (adj.poincarePairing F pf adj' n T γ) := by
  refine ⟨isIso_of_bijective_shift_comp _ n fun Z ↦ ?_⟩
  have e₁ : (fun t : Z⟦n⟧ ⟶ _ ↦ t ≫ curry (adj.poincarePairing F pf adj' n T γ)) =
      (ihom.adjunction _).homEquiv _ _ ∘
        (fun t ↦ F.obj K ◁ t ≫ adj.poincarePairing F pf adj' n T γ) := by
    ext t
    rw [Function.comp_apply, MonoidalClosed.homEquiv_apply_eq, curry_natural_left]
  rw [e₁]
  refine ((ihom.adjunction _).homEquiv _ _).bijective.comp ?_
  rw [← Function.Bijective.of_comp_iff _
    ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D n)).map_bijective Z
      (G.obj ((ihom K).obj (𝟙_ C) ⊗ T)))]
  have := hpf Z
  let I := ((tensorLeft (F.obj K)).commShiftIso n).app Z ≪≫ (shiftFunctor D n).mapIso
    (asIso (pf.app Z)) ≪≫ ((F.commShiftIso n).app _).symm
  have e₂ : (fun t ↦ F.obj K ◁ t ≫ adj.poincarePairing F pf adj' n T γ) ∘
      (fun t ↦ (shiftFunctor D n).map t) =
      (fun f ↦ I.hom ≫ f) ∘ (fun h ↦ (adj'.homEquiv _ (𝟙_ D)).symm h) ∘
        (fun g : (K ⊗ P.obj Z)⟦n⟧ ⟶ T⟦n⟧ ↦ g ≫ γ.hom) ∘
          (fun g : K ⊗ P.obj Z ⟶ T ↦ (shiftFunctor C n).map g) ∘
            (fun s ↦ K ◁ s ≫ twistedEvaluation K T) ∘
              (fun t : Z ⟶ G.obj ((ihom K).obj (𝟙_ C) ⊗ T) ↦ (adj.homEquiv _ _).symm t) := by
    ext t
    simp [whiskerLeft_shift_comp_poincarePairing, I]
  rw [e₂]
  exact I.symm.homFromEquiv.bijective.comp ((adj'.homEquiv _ _).symm.bijective.comp
    (γ.homToEquiv.bijective.comp
      (((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C n)).map_bijective _ _).comp
        ((bijective_whiskerLeft_comp_twistedEvaluation L K _ T).comp
          (adj.homEquiv _ _).symm.bijective))))

end Adjunction

end CategoryTheory
