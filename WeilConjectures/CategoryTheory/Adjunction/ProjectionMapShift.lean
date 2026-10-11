/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# Projection maps commute with shifts

Let `adj : F ⊣ G` be an adjunction compatible with shifts. If a comparison
`φ : F (T_D a b) ⟶ T_C (F a) (F b)` commutes with the shifts in the variable `a`, then the
right adjoint projection map `T_D (G M) L ⟶ G (T_C M (F L))` commutes with the shifts in the
variable `M` (`CategoryTheory.Adjunction.commShift_rightAdjointProjectionMapFlipApp`).
Dually, for `adj : F ⊣ G` and a comparison `δ : T (G X) (G' M) ⟶ G (T' X M)` commuting with the
shifts in `X`, the projection map `F (T K (G' M)) ⟶ T' (F K) M` commutes with the shifts in the
variable `K` (`CategoryTheory.Adjunction.commShift_projectionMapFlipApp`).

These lemmas are groundwork for the compatibility of global Verdier duality with shifts
(blueprint `sk-thm-sf-global-duality`), which is not formalised yet; nothing uses them so far.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

/-- The comparison `φ : F (T_D a L) ⟶ T_C (F a) (F L)` for a fixed `L`, as a natural
transformation of functors of `a`. -/
@[simps]
def comparisonFlipApp (L : D) : T_D.flip.obj L ⋙ F ⟶ F ⋙ T_C.flip.obj (F.obj L) where
  app a := (φ.app a).app L
  naturality a a' f := by
    have := NatTrans.congr_app (φ.naturality f) L
    dsimp at this ⊢
    exact this

/-- The right adjoint projection map `T_D (G M) L ⟶ G (T_C M (F L))` for a fixed `L`, as a
natural transformation of functors of `M`. -/
@[simps]
def rightAdjointProjectionMapFlipApp (L : D) :
    G ⋙ T_D.flip.obj L ⟶ T_C.flip.obj (F.obj L) ⋙ G where
  app M := ((adj.rightAdjointProjectionMap φ).app M).app L
  naturality M M' f := by
    simpa using NatTrans.congr_app ((adj.rightAdjointProjectionMap φ).naturality f) L

/-- The right adjoint projection map for a fixed `L`, written as a composite of the whiskered
unit, the comparison `φ` and the whiskered counit. -/
lemma rightAdjointProjectionMapFlipApp_eq (L : D) :
    adj.rightAdjointProjectionMapFlipApp φ L =
      (Functor.rightUnitor _).inv ≫ whiskerLeft (G ⋙ T_D.flip.obj L) adj.unit ≫
        (Functor.associator (G ⋙ T_D.flip.obj L) F G).inv ≫
        whiskerRight (Functor.associator G (T_D.flip.obj L) F).hom G ≫
        whiskerRight (whiskerLeft G (comparisonFlipApp φ L) ≫
          (Functor.associator G F (T_C.flip.obj (F.obj L))).inv ≫
          whiskerRight adj.counit (T_C.flip.obj (F.obj L)) ≫
          (Functor.leftUnitor _).hom) G := by
  ext M
  simp [rightAdjointProjectionMap_app_app, homEquiv_unit]

variable (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [F.CommShift A] [G.CommShift A]
  [adj.CommShift A] [∀ L : D, (T_D.flip.obj L).CommShift A]
  [∀ X : C, (T_C.flip.obj X).CommShift A]

/-- If `φ` commutes with the shifts in its first variable, so does the right adjoint projection
map: for every `a : A` the square in `D`
```
T_D ((G M)⟦a⟧) L ─────────▶ G (T_C (M⟦a⟧) (F L))
        │                              │
        ▼                              ▼
(T_D (G M) L)⟦a⟧ ─────────▶ (G (T_C M (F L)))⟦a⟧
```
commutes, where the horizontal maps are projection maps and the vertical maps are built from
the shift isomorphisms. -/
lemma commShift_rightAdjointProjectionMapFlipApp (L : D)
    [NatTrans.CommShift (comparisonFlipApp φ L) A] :
    NatTrans.CommShift (adj.rightAdjointProjectionMapFlipApp φ L) A := by
  rw [rightAdjointProjectionMapFlipApp_eq]
  infer_instance

section LeftAdjoint

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (G' : D ⥤ C) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
  (δ : (((Functor.whiskeringLeft₂ C).obj G).obj G').obj T ⟶
    (Functor.postcompose₂.obj G).obj T')

/-- The comparison `δ : G X ⊗ G' M ⟶ G (X ⊗ M)` for a fixed `M`, as a natural transformation
of functors of `X`. -/
@[simps]
def comparisonFlipApp' (M : D) : G ⋙ T.flip.obj (G'.obj M) ⟶ T'.flip.obj M ⋙ G where
  app X := (δ.app X).app M
  naturality X X' f := by
    have := NatTrans.congr_app (δ.naturality f) M
    dsimp at this ⊢
    exact this

/-- The projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` for a fixed `M`, as a natural transformation of
functors of `K`. -/
@[simps]
noncomputable def projectionMapFlipApp (M : D) : T.flip.obj (G'.obj M) ⋙ F ⟶ F ⋙ T'.flip.obj M where
  app K := ((adj.projectionMap G' T T' δ).app K).app M
  naturality K K' f := by
    have := NatTrans.congr_app ((adj.projectionMap G' T T' δ).naturality f) M
    dsimp at this ⊢
    exact this

/-- The projection map for a fixed `M`, written as a composite of the whiskered unit, the
comparison `δ` and the whiskered counit. -/
lemma projectionMapFlipApp_eq (M : D) :
    adj.projectionMapFlipApp G' T T' δ M =
      whiskerRight ((Functor.leftUnitor _).inv ≫
          whiskerRight adj.unit (T.flip.obj (G'.obj M)) ≫
          (Functor.associator F G (T.flip.obj (G'.obj M))).hom ≫
          whiskerLeft F (comparisonFlipApp' G' T T' δ M) ≫
          (Functor.associator F (T'.flip.obj M) G).inv) F ≫
        (Functor.associator (F ⋙ T'.flip.obj M) G F).hom ≫
        whiskerLeft (F ⋙ T'.flip.obj M) adj.counit ≫ (Functor.rightUnitor _).hom := by
  ext K
  simp [projectionMap, projectionMapTranspose]

variable (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [F.CommShift A] [G.CommShift A]
  [adj.CommShift A] [∀ M : D, (T.flip.obj (G'.obj M)).CommShift A]
  [∀ M : D, (T'.flip.obj M).CommShift A]

/-- If `δ` commutes with the shifts in its first variable, so does the projection map: for every
`a : A` the square in `D`
```
F (T (K⟦a⟧) (G' M)) ─────────▶ T' (F (K⟦a⟧)) M
         │                             │
         ▼                             ▼
(F (T K (G' M)))⟦a⟧ ─────────▶ (T' (F K) M)⟦a⟧
```
commutes, where the horizontal maps are projection maps and the vertical maps are built from
the shift isomorphisms. -/
lemma commShift_projectionMapFlipApp (M : D)
    [NatTrans.CommShift (comparisonFlipApp' G' T T' δ M) A] :
    NatTrans.CommShift (adj.projectionMapFlipApp G' T T' δ M) A := by
  rw [projectionMapFlipApp_eq]
  infer_instance

end LeftAdjoint

end CategoryTheory.Adjunction
