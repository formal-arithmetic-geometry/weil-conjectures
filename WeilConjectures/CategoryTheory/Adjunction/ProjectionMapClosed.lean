/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal homs along adjunctions of monoidal functors

Let `C` and `D` be monoidal closed categories. This file records how projection formulas for
an adjunction of monoidal functors control the comparison maps between internal homs.

- **Internal adjunction.** For adjunctions `F ⊣ G ⊣ H` with `F` monoidal, if the projection
  maps `G M ⊗ L ⟶ G (M ⊗ F L)` are isomorphisms then so are the maps
  `G [M, H K] ⟶ [G M, G H K] ⟶ [G M, K]` given by the comparison map of the lax monoidal
  functor `G` and the counit of `G ⊣ H`
  (`CategoryTheory.Adjunction.isIso_internalAdjunctionHom`). For `G = Rf_*` and `H = f^!` with
  `f` proper, this is `Rf_* RHom(M, f^! K) ≅ RHom(Rf_* M, K)`.
- **Monoidal right adjoints commute with internal homs.** For an adjunction `F ⊣ G` with `G`
  monoidal, if the projection maps `F (G A ⊗ N) ⟶ A ⊗ F N` are isomorphisms then so are the
  comparison maps `G [A, B] ⟶ [G A, G B]`
  (`CategoryTheory.Adjunction.isIso_ihomComparison_of_isIso_leftProjectionHom`). For `G = j^*`
  and `F = j_!` with `j` an open immersion, this is `j^* RHom(A, B) ≅ RHom(j^* A, j^* B)`.

Both statements are proved with the Yoneda lemma, by writing the morphisms induced by the
comparison maps as composites of adjunction bijections.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory MonoidalClosed Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

section InternalAdjunction

variable [MonoidalClosed C] [MonoidalClosed D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  [F.OplaxMonoidal] {H : D ⥤ C} (adj' : G ⊣ H)

/-- The projection map `G M ⊗ L ⟶ G (M ⊗ F L)` of an adjunction `F ⊣ G` with `F` oplax
monoidal: the transpose of `F (G M ⊗ L) ⟶ F G M ⊗ F L ⟶ M ⊗ F L`. -/
noncomputable def projectionHom (M : C) (L : D) : G.obj M ⊗ L ⟶ G.obj (M ⊗ F.obj L) :=
  adj.homEquiv _ _ (δ F (G.obj M) L ≫ adj.counit.app M ▷ F.obj L)

omit [MonoidalClosed C] [MonoidalClosed D] in
/-- `CategoryTheory.Adjunction.projectionHom` is the right adjoint projection map
(`CategoryTheory.Adjunction.rightAdjointProjectionMap`) of any natural transformation `φ` of
bifunctors with components the comonoidal structure maps `δ` of `F`. -/
lemma projectionHom_eq_rightAdjointProjectionMap
    (φ : (Functor.postcompose₂.obj F).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (hφ : ∀ X Y, (φ.app X).app Y = δ F X Y) (M : C) (L : D) :
    adj.projectionHom M L = ((adj.rightAdjointProjectionMap φ).app M).app L := by
  rw [rightAdjointProjectionMap_app_app, hφ]
  rfl

omit [MonoidalClosed C] [MonoidalClosed D] in
/-- The lax monoidal structure of the right adjoint `G` through the projection map: for
`a : L ⟶ G Y`, `G M ◁ a ≫ μ = π ≫ G (M ◁ a♭)`, where `a♭ : F L ⟶ Y` is the transpose of `a`. -/
lemma whiskerLeft_comp_rightAdjointLaxMonoidal_μ (M : C) {L : D} {Y : C} (a : L ⟶ G.obj Y) :
    letI := adj.rightAdjointLaxMonoidal
    G.obj M ◁ a ≫ μ G M Y = adj.projectionHom M L ≫ G.map (M ◁ (adj.homEquiv _ _).symm a) := by
  rw [rightAdjointLaxMonoidal_μ, ← homEquiv_naturality_left, projectionHom,
    ← homEquiv_naturality_right]
  congr 1
  rw [homEquiv_counit, ← δ_natural_right_assoc, Category.assoc, tensorHom_def',
    ← MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange]

/-- The internal adjunction map `G [M, H K] ⟶ [G M, G H K] ⟶ [G M, K]`, the comparison map of
the lax monoidal right adjoint `G` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`)
followed by the counit of `G ⊣ H`. -/
noncomputable def internalAdjunctionHom (M : C) (K : D) :
    G.obj ((ihom M).obj (H.obj K)) ⟶ (ihom (G.obj M)).obj K :=
  letI := adj.rightAdjointLaxMonoidal
  (ihomComparison G M).natTrans.app (H.obj K) ≫ (ihom (G.obj M)).map (adj'.counit.app K)

lemma uncurry_comp_internalAdjunctionHom (M : C) (K : D) {T : D}
    (a : T ⟶ G.obj ((ihom M).obj (H.obj K))) :
    uncurry (a ≫ adj.internalAdjunctionHom adj' M K) =
      adj.projectionHom M T ≫ (adj'.homEquiv _ _).symm (uncurry ((adj.homEquiv _ _).symm a)) := by
  let := adj.rightAdjointLaxMonoidal
  have h := adj.whiskerLeft_comp_rightAdjointLaxMonoidal_μ M a
  rw [internalAdjunctionHom, ← Category.assoc, uncurry_natural_right, uncurry_natural_left,
    uncurry_eq, ihomComparison_ev, ← Category.assoc, h, adj'.homEquiv_counit, uncurry_eq,
    Functor.map_comp]
  simp only [Category.assoc]

/-- **The internal adjunction.** For adjunctions `F ⊣ G ⊣ H` with `F` monoidal, if the
projection maps `G M ⊗ L ⟶ G (M ⊗ F L)` are isomorphisms, then the internal adjunction map
`G [M, H K] ⟶ [G M, K]` (`CategoryTheory.Adjunction.internalAdjunctionHom`) is an
isomorphism. -/
theorem isIso_internalAdjunctionHom [∀ M L, IsIso (adj.projectionHom M L)] (M : C) (K : D) :
    IsIso (adj.internalAdjunctionHom adj' M K) := by
  refine isIso_of_yoneda_map_bijective _ fun T ↦ ?_
  have h : (fun a : T ⟶ G.obj ((ihom M).obj (H.obj K)) ↦ a ≫ adj.internalAdjunctionHom adj' M K) =
      (fun g ↦ curry (adj.projectionHom M T ≫ g)) ∘ (adj'.homEquiv _ _).symm ∘ uncurry ∘
        (adj.homEquiv _ _).symm := by
    funext a
    exact (eq_curry_iff _ _).2 (adj.uncurry_comp_internalAdjunctionHom adj' M K a)
  rw [h]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp (Equiv.bijective _)
    (Function.Bijective.comp ?_ (Equiv.bijective _)))
  · refine Function.Bijective.comp ?_ ?_
    · exact ⟨fun _ _ h ↦ curry_injective h, fun g ↦ ⟨uncurry g, curry_uncurry g⟩⟩
    · exact ⟨fun _ _ h ↦ (cancel_epi _).1 h, fun g ↦ ⟨inv (adj.projectionHom M T) ≫ g, by simp⟩⟩
  · exact ⟨fun _ _ h ↦ uncurry_injective h, fun g ↦ ⟨curry g, uncurry_curry g⟩⟩

end InternalAdjunction

section IhomComparison

variable [MonoidalClosed C] [MonoidalClosed D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  [G.LaxMonoidal]

/-- The left projection map `F (G A ⊗ N) ⟶ A ⊗ F N` of an adjunction `F ⊣ G` with `G` lax
monoidal: the transpose of `G A ⊗ N ⟶ G A ⊗ G F N ⟶ G (A ⊗ F N)`. -/
noncomputable def leftProjectionHom (A : C) (N : D) : F.obj (G.obj A ⊗ N) ⟶ A ⊗ F.obj N :=
  (adj.homEquiv _ _).symm (G.obj A ◁ adj.unit.app N ≫ μ G A (F.obj N))

lemma homEquiv_symm_uncurry_comp_ihomComparison (A B : C) {N : D}
    (b : N ⟶ G.obj ((ihom A).obj B)) :
    (adj.homEquiv _ _).symm (uncurry (b ≫ (ihomComparison G A).natTrans.app B)) =
      adj.leftProjectionHom A N ≫ uncurry ((adj.homEquiv _ _).symm b) := by
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, uncurry_natural_left, uncurry_eq, ihomComparison_ev,
    leftProjectionHom, homEquiv_naturality_right, Equiv.apply_symm_apply, uncurry_eq,
    Category.assoc, Functor.map_comp, ← μ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← homEquiv_unit, Equiv.apply_symm_apply]

/-- **Right adjoints commute with internal homs under a projection formula.** For an adjunction
`F ⊣ G` with `G` lax monoidal, if the left projection maps `F (G A ⊗ N) ⟶ A ⊗ F N`
(`CategoryTheory.Adjunction.leftProjectionHom`) are isomorphisms, then the comparison maps
`G [A, B] ⟶ [G A, G B]` are isomorphisms. -/
theorem isIso_ihomComparison_of_isIso_leftProjectionHom (A B : C)
    [∀ N, IsIso (adj.leftProjectionHom A N)] :
    IsIso ((ihomComparison G A).natTrans.app B) := by
  refine isIso_of_yoneda_map_bijective _ fun N ↦ ?_
  have h : (fun b : N ⟶ (ihom A ⋙ G).obj B ↦ b ≫ (ihomComparison G A).natTrans.app B) =
      curry ∘ adj.homEquiv _ _ ∘ (fun g ↦ adj.leftProjectionHom A N ≫ g) ∘ uncurry ∘
        (adj.homEquiv _ _).symm := by
    funext b
    simp only [Function.comp_apply]
    rw [← homEquiv_symm_uncurry_comp_ihomComparison, Equiv.apply_symm_apply, curry_uncurry]
  rw [h]
  refine Function.Bijective.comp ⟨fun _ _ h ↦ curry_injective h,
    fun g ↦ ⟨uncurry g, curry_uncurry g⟩⟩ (Function.Bijective.comp (Equiv.bijective _)
      (Function.Bijective.comp ?_ (Function.Bijective.comp ?_ (Equiv.bijective _))))
  · exact ⟨fun _ _ h ↦ (cancel_epi _).1 h,
      fun g ↦ ⟨inv (adj.leftProjectionHom A N) ≫ g, by simp⟩⟩
  · exact ⟨fun _ _ h ↦ uncurry_injective h, fun g ↦ ⟨curry g, uncurry_curry g⟩⟩

end IhomComparison

end CategoryTheory.Adjunction

namespace CategoryTheory

open MonoidalCategory MonoidalClosed Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

/-- The comparison maps `G [A, B] ⟶ [G A, G B]` of a lax monoidal functor are natural in `A`:
for `u : A' ⟶ A` the square
```
  G [A, B] ──────c──────→ [G A, G B]
     │                        │
  G [u, B]                [G u, G B]
     ↓                        ↓
  G [A', B] ─────c─────→ [G A', G B]
```
commutes. -/
@[reassoc]
lemma Functor.LaxMonoidal.map_pre_app_comp_ihomComparison [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.LaxMonoidal] {A A' : C} (u : A' ⟶ A) (B : C) :
    G.map ((pre u).app B) ≫ (ihomComparison G A').natTrans.app B =
      (ihomComparison G A).natTrans.app B ≫ (pre (G.map u)).app (G.obj B) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_eq, ihomComparison_ev, uncurry_pre_app, uncurry_eq,
    ihomComparison_ev, μ_natural_right_assoc, ← G.map_comp, id_tensor_pre_app_comp_ev,
    G.map_comp, ← μ_natural_left_assoc]

namespace Adjunction

/-- The lax monoidal right adjoint (`CategoryTheory.Adjunction.rightAdjointLaxMonoidal`) of an
oplax monoidal functor `F` whose comonoidal structure is compatible with the braidings is lax
braided. -/
@[instance_reducible]
noncomputable def rightAdjointLaxBraidedOfMapBraidingCompδ [BraidedCategory C]
    [BraidedCategory D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]
    (h : ∀ X Y, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) :
    G.LaxBraided where
  toLaxMonoidal := adj.rightAdjointLaxMonoidal
  braided X Y := by
    let := adj.rightAdjointLaxMonoidal
    rw [rightAdjointLaxMonoidal_μ, rightAdjointLaxMonoidal_μ,
      ← homEquiv_naturality_right, ← homEquiv_naturality_left]
    congr 1
    rw [Category.assoc, BraidedCategory.braiding_naturality, reassoc_of% (h (G.obj X) (G.obj Y))]

end Adjunction

end CategoryTheory
