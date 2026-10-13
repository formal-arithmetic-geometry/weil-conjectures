/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-!
# The base change map along a square of adjunctions through projection maps

Let `adj : F ⊣ G` and `adj' : F' ⊣ G'` be adjunctions, with `F : D ⥤ C` and `F' : D' ⥤ C'`,
let `adj_D : N_D ⊣ R_D` and `adj_C : N_C ⊣ R_C` be adjunctions with `N_D : D ⥤ D'` and
`N_C : C ⥤ C'`, and let `α : N_D ⋙ F' ≅ F ⋙ N_C`. Write `β : N_D (G M) ⟶ G' (N_C M)` for the
base change map, the mate of `α`, and `γ : F (R_D P) ⟶ R_C (F' P)` for the mate of `α⁻¹`.

Suppose the four categories carry bifunctors `⊗` and `F`, `F'`, `N_C`, `N_D` carry compatible
tensor comparisons (`CategoryTheory.Adjunction.ComparisonCompatible`). The four projection maps
of the four adjunctions and `γ` then compute `R_D` of the base change map: for `M` in `C` and `P`
in `D'`, the square

```
G M ⊗ R_D P ──PF_N──▶ R_D (N_D (G M) ⊗ P) ──R_D(β ⊗ P)──▶ R_D (G' (N_C M) ⊗ P)
     │                                                              │
  PF_F                                                          R_D(PF_F')
     ▼                                                              ▼
G (M ⊗ F (R_D P)) ──G(M ⊗ γ)──▶ G (M ⊗ R_C (F' P)) ──G(PF_N)──▶ G R_C (N_C M ⊗ F' P) ──▶ R_D G' (…)
```

commutes, the last arrow being the conjugate of `α`. This is the abstract form of the classical
argument showing that extension of scalars `- ⊗ᴸ_R S` commutes with `Rg_*` for proper `g`: with
`P` the unit, `R_D P` is `S` viewed as an `R`-module, `PF_N` is the identification
`K ⊗ᴸ_R S ≅ (K ⊗ᴸ_R S)|_R`, and `PF_F` is the projection formula for `Rg_*` at `S`.

## Main results

- `CategoryTheory.Adjunction.rightAdjointProjectionMap_comp_map_mateEquiv`: the square above.
- `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_projectionMap`: if the projection maps,
  `γ` at `P` are isomorphisms, `R_D` reflects isomorphisms and `- ⊗ P` reflects isomorphisms,
  then the base change map `β` is an isomorphism at `M`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
  {N_D : D ⥤ D'} {N_C : C ⥤ C'} {α : N_D ⋙ F' ≅ F ⋙ N_C}
  {R_D : D' ⥤ D} {R_C : C' ⥤ C} (adj_D : N_D ⊣ R_D) (adj_C : N_C ⊣ R_C)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D} {T_C' : C' ⥤ C' ⥤ C'} {T_D' : D' ⥤ D' ⥤ D'}
  {φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C}
  {φ' : (postcompose₂.obj F').obj T_D' ⟶ (((whiskeringLeft₂ C').obj F').obj F').obj T_C'}
  {m_C : (postcompose₂.obj N_C).obj T_C ≅ (((whiskeringLeft₂ C').obj N_C).obj N_C).obj T_C'}
  {m_D : (postcompose₂.obj N_D).obj T_D ≅ (((whiskeringLeft₂ D').obj N_D).obj N_D).obj T_D'}

/-- The projection map `M ⊗ R_N P ⟶ R_N (N M ⊗ P)` of an adjunction `N ⊣ R_N` with respect to
the second variable of a bifunctor: the transpose of `N (M ⊗ R_N P) ⟶ N M ⊗ N (R_N P) ⟶ N M ⊗ P`.
-/
def projectionMapRight {E E' : Type*} [Category* E] [Category* E'] {N : E ⥤ E'} {R_N : E' ⥤ E}
    (adj_N : N ⊣ R_N) {T_E : E ⥤ E ⥤ E} {T_E' : E' ⥤ E' ⥤ E'}
    (m : (postcompose₂.obj N).obj T_E ⟶ (((whiskeringLeft₂ E').obj N).obj N).obj T_E')
    (M : E) (P : E') : (T_E.obj M).obj (R_N.obj P) ⟶ R_N.obj ((T_E'.obj (N.obj M)).obj P) :=
  adj_N.homEquiv _ _ ((m.app M).app (R_N.obj P) ≫ (T_E'.obj (N.obj M)).map (adj_N.counit.app P))

include adj adj' adj_D adj_C in
/-- `R_D` of the base change map `β`, through the projection maps of the four adjunctions and the
mate `γ : F (R_D P) ⟶ R_C (F' P)` of `α⁻¹`. -/
lemma projectionMapRight_comp_map_mateEquiv (H : ComparisonCompatible α φ φ' m_C m_D) (M : C)
    (P : D') :
    projectionMapRight adj_D m_D.hom (G.obj M) P ≫
        R_D.map ((T_D'.map ((mateEquiv adj adj' α.hom).app M)).app P) ≫
        R_D.map (((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app P) =
      ((adj.rightAdjointProjectionMap φ).app M).app (R_D.obj P) ≫
        G.map ((T_C.obj M).map ((mateEquiv adj_D adj_C α.inv).app P)) ≫
        G.map (projectionMapRight adj_C m_C.hom M (F'.obj P)) ≫
        (mateEquiv adj_C adj_D (mateEquiv adj adj' α.hom)).app _ := by
  apply (adj_D.homEquiv _ _).symm.injective
  have hγ : N_C.map ((mateEquiv adj_D adj_C α.inv).app P) ≫ adj_C.counit.app (F'.obj P) =
      α.inv.app (R_D.obj P) ≫ F'.map (adj_D.counit.app P) :=
    mateEquiv_counit adj_D adj_C α.inv P
  have hβ' (x : C') := mateEquiv_counit adj_C adj_D (mateEquiv adj adj' α.hom) x
  have hPF' := ((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).naturality
    (adj_D.counit.app P)
  have hm := (m_C.hom.app M).naturality ((mateEquiv adj_D adj_C α.inv).app P)
  have hβ₁ := (mateEquiv adj adj' α.hom).naturality
    ((T_C.obj M).map ((mateEquiv adj_D adj_C α.inv).app P))
  have hβ₂ := (mateEquiv adj adj' α.hom).naturality
    (projectionMapRight adj_C m_C.hom M (F'.obj P))
  have hi := (T_D'.map ((mateEquiv adj adj' α.hom).app M)).naturality (adj_D.counit.app P)
  have hC : N_C.map (projectionMapRight adj_C m_C.hom M (F'.obj P)) ≫
      adj_C.counit.app _ = (m_C.hom.app M).app (R_C.obj (F'.obj P)) ≫
        (T_C'.obj (N_C.obj M)).map (adj_C.counit.app (F'.obj P)) :=
    (adj_C.homEquiv_counit _ _ _).symm.trans
      (by rw [projectionMapRight]; exact Equiv.symm_apply_apply _ _)
  have hD : N_D.map (projectionMapRight adj_D m_D.hom (G.obj M) P) ≫
      adj_D.counit.app _ = (m_D.hom.app (G.obj M)).app (R_D.obj P) ≫
        (T_D'.obj (N_D.obj (G.obj M))).map (adj_D.counit.app P) :=
    (adj_D.homEquiv_counit _ _ _).symm.trans
      (by rw [projectionMapRight]; exact Equiv.symm_apply_apply _ _)
  have key := adj.map_rightAdjointProjectionMap_comp_mateEquiv adj' H M (R_D.obj P)
  dsimp at hβ' hPF' hm hβ₁ hβ₂ hi key ⊢
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, counit_naturality,
    counit_naturality_assoc] at key ⊢
  rw [reassoc_of% hD, reassoc_of% hi, hPF', ← reassoc_of% key, hβ', reassoc_of% hβ₂,
    reassoc_of% hβ₁, ← G'.map_comp, ← G'.map_comp, ← G'.map_comp, ← G'.map_comp, hC,
    reassoc_of% hm, ← Functor.map_comp (T_C'.obj (N_C.obj M)) (α.inv.app _), ← hγ,
    Functor.map_comp]
  simp only [Functor.map_comp]

include adj adj' adj_D adj_C in
/-- **The base change map through projection maps.** Let `P` be an object of `D'` such that
`- ⊗ P` reflects isomorphisms (for instance the unit), and suppose that `R_D` reflects
isomorphisms. If the projection maps of `F ⊣ G` at `(M, R_D P)`, of `F' ⊣ G'` at `(N_C M, P)`,
of `N_D ⊣ R_D` at `(G M, P)` and of `N_C ⊣ R_C` at `(M, F' P)` are isomorphisms, and so is the
mate `F (R_D P) ⟶ R_C (F' P)` of `α⁻¹` at `P`, then the base change map
`N_D (G M) ⟶ G' (N_C M)` is an isomorphism. -/
theorem isIso_mateEquiv_app_of_isIso_projectionMap (H : ComparisonCompatible α φ φ' m_C m_D)
    (M : C) (P : D') [R_D.ReflectsIsomorphisms]
    (hP : ∀ {X Y : D'} (f : X ⟶ Y), IsIso ((T_D'.map f).app P) → IsIso f)
    [IsIso (projectionMapRight adj_D m_D.hom (G.obj M) P)]
    [IsIso (((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app P)]
    [IsIso (((adj.rightAdjointProjectionMap φ).app M).app (R_D.obj P))]
    [IsIso ((mateEquiv adj_D adj_C α.inv).app P)]
    [IsIso (projectionMapRight adj_C m_C.hom M (F'.obj P))] :
    IsIso ((mateEquiv adj adj' α.hom).app M) := by
  have : IsIso (mateEquiv adj_C adj_D (mateEquiv adj adj' α.hom)) :=
    isIso_mateEquiv_mateEquiv adj adj' α adj_D adj_C
  have h := projectionMapRight_comp_map_mateEquiv adj adj' adj_D adj_C H M P
  have : IsIso (projectionMapRight adj_D m_D.hom (G.obj M) P ≫
      R_D.map ((T_D'.map ((mateEquiv adj adj' α.hom).app M)).app P) ≫
      R_D.map (((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app P)) := by
    rw [h]
    infer_instance
  have : IsIso (R_D.map ((T_D'.map ((mateEquiv adj adj' α.hom).app M)).app P)) := by
    have := IsIso.of_isIso_comp_left (projectionMapRight adj_D m_D.hom (G.obj M) P)
      (R_D.map ((T_D'.map ((mateEquiv adj adj' α.hom).app M)).app P) ≫
        R_D.map (((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app P))
    exact IsIso.of_isIso_comp_right _
      (R_D.map (((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app P))
  exact hP _ (isIso_of_reflects_iso _ R_D)

end CategoryTheory.Adjunction
