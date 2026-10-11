/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# Associativity of projection maps

Let `F ⊣ G` be an adjunction between monoidal categories, with `F` oplax monoidal. The right
adjoint projection map `π_{M, L} : G M ⊗ L ⟶ G (M ⊗ F L)` of
`CategoryTheory.Adjunction.rightAdjointProjectionMap` (for the comparison `δ F`) is compatible
with the associativity of the tensor products: the two maps
`(G M ⊗ L) ⊗ L' ⟶ G (M ⊗ (F L ⊗ F L'))` obtained from `π_{M, L ⊗ L'}` and from
`π_{M, L}` followed by `π_{M ⊗ F L, L'}` agree
(`CategoryTheory.Adjunction.rightAdjointProjectionMap_assoc_of_δ`).

Dually, the left adjoint projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` of
`CategoryTheory.Adjunction.projectionMap` is associative as soon as its comparison
`δ : G X ⊗ G' Y ⟶ G (X ⊗ Y)` is compatible with an oplax monoidal structure on `G'`
(`CategoryTheory.Adjunction.projectionMap_assoc_of_projectionComparisonAssoc`); this holds for
the comparison obtained from an isomorphism `G' ≅ G` and the inverse of the comonoidal
structure of `G'` (`CategoryTheory.Adjunction.projectionComparisonAssoc_of_iso`).

Finally, for a composite `Rf_! = R ∘ I` of two functors equipped with associative projection
maps, the composite projection map, transported along a monoidal isomorphism of pullbacks
`P_g ⋙ P_i ≅ P_f`, is again associative
(`CategoryTheory.Adjunction.compProjectionMap_assoc`). This is the formal input for the
compatibility of the projection formula for compactly supported direct images with finite
reduction of coefficients (blueprint `sk-prop-sf-pf-reduction`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory Functor.OplaxMonoidal

section RightAdjoint

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]
  (φ : (Functor.postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
  (hφ : ∀ a b, (φ.app a).app b = δ F a b)

include hφ in
/-- The transpose of the right adjoint projection map for the comparison `δ F` is
`δ F` followed by the counit in the first variable. -/
@[reassoc]
lemma map_rightAdjointProjectionMap_app_app_comp_counit_of_δ (M : C) (L : D) :
    F.map (((adj.rightAdjointProjectionMap φ).app M).app L) ≫ adj.counit.app _ =
      δ F (G.obj M) L ≫ adj.counit.app M ▷ F.obj L := by
  rw [map_rightAdjointProjectionMap_app_app_comp_counit, hφ]
  rfl

include hφ in
/-- **Associativity of the right adjoint projection map.** For `F ⊣ G` with `F` oplax monoidal
and `π_{M, L} : G M ⊗ L ⟶ G (M ⊗ F L)` the right adjoint projection map for `δ F`, the square
```
(G M ⊗ L) ⊗ L' --π ▷ L'--> G (M ⊗ F L) ⊗ L' --π--> G ((M ⊗ F L) ⊗ F L')
      | α                                                  | G α
      v                                                    v
G M ⊗ (L ⊗ L') ------π-----> G (M ⊗ F (L ⊗ L')) --G (M ◁ δ)--> G (M ⊗ (F L ⊗ F L'))
```
commutes. -/
lemma rightAdjointProjectionMap_assoc_of_δ (M : C) (L L' : D) :
    ((adj.rightAdjointProjectionMap φ).app M).app L ▷ L' ≫
        ((adj.rightAdjointProjectionMap φ).app (M ⊗ F.obj L)).app L' ≫
          G.map (α_ M (F.obj L) (F.obj L')).hom =
      (α_ (G.obj M) L L').hom ≫ ((adj.rightAdjointProjectionMap φ).app M).app (L ⊗ L') ≫
        G.map (M ◁ δ F L L') := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    map_rightAdjointProjectionMap_app_app_comp_counit_of_δ_assoc adj φ hφ]
  have h₁ := δ_natural_left F (((adj.rightAdjointProjectionMap φ).app M).app L) L'
  have h₂ := map_rightAdjointProjectionMap_app_app_comp_counit_of_δ adj φ hφ M L
  erw [← reassoc_of% h₁, ← comp_whiskerRight_assoc, h₂]
  rw [comp_whiskerRight_assoc]
  erw [associator_naturality_left, associativity_assoc]
  rw [whisker_exchange]
  rfl

end RightAdjoint

section LeftAdjoint

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (G' : D ⥤ C) [G'.OplaxMonoidal]
  (δ' : (((Functor.whiskeringLeft₂ C).obj G).obj G').obj (curriedTensor C) ⟶
    (Functor.postcompose₂.obj G).obj (curriedTensor D))

/-- The compatibility of a comparison `δ' : G X ⊗ G' Y ⟶ G (X ⊗ Y)` with the comonoidal
structure of `G'`: the two maps `G X ⊗ G' (Y ⊗ Z) ⟶ G (X ⊗ (Y ⊗ Z))` agree. -/
def ProjectionComparisonAssoc : Prop :=
  ∀ X Y Z, G.obj X ◁ δ G' Y Z ≫ (α_ _ _ _).inv ≫ ((δ'.app X).app Y ▷ G'.obj Z) ≫
    (δ'.app (X ⊗ Y)).app Z ≫ G.map (α_ X Y Z).hom = (δ'.app X).app (Y ⊗ Z)

variable {G'} {δ'}

/-- **Associativity of the left adjoint projection map.** For `F ⊣ G`, an oplax monoidal
`G'` and a comparison `δ' : G X ⊗ G' Y ⟶ G (X ⊗ Y)` compatible with `δ G'`, the projection
map `p_{K, M} : F (K ⊗ G' M) ⟶ F K ⊗ M` satisfies
```
F (K ⊗ G' (M ⊗ M')) --F (K ◁ δ)--> F (K ⊗ (G' M ⊗ G' M')) --F α⁻¹--> F ((K ⊗ G' M) ⊗ G' M')
        | p                                                                   | p
        v                                                                     v
F K ⊗ (M ⊗ M') <-------α-------- (F K ⊗ M) ⊗ M' <-------p ▷ M'------- F (K ⊗ G' M) ⊗ M'
``` -/
lemma projectionMap_assoc_of_projectionComparisonAssoc (hδ' : ProjectionComparisonAssoc G' δ')
    (K : C) (M M' : D) :
    F.map (K ◁ δ G' M M') ≫ F.map (α_ K (G'.obj M) (G'.obj M')).inv ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ').app
          (K ⊗ G'.obj M)).app M' ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ').app K).app M ▷ M' ≫
        (α_ (F.obj K) M M').hom =
      ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ').app K).app (M ⊗ M') := by
  apply (adj.homEquiv _ _).injective
  have h₁ := adj.unit_app_comp_map_projectionMap_app_app G' (curriedTensor C)
    (curriedTensor D) δ' (K ⊗ G'.obj M) M'
  have h₂ := adj.unit_app_comp_map_projectionMap_app_app G' (curriedTensor C)
    (curriedTensor D) δ' K (M ⊗ M')
  have h₃ := adj.unit_app_comp_map_projectionMap_app_app G' (curriedTensor C)
    (curriedTensor D) δ' K M
  have h₄ := NatTrans.congr_app (δ'.naturality
    (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ').app K).app M)) M'
  simp only [homEquiv_unit, Functor.map_comp, unit_naturality_assoc]
  erw [reassoc_of% h₁, h₂]
  dsimp only [projectionMapTranspose, NatTrans.comp_app] at h₃ h₄ ⊢
  dsimp at h₃ h₄ ⊢
  rw [assoc, ← reassoc_of% h₄, ← comp_whiskerRight_assoc, h₃, comp_whiskerRight_assoc,
    ← associator_inv_naturality_left_assoc, whisker_exchange_assoc, ← hδ' (F.obj K) M M']

end LeftAdjoint

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

open Category MonoidalCategory Functor.OplaxMonoidal

section LeftAdjointIso

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {G G' : D ⥤ C} [G'.OplaxMonoidal] [∀ X Y, IsIso (δ G' X Y)] (ι : G' ≅ G)
  {δ' : (((Functor.whiskeringLeft₂ C).obj G).obj G').obj (curriedTensor C) ⟶
    (Functor.postcompose₂.obj G).obj (curriedTensor D)}

/-- The comparison `G X ⊗ G' Y ⟶ G (X ⊗ Y)` built from an isomorphism `ι : G' ≅ G` and the
inverse of the comonoidal structure of `G'` is compatible with `δ G'`. -/
lemma projectionComparisonAssoc_of_iso
    (hδ' : ∀ X Y, (δ'.app X).app Y =
      ι.inv.app X ▷ G'.obj Y ≫ inv (δ G' X Y) ≫ ι.hom.app (X ⊗ Y)) :
    ProjectionComparisonAssoc G' δ' := by
  intro X Y Z
  have key : G'.obj X ◁ δ G' Y Z ≫ (α_ _ _ _).inv ≫ inv (δ G' X Y) ▷ G'.obj Z ≫
      inv (δ G' (X ⊗ Y) Z) ≫ G'.map (α_ X Y Z).hom = inv (δ G' X (Y ⊗ Z)) := by
    rw [← cancel_epi (δ G' X (Y ⊗ Z)), IsIso.hom_inv_id, ← cancel_mono (G'.map (α_ X Y Z).inv)]
    simp only [assoc, ← G'.map_comp, Iso.hom_inv_id, G'.map_id, comp_id, id_comp]
    rw [← cancel_mono (δ G' (X ⊗ Y) Z), assoc, assoc, assoc, assoc, IsIso.inv_hom_id, comp_id,
      ← cancel_mono (δ G' X Y ▷ G'.obj Z), assoc, assoc, assoc, ← comp_whiskerRight,
      IsIso.inv_hom_id, id_whiskerRight, comp_id, associativity_inv, assoc]
  rw [hδ', hδ', hδ', comp_whiskerRight, comp_whiskerRight, assoc, assoc, assoc, assoc,
    ← comp_whiskerRight_assoc (ι.hom.app _), Iso.hom_inv_id_app, id_whiskerRight, id_comp,
    ← ι.hom.naturality, ← associator_inv_naturality_left_assoc, whisker_exchange_assoc]
  rw [reassoc_of% key]

end LeftAdjointIso

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

open Category MonoidalCategory Functor.OplaxMonoidal

section Composite

variable {CX CZ CY : Type*} [Category* CX] [Category* CZ] [Category* CY] [MonoidalCategory CX]
  [MonoidalCategory CZ] [MonoidalCategory CY] {I : CX ⥤ CZ} {R : CZ ⥤ CY}
  {Pi : CZ ⥤ CX} {Pg : CY ⥤ CZ} {Pf : CY ⥤ CX} (e : Pg ⋙ Pi ≅ Pf)
  {δi : ∀ M M', Pi.obj (M ⊗ M') ⟶ Pi.obj M ⊗ Pi.obj M'}
  {δg : ∀ L L', Pg.obj (L ⊗ L') ⟶ Pg.obj L ⊗ Pg.obj L'}
  {δf : ∀ L L', Pf.obj (L ⊗ L') ⟶ Pf.obj L ⊗ Pf.obj L'}
  (πg : ∀ M L, R.obj M ⊗ L ⟶ R.obj (M ⊗ Pg.obj L))
  (q : ∀ K M, I.obj K ⊗ M ⟶ I.obj (K ⊗ Pi.obj M))

/-- The composite projection map `R (I K) ⊗ L ⟶ R (I (K ⊗ P_f L))` of the projection map `πg`
of `R`, of the projection map `q` of `I` and of the isomorphism `e : P_g ⋙ P_i ≅ P_f`. -/
def compProjectionMap (K : CX) (L : CY) : R.obj (I.obj K) ⊗ L ⟶ R.obj (I.obj (K ⊗ Pf.obj L)) :=
  πg (I.obj K) L ≫ R.map (q K (Pg.obj L)) ≫ R.map (I.map (K ◁ e.hom.app L))

variable {e πg q}

/-- **Associativity of a composite projection map.** Let `πg : R M ⊗ L ⟶ R (M ⊗ P_g L)` and
`q : I K ⊗ M ⟶ I (K ⊗ P_i M)` be natural projection maps satisfying the associativity laws for
comparisons `δg : P_g (L ⊗ L') ⟶ P_g L ⊗ P_g L'` and `δi`, and let `e : P_g ⋙ P_i ≅ P_f` carry
`δg` and `δi` to a comparison `δf` for `P_f`. Then the composite projection map
`R (I K) ⊗ L ⟶ R (I (K ⊗ P_f L))` satisfies the associativity law for `δf`. -/
lemma compProjectionMap_assoc
    (he : ∀ L L', e.hom.app (L ⊗ L') ≫ δf L L' =
      Pi.map (δg L L') ≫ δi (Pg.obj L) (Pg.obj L') ≫ (e.hom.app L ⊗ₘ e.hom.app L'))
    (hπnat : ∀ {M M'} (f : M ⟶ M') L, R.map f ▷ L ≫ πg M' L = πg M L ≫ R.map (f ▷ Pg.obj L))
    (hπ : ∀ M L L', πg M L ▷ L' ≫ πg (M ⊗ Pg.obj L) L' ≫ R.map (α_ M (Pg.obj L) (Pg.obj L')).hom =
      (α_ (R.obj M) L L').hom ≫ πg M (L ⊗ L') ≫ R.map (M ◁ δg L L'))
    (hqnat₁ : ∀ {K K'} (f : K ⟶ K') M, I.map f ▷ M ≫ q K' M = q K M ≫ I.map (f ▷ Pi.obj M))
    (hqnat₂ : ∀ K {M M'} (g : M ⟶ M'), I.obj K ◁ g ≫ q K M' = q K M ≫ I.map (K ◁ Pi.map g))
    (hq : ∀ K M M', q K (M ⊗ M') ≫ I.map (K ◁ δi M M') =
      (α_ (I.obj K) M M').inv ≫ q K M ▷ M' ≫ q (K ⊗ Pi.obj M) M' ≫
        I.map (α_ K (Pi.obj M) (Pi.obj M')).hom)
    (K : CX) (L L' : CY) :
    compProjectionMap e πg q K L ▷ L' ≫ compProjectionMap e πg q (K ⊗ Pf.obj L) L' ≫
        R.map (I.map (α_ K (Pf.obj L) (Pf.obj L')).hom) =
      (α_ (R.obj (I.obj K)) L L').hom ≫ compProjectionMap e πg q K (L ⊗ L') ≫
        R.map (I.map (K ◁ δf L L')) := by
  dsimp only [compProjectionMap]
  have h₂ : q K (Pg.obj L) ▷ Pg.obj L' ≫ I.map (K ◁ e.hom.app L) ▷ Pg.obj L' ≫
      q (K ⊗ Pf.obj L) (Pg.obj L') ≫ I.map ((K ⊗ Pf.obj L) ◁ e.hom.app L') ≫
        I.map (α_ K (Pf.obj L) (Pf.obj L')).hom =
      q K (Pg.obj L) ▷ Pg.obj L' ≫ q (K ⊗ Pi.obj (Pg.obj L)) (Pg.obj L') ≫
        I.map (α_ K (Pi.obj (Pg.obj L)) (Pi.obj (Pg.obj L'))).hom ≫
          I.map (K ◁ (e.hom.app L ⊗ₘ e.hom.app L')) := by
    rw [reassoc_of% (hqnat₁ (K ◁ e.hom.app L) (Pg.obj L')), ← I.map_comp, ← I.map_comp,
      ← I.map_comp]
    congr 3
    simp [tensorHom_def]
  have h₃ := hqnat₂ K (δg L L')
  have h₄ := hq K (Pg.obj L) (Pg.obj L')
  have h₅ := he L L'
  simp only [comp_whiskerRight, assoc, ← R.map_comp]
  have hπ' : πg (I.obj K) L ▷ L' ≫ πg (I.obj K ⊗ Pg.obj L) L' = (α_ _ _ _).hom ≫
      πg (I.obj K) (L ⊗ L') ≫ R.map (I.obj K ◁ δg L L') ≫ R.map (α_ _ _ _).inv := by
    rw [← reassoc_of% (hπ (I.obj K) L L'), ← R.map_comp, Iso.hom_inv_id, R.map_id, comp_id]
  rw [reassoc_of% (hπnat (q K (Pg.obj L) ≫ I.map (K ◁ e.hom.app L)) L'), reassoc_of% hπ']
  simp only [← R.map_comp]
  congr 3
  have h₆ : I.map (K ◁ e.hom.app (L ⊗ L')) ≫ I.map (K ◁ δf L L') =
      I.map (K ◁ Pi.map (δg L L')) ≫ I.map (K ◁ δi (Pg.obj L) (Pg.obj L')) ≫
        I.map (K ◁ (e.hom.app L ⊗ₘ e.hom.app L')) := by
    rw [← I.map_comp, ← MonoidalCategory.whiskerLeft_comp, h₅]
    simp only [MonoidalCategory.whiskerLeft_comp, I.map_comp]
  rw [h₆, ← reassoc_of% h₃, reassoc_of% h₄, ← h₂, comp_whiskerRight_assoc]

end Composite

section TensorRight

variable {CX CY : Type*} [Category* CX] [Category* CY] [MonoidalCategory CX]
  [MonoidalCategory CY] {R : CX ⥤ CY} {P : CY ⥤ CX}
  {δ : ∀ L L', P.obj (L ⊗ L') ⟶ P.obj L ⊗ P.obj L'}
  (π : ∀ K L, R.obj K ⊗ L ⟶ R.obj (K ⊗ P.obj L))
  (hπ : ∀ K L L', π K L ▷ L' ≫ π (K ⊗ P.obj L) L' ≫ R.map (α_ K (P.obj L) (P.obj L')).hom =
    (α_ (R.obj K) L L').hom ≫ π K (L ⊗ L') ≫ R.map (K ◁ δ L L'))
  {NY : CY} {NX : CX} (a : P.obj NY ⟶ NX)

include hπ in
/-- **Tensoring a projection map with a fixed object.** Let `π_{K, L} : R K ⊗ L ⟶ R (K ⊗ P L)`
be a projection map satisfying the associativity law for a comparison
`δ : P (L ⊗ L') ⟶ P L ⊗ P L'`, and let `a : P N_Y ⟶ N_X`. Write
`c_M = π_{M, N_Y} ≫ R (M ◁ a) : R M ⊗ N_Y ⟶ R (M ⊗ N_X)` for the induced comparison of `R`
with `- ⊗ N`. Then the square
```
(R K ⊗ L) ⊗ N_Y --π_{K, L} ▷ N_Y--> R (K ⊗ P L) ⊗ N_Y ------c------> R ((K ⊗ P L) ⊗ N_X)
      | α                                                                  ^ R α⁻¹
      v                                                                    |
R K ⊗ (L ⊗ N_Y) --π--> R (K ⊗ P (L ⊗ N_Y)) --R (K ◁ (δ ≫ P L ◁ a))--> R (K ⊗ (P L ⊗ N_X))
```
commutes. -/
lemma projectionMap_whiskerRight_comp (K : CX) (L : CY) :
    π K L ▷ NY ≫ π (K ⊗ P.obj L) NY ≫ R.map ((K ⊗ P.obj L) ◁ a) =
      (α_ (R.obj K) L NY).hom ≫ π K (L ⊗ NY) ≫ R.map (K ◁ (δ L NY ≫ P.obj L ◁ a)) ≫
        R.map (α_ K (P.obj L) NX).inv := by
  have h : π K L ▷ NY ≫ π (K ⊗ P.obj L) NY = (α_ (R.obj K) L NY).hom ≫ π K (L ⊗ NY) ≫
      R.map (K ◁ δ L NY) ≫ R.map (α_ K (P.obj L) (P.obj NY)).inv := by
    rw [← reassoc_of% (hπ K L NY), ← R.map_comp, Iso.hom_inv_id, R.map_id, comp_id]
  rw [reassoc_of% h]
  simp only [← R.map_comp, MonoidalCategory.whiskerLeft_comp, assoc,
    associator_inv_naturality_right]

/-- The comparison `c_K = π_{K, N_Y} ≫ R (K ◁ a)` of
`CategoryTheory.Adjunction.projectionMap_whiskerRight_comp` is natural in `K` if `π` is. -/
lemma projectionMap_comp_map_whiskerLeft_naturality
    (hnat : ∀ {K K'} (φ : K ⟶ K') L, R.map φ ▷ L ≫ π K' L = π K L ≫ R.map (φ ▷ P.obj L))
    {K K' : CX} (φ : K ⟶ K') :
    R.map φ ▷ NY ≫ π K' NY ≫ R.map (K' ◁ a) = (π K NY ≫ R.map (K ◁ a)) ≫ R.map (φ ▷ NX) := by
  rw [reassoc_of% (hnat φ NY), assoc, ← R.map_comp, ← R.map_comp, whisker_exchange]

include hπ in
/-- With the notation of `CategoryTheory.Adjunction.projectionMap_whiskerRight_comp`: if `a`,
`δ` and the comparison `c_{K ⊗ P L}` are isomorphisms, then `π_{K, L} ▷ N_Y` is an isomorphism if
and only if `π_{K, L ⊗ N_Y}` is. -/
lemma isIso_projectionMap_whiskerRight_iff [IsIso a] (K : CX) (L : CY)
    [IsIso (δ L NY)] (hc : IsIso (π (K ⊗ P.obj L) NY ≫ R.map ((K ⊗ P.obj L) ◁ a))) :
    IsIso (π K L ▷ NY) ↔ IsIso (π K (L ⊗ NY)) := by
  rw [← isIso_comp_right_iff _ (π (K ⊗ P.obj L) NY ≫ R.map ((K ⊗ P.obj L) ◁ a)),
    projectionMap_whiskerRight_comp π hπ, isIso_comp_left_iff, ← assoc, isIso_comp_right_iff,
    isIso_comp_right_iff]

end TensorRight

end CategoryTheory.Adjunction
