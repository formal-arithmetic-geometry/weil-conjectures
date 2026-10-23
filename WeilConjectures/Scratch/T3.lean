module

public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section
open CategoryTheory

variable {CX CZ D : Type*} [Category CX] [Category CZ] [Category D] {aX : CX ⥤ D}
  {aZ : CZ ⥤ D} {uΦ : CX ⥤ CX} {ui : CX ⥤ CZ} {uΦZ : CZ ⥤ CZ} {ri : CZ ⥤ CX}

lemma closedPiece_pullback_comm_aux (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ)
    (pΦZ : aZ ⟶ uΦZ ⋙ aZ) {u₁ u₂ : CX ⥤ CZ} (p₁ : aX ⟶ u₁ ⋙ aZ) (p₂ : aX ⟶ u₂ ⋙ aZ)
    (c₁ : u₁ ≅ uΦ ⋙ ui) (c₂ : u₂ ≅ ui ⋙ uΦZ) (M : CX) (e : u₂.obj M ⟶ u₁.obj M)
    (h1 : p₁.app M = pΦ.app M ≫ pi.app (uΦ.obj M) ≫ aZ.map (c₁.inv.app M))
    (h2 : p₂.app M = pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (c₂.inv.app M))
    (h3 : p₂.app M ≫ aZ.map e = p₁.app M) (cmp : uΦZ.obj (ui.obj M) ⟶ ui.obj (uΦ.obj M))
    (hc : cmp = c₂.inv.app M ≫ e ≫ c₁.hom.app M) :
    pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map cmp = pΦ.app M ≫ pi.app (uΦ.obj M) := by
  have h3' : pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (c₂.inv.app M) ≫ aZ.map e =
      pΦ.app M ≫ pi.app (uΦ.obj M) ≫ aZ.map (c₁.inv.app M) := by
    simpa [h1, h2] using h3
  rw [hc, Functor.map_comp, Functor.map_comp, reassoc_of% h3']
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

lemma closedPiece_eq_aux (adj : ui ⊣ ri) (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ)
    (pΦZ : aZ ⟶ uΦZ ⋙ aZ) (c : ri ⋙ aX ≅ aZ)
    (hpi : ∀ M, pi.app M = aX.map (adj.unit.app M) ≫ c.hom.app (ui.obj M))
    (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui)
    (hcomm : ∀ M, pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (cmp.hom.app M) =
      pΦ.app M ≫ pi.app (uΦ.obj M)) (N : CZ) (g : uΦZ.obj N ⟶ N) :
    c.hom.app N ≫ (pΦZ.app N ≫ aZ.map g) ≫ c.inv.app N =
      pΦ.app (ri.obj N) ≫ aX.map (adj.unit.app _ ≫ ri.map (cmp.inv.app (ri.obj N) ≫
        uΦZ.map (adj.counit.app N) ≫ g)) := by
  have hc : c.hom.app N = pi.app (ri.obj N) ≫ aZ.map (adj.counit.app N) := by
    have hn := c.hom.naturality (adj.counit.app N)
    dsimp at hn
    rw [hpi, Category.assoc, ← hn, ← aX.map_comp_assoc, adj.right_triangle_components]
    simp
  have h' : pi.app (ri.obj N) ≫ pΦZ.app (ui.obj (ri.obj N)) =
      pΦ.app (ri.obj N) ≫ pi.app (uΦ.obj (ri.obj N)) ≫ aZ.map (cmp.inv.app (ri.obj N)) := by
    rw [← reassoc_of% (hcomm (ri.obj N)), ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hnat := c.hom.naturality (cmp.inv.app (ri.obj N) ≫ uΦZ.map (adj.counit.app N) ≫ g)
  have hn := pΦZ.naturality (adj.counit.app N)
  dsimp at hnat hn
  simp only [Functor.map_comp, Category.assoc] at hnat
  rw [← cancel_mono (c.hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.map_comp]
  rw [hnat, ← Category.assoc (aX.map _), ← hpi, ← reassoc_of% h', reassoc_of% hn.symm,
    ← reassoc_of% hc]

lemma closedPiece_coeff_unit_aux (adj : ui ⊣ ri) (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui) (K : CX)
    (φ : uΦ.obj K ⟶ K) :
    uΦ.map (adj.unit.app K) ≫ adj.unit.app (uΦ.obj (ri.obj (ui.obj K))) ≫ ri.map (cmp.inv.app (ri.obj (ui.obj K)) ≫
        uΦZ.map (adj.counit.app (ui.obj K)) ≫ cmp.hom.app K ≫ ui.map φ) =
      φ ≫ adj.unit.app K := by
  have hu := adj.unit.naturality (uΦ.map (adj.unit.app K))
  have hu' := adj.unit.naturality φ
  have hc := cmp.inv.naturality (adj.unit.app K)
  dsimp at hu hu' hc
  rw [reassoc_of% hu, ← Functor.map_comp, reassoc_of% hc, ← Functor.map_comp_assoc uΦZ,
    adj.left_triangle_components]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact hu'.symm

variable {CU : Type*} [Category CU] {aU : CU ⥤ D} {uΦU : CU ⥤ CU} {rj : CU ⥤ CX}

lemma openPiece_eq_aux (pΦ : aX ⟶ uΦ ⋙ aX) (pΦU : aU ⟶ uΦU ⋙ aU) (c : rj ⋙ aX ≅ aU)
    (bc : rj ⋙ uΦ ⟶ uΦU ⋙ rj) (N : CU)
    (hB : pΦ.app (rj.obj N) ≫ aX.map (bc.app N) ≫ c.hom.app (uΦU.obj N) =
      c.hom.app N ≫ pΦU.app N) (g : uΦU.obj N ⟶ N) :
    c.hom.app N ≫ (pΦU.app N ≫ aU.map g) ≫ c.inv.app N =
      pΦ.app (rj.obj N) ≫ aX.map (bc.app N ≫ rj.map g) := by
  have hn := c.hom.naturality g
  dsimp at hn
  rw [← Category.assoc, ← Category.assoc, ← hB]
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app]
  simp
