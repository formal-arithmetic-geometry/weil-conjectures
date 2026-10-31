/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient comparisons on ring colimits

Source: the universal-property argument for quotient colimits in ILO XX 4.4,
pp.373--374 (blueprint: lem-per-colimit-quotient-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

private theorem hom_ext_of_quotient_surjective
    {R T H : Type u} [CommRing R] [CommRing T] [CommRing H]
    (f : R →+* T) (L : Ideal T)
    (hf : Function.Surjective ((Ideal.Quotient.mk L).comp f))
    (a b : T →+* H) (ha : L ≤ RingHom.ker a) (hb : L ≤ RingHom.ker b)
    (hab : a.comp f = b.comp f) : a = b := by
  let aq := Ideal.Quotient.lift L a ha
  let bq := Ideal.Quotient.lift L b hb
  have he : aq = bq := by
    apply RingHom.ext
    intro z
    obtain ⟨x, rfl⟩ := hf z
    exact DFunLike.congr_fun hab x
  calc
    a = aq.comp (Ideal.Quotient.mk L) := rfl
    _ = bq.comp (Ideal.Quotient.mk L) :=
      congrArg (fun h : T ⧸ L →+* H ↦ h.comp (Ideal.Quotient.mk L)) he
    _ = b := rfl

/-- A comparison of ring diagrams which is bijective after quotienting at every stage
is bijective on the corresponding colimit quotient. The structural maps from the base
are required to induce the specified single map to the source colimit; connectedness
of the index is one way to check this condition. No filteredness is needed here.

Source: ILO XX 4.4, pp.373--374, passage to colimits of congruences
(blueprint: lem-per-colimit-quotient-comparison).

Proof: take the inverses of the stage quotient maps, and compose them with the source
coprojections modulo the base ideal. These maps kill the target stage ideals. They form
a cocone: naturality can be checked on the source stage images, which surject onto the
target stage quotients. Descend this cocone to the target colimit. Its composite with
the comparison is the source quotient map, so it kills the extended source ideal and
descends to the target colimit quotient. Both inverse identities can be checked on the
original coprojections and then on quotient representatives. This also applies to zero rings
and to ideals which are not finitely generated. -/
theorem colimit_quotientMap_bijective
    {D : Type v} [Category.{w} D]
    (A : CommRingCat.{u}) (K : Ideal A)
    (F G : D ⥤ CommRingCat.{u}) [HasColimit F] [HasColimit G]
    (b : (Functor.const D).obj A ⟶ F)
    (bB : A ⟶ colimit F)
    (hb : ∀ j : D, b.app j ≫ colimit.ι F j = bB)
    (η : F ⟶ G)
    (hη : ∀ j, Function.Bijective
      (Ideal.quotientMap ((K.map (b.app j).hom).map (η.app j).hom)
        (η.app j).hom Ideal.le_comap_map)) :
    Function.Bijective
      (Ideal.quotientMap ((K.map bB.hom).map (colimMap η).hom)
        (colimMap η).hom Ideal.le_comap_map) := by
  classical
  have hb' (j : D) : (colimit.ι F j).hom.comp (b.app j).hom = bB.hom :=
    congrArg Hom.hom (hb j)
  have hbmap {j k : D} (f : j ⟶ k) : b.app j ≫ F.map f = b.app k := by
    have he := b.naturality f
    change 𝟙 A ≫ b.app k = b.app j ≫ F.map f at he
    simpa only [Category.id_comp] using he.symm
  let B : CommRingCat.{u} := colimit F
  let C : CommRingCat.{u} := colimit G
  let IB := K.map bB.hom
  let uBC := (colimMap η).hom
  let IC := IB.map uBC
  let q : B ⧸ IB →+* C ⧸ IC := Ideal.quotientMap IC uBC Ideal.le_comap_map
  let LF (j : D) := K.map (b.app j).hom
  let LG (j : D) := (LF j).map (η.app j).hom
  let e (j : D) : F.obj j ⧸ LF j ≃+* G.obj j ⧸ LG j :=
    RingEquiv.ofBijective (Ideal.quotientMap (LG j) (η.app j).hom
      Ideal.le_comap_map) (hη j)
  have hF (j : D) : LF j ≤ IB.comap (colimit.ι F j).hom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hb']
  let m (j : D) : F.obj j ⧸ LF j →+* B ⧸ IB :=
    Ideal.quotientMap IB (colimit.ι F j).hom (hF j)
  let t (j : D) : G.obj j →+* B ⧸ IB :=
    ((m j).comp (e j).symm.toRingHom).comp (Ideal.Quotient.mk (LG j))
  have ht (j : D) : (t j).comp (η.app j).hom =
      (Ideal.Quotient.mk IB).comp (colimit.ι F j).hom := by
    ext x
    change m j ((e j).symm (e j (Ideal.Quotient.mk (LF j) x))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  have hkill (j : D) : LG j ≤ RingHom.ker (t j) := by
    intro x hx
    change m j ((e j).symm (Ideal.Quotient.mk (LG j) x)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero, map_zero]
  have hs (j : D) : Function.Surjective
      ((Ideal.Quotient.mk (LG j)).comp (η.app j).hom) := by
    intro z
    obtain ⟨y, hy⟩ := (hη j).2 z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hy⟩
  have hG {j k : D} (f : j ⟶ k) :
      (LG j).map (G.map f).hom ≤ LG k := by
    dsimp only [LG, LF]
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_map]
    have he : (G.map f).hom.comp ((η.app j).hom.comp (b.app j).hom) =
        (η.app k).hom.comp (b.app k).hom := by
      change ((b.app j ≫ η.app j) ≫ G.map f).hom = (b.app k ≫ η.app k).hom
      rw [Category.assoc, ← η.naturality, ← Category.assoc, hbmap]
    rw [RingHom.comp_assoc, he]
  let c : Cocone G :=
    { pt := .of (B ⧸ IB)
      ι :=
        { app := fun j ↦ ofHom (t j)
          naturality := by
            intro j k f
            apply hom_ext
            change (t k).comp (G.map f).hom = t j
            apply hom_ext_of_quotient_surjective (η.app j).hom (LG j) (hs j)
            · intro x hx
              exact hkill k (hG f (Ideal.mem_map_of_mem (G.map f).hom hx))
            · exact hkill j
            · rw [RingHom.comp_assoc, ← hom_comp, ← η.naturality, hom_comp,
                ← RingHom.comp_assoc, ht, RingHom.comp_assoc, ← hom_comp, colimit.w, ht] } }
  let vCB : C →+* B ⧸ IB := (colimit.desc G c).hom
  have hv (j : D) : vCB.comp (colimit.ι G j).hom = t j :=
    congrArg Hom.hom (colimit.ι_desc c j)
  have hleft : vCB.comp uBC = Ideal.Quotient.mk IB := by
    suffices h : ofHom (vCB.comp uBC) = ofHom (Ideal.Quotient.mk IB) from
      congrArg Hom.hom h
    apply colimit.hom_ext
    intro j
    apply hom_ext
    change vCB.comp (uBC.comp (colimit.ι F j).hom) =
      (Ideal.Quotient.mk IB).comp (colimit.ι F j).hom
    rw [← hom_comp, ι_colimMap, hom_comp, ← RingHom.comp_assoc, hv, ht]
  have hIC : IC ≤ RingHom.ker vCB := by
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, hleft, Ideal.mk_ker]
  let v : C ⧸ IC →+* B ⧸ IB := Ideal.Quotient.lift IC vCB hIC
  have hvq : v.comp q = RingHom.id (B ⧸ IB) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    exact DFunLike.congr_fun hleft x
  have hright : q.comp vCB = Ideal.Quotient.mk IC := by
    suffices h : ofHom (q.comp vCB) = ofHom (Ideal.Quotient.mk IC) from
      congrArg Hom.hom h
    apply colimit.hom_ext
    intro j
    apply hom_ext
    change (q.comp vCB).comp (colimit.ι G j).hom =
      (Ideal.Quotient.mk IC).comp (colimit.ι G j).hom
    apply hom_ext_of_quotient_surjective (η.app j).hom (LG j) (hs j)
    · intro x hx
      change q ((vCB.comp (colimit.ι G j).hom) x) = 0
      rw [hv]
      exact (congrArg q (hkill j hx)).trans (map_zero q)
    · intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hmaps : (LG j).map (colimit.ι G j).hom ≤ IC := by
        dsimp only [LG, LF, IC, IB]
        rw [Ideal.map_map, Ideal.map_map, Ideal.map_map]
        have he : (colimit.ι G j).hom.comp
            ((η.app j).hom.comp (b.app j).hom) = uBC.comp bB.hom := by
          rw [← RingHom.comp_assoc, ← hom_comp, ← ι_colimMap, hom_comp,
            RingHom.comp_assoc, hb']
        rw [RingHom.comp_assoc, he]
      exact hmaps (Ideal.mem_map_of_mem (colimit.ι G j).hom hx)
    · ext x
      change q (vCB ((colimit.ι G j).hom ((η.app j).hom x))) =
        Ideal.Quotient.mk IC ((colimit.ι G j).hom ((η.app j).hom x))
      have hvi : vCB ((colimit.ι G j).hom ((η.app j).hom x)) =
          Ideal.Quotient.mk IB ((colimit.ι F j).hom x) :=
        (DFunLike.congr_fun (hv j) ((η.app j).hom x)).trans (DFunLike.congr_fun (ht j) x)
      rw [hvi]
      change Ideal.Quotient.mk IC (uBC ((colimit.ι F j).hom x)) = _
      exact congrArg (Ideal.Quotient.mk IC)
        (congrArg (fun f : F.obj j ⟶ C ↦ f.hom x) (ι_colimMap η j))
  have hqv : q.comp v = RingHom.id (C ⧸ IC) := by
    apply Ideal.Quotient.ringHom_ext
    exact hright
  exact ⟨Function.HasLeftInverse.injective ⟨v, DFunLike.congr_fun hvq⟩,
    Function.HasRightInverse.surjective ⟨v, DFunLike.congr_fun hqv⟩⟩

end CommRingCat
