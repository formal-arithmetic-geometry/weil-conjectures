/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.PairHenselization
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Preserves.Over

/-! # A directed ring presentation of a closed affine henselian neighborhood

Source: Stacks Project, Tags 0A51, 0A02, and 0032.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A closed affine pair has a henselian neighborhood presented by a small directed
colimit of rings whose spectra are etale over the original scheme.

Source: Stacks Project, Tags 0A51 (affine proof), 0A02 (henselization of pairs),
and 0032 (directed presentation of a filtered category). -/
theorem Etale.affine_closed_henselian_ring_presentation
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (_ : IsColimit c)
      (K : Ideal c.pt) (_ : HenselianRing c.pt K)
      (t : Spec c.pt ⟶ X) (e : Z ≅ Spec (.of (c.pt ⧸ K))),
      i = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ t ∧
      ∃ v : ∀ a : I, Spec (R.obj a) ⟶ X,
        (∀ (a b : I) (f : a ⟶ b), v b = Spec.map (R.map f) ≫ v a) ∧
        (∀ a : I, t = Spec.map (c.ι.app a) ≫ v a) ∧
        (∀ a : I, Etale (v a)) := by
  classical
  let B := Γ(X, ⊤)
  let x : X ≅ Spec B := X.isoSpec
  obtain ⟨L, z, hz⟩ := (IsClosedImmersion.Spec_iff (f := i ≫ x.hom)).mp inferInstance
  let P : ObjectProperty (Under B) := fun C ↦
    Etale (Spec.map C.hom) ∧
      Function.Bijective (Ideal.quotientMap (L.map C.hom.hom) C.hom.hom
        Ideal.le_comap_map)
  obtain ⟨hsmall, hfiltered, c₀, ⟨hc₀⟩, hH, hq⟩ := RingTheory.pair_henselization B L
  let : EssentiallySmall.{u} P.FullSubcategory := hsmall
  let : IsFiltered P.FullSubcategory := hfiltered
  let J := SmallModel.{u} P.FullSubcategory
  let E : J ⥤ P.FullSubcategory := (equivSmallModel P.FullSubcategory).inverse
  let : IsFiltered J := IsFiltered.of_equivalence (equivSmallModel P.FullSubcategory)
  obtain ⟨I, horder, hdirected, hnonempty, F, hfinal⟩ := IsFiltered.exists_directed J
  let := horder
  let := hfinal
  let G : I ⥤ P.FullSubcategory := F ⋙ E
  let D := P.ι ⋙ Under.forget B
  let c := (Under.forget B).mapCocone c₀
  have hc : IsColimit c := isColimitOfPreserves (Under.forget B) hc₀
  let R := G ⋙ D
  let d : Cocone R := c.whisker G
  have hd : IsColimit d := (Functor.Final.isColimitWhiskerEquiv G c).symm hc
  let K := L.map c₀.pt.hom.hom
  let q := Ideal.quotientMap K c₀.pt.hom.hom Ideal.le_comap_map
  let eq : CommRingCat.of (B ⧸ L) ≅ CommRingCat.of (c₀.pt.right ⧸ K) :=
    (RingEquiv.ofBijective q hq).toCommRingCatIso
  let e : Z ≅ Spec (CommRingCat.of (d.pt ⧸ K)) :=
    z ≪≫ Scheme.Spec.mapIso eq.op.symm
  let t : Spec d.pt ⟶ X := Spec.map c₀.pt.hom ≫ x.inv
  refine ⟨I, horder.toPreorder, hdirected, hnonempty, R, d, hd, K, hH, t, e, ?_, ?_⟩
  · have hs : c₀.pt.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk K) =
        CommRingCat.ofHom (Ideal.Quotient.mk L) ≫ eq.hom := by
      ext b
      change Ideal.Quotient.mk K (c₀.pt.hom.hom b) = q (Ideal.Quotient.mk L b)
      exact Ideal.quotientMap_mk.symm
    have hs' : c₀.pt.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk K) ≫ eq.inv =
        CommRingCat.ofHom (Ideal.Quotient.mk L) := by
      rw [← Category.assoc, hs]
      simp
    dsimp [e, t]
    simp only [Iso.op_inv, Quiver.Hom.unop_op, Category.assoc]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hs']
    rw [← Category.assoc, ← hz]
    simp
  · refine ⟨fun a ↦ Spec.map (G.obj a).obj.hom ≫ x.inv, ?_, ?_, ?_⟩
    · intro a b f
      have hw := (G.map f).hom.w
      dsimp [R, D]
      rw [← Category.assoc, ← Spec.map_comp, hw]
    · intro a
      have hw := (c₀.ι.app (G.obj a)).w
      change (G.obj a).obj.hom ≫ (c₀.ι.app (G.obj a)).right = c₀.pt.hom at hw
      change Spec.map c₀.pt.hom ≫ x.inv =
        Spec.map (c₀.ι.app (G.obj a)).right ≫ Spec.map (G.obj a).obj.hom ≫ x.inv
      rw [← Category.assoc, ← Spec.map_comp, hw]
    · intro a
      have : Etale (Spec.map (G.obj a).obj.hom) := (G.obj a).property.1
      infer_instance

end AlgebraicGeometry
