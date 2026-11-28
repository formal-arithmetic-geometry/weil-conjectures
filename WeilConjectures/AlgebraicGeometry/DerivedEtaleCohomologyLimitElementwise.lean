/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleComplexPullbackTransport
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import WeilConjectures.AlgebraicGeometry.FixedDerivedCohomologyDiagram

/-!
# Continuity of abelian étale hypercohomology, elementwise

Let `(Uᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps and limit `U`, and let `K ∈ D⁺(S_ét, ℤ)`. This file spells out the continuity of
étale hypercohomology `colimᵢ Hᵠ(Uᵢ, K|_{Uᵢ}) ≅ Hᵠ(U, K|_U)`
(`AlgebraicGeometry.derivedEtaleCohomology_limit`) elementwise, in terms of the restriction maps
`AlgebraicGeometry.Etale.presentationDerivedMap`
(`AlgebraicGeometry.Etale.presentationDerivedMap_isColimit_of_isLimit`).

## References

* Stacks Project, Tag 0GIT
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- **Continuity of abelian étale hypercohomology**, elementwise [Stacks, Tag 0GIT]. Let `(Uᵢ)`
be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine transition
maps and limit `U`, and let `K ∈ D⁺(S_ét, ℤ)`. Then the restriction maps
`Hᵠ(Uᵢ, K|_{Uᵢ}) ⟶ Hᵠ(U, K|_U)` are compatible with the transition maps, every class on `U`
comes from some `Uᵢ`, and a class on `Uᵢ` vanishing on `U` vanishes on some `Uⱼ`. -/
theorem presentationDerivedMap_isColimit_of_isLimit {S : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}))
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℤ) :
    (∀ {i j : I} (g : j ⟶ i),
      presentationDerivedMap (D.map g).left (D.obj i).hom (D.obj j).hom (Over.w _).symm K.obj q ≫
        presentationDerivedMap (c.π.app j).left (D.obj j).hom c.pt.hom (Over.w _).symm K.obj q =
      presentationDerivedMap (c.π.app i).left (D.obj i).hom c.pt.hom (Over.w _).symm K.obj q) ∧
    (∀ x : (cohomology AddCommGrpCat.{u + 1} c.pt.left q).obj
        ((upperStar _ c.pt.hom).mapDerivedCategory.obj K.obj),
      ∃ (i : I) (y : (cohomology AddCommGrpCat.{u + 1} (D.obj i).left q).obj
          ((upperStar _ (D.obj i).hom).mapDerivedCategory.obj K.obj)),
        (presentationDerivedMap (c.π.app i).left (D.obj i).hom c.pt.hom (Over.w _).symm
          K.obj q).hom y = x) ∧
    (∀ (i : I) (y : (cohomology AddCommGrpCat.{u + 1} (D.obj i).left q).obj
        ((upperStar _ (D.obj i).hom).mapDerivedCategory.obj K.obj)),
      (presentationDerivedMap (c.π.app i).left (D.obj i).hom c.pt.hom (Over.w _).symm
          K.obj q).hom y = 0 →
        ∃ (j : I) (g : j ⟶ i),
          (presentationDerivedMap (D.map g).left (D.obj i).hom (D.obj j).hom (Over.w _).symm
            K.obj q).hom y = 0) := by
  let D' := D ⋙ Over.forget S
  let c' := (Over.forget S).mapCone c
  let t : D' ⟶ (Functor.const I).obj S :=
    { app i := (D.obj i).hom
      naturality _ _ f := by simp [D'] }
  have hp (i : I) : c'.π.app i ≫ t.app i = c.pt.hom := Over.w (c.π.app i)
  have : ∀ i, CompactSpace (D'.obj i) := fun i ↦ inferInstanceAs (CompactSpace (D.obj i).left)
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) := fun i ↦
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D'.map f) := fun f ↦
    inferInstanceAs (IsAffineHom (D.map f).left)
  obtain ⟨v⟩ := exists_fixedDerivedCohomologyDiagram S D' c' t c.pt.hom hp K q
  obtain ⟨hv⟩ := derivedEtaleCohomology_limit S D' c' hc t c.pt.hom hp K q v.H v.e v.hm v.B v.eY
    v.hs
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget AddCommGrpCat.{u + 1})
  have hv' := isColimitOfPreserves (forget AddCommGrpCat.{u + 1}) hv
  -- the cocone maps are the restriction maps, up to the isomorphisms `v.e` and `v.eY`
  have hs (i : I) :
      presentationDerivedMap (c.π.app i).left (D.obj i).hom c.pt.hom (Over.w _).symm K.obj q =
        (v.e i).inv ≫ v.B.ι.app (op i) ≫ v.eY.hom := by
    rw [v.hs i]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
    rfl
  have hm {i j : I} (g : j ⟶ i) :
      presentationDerivedMap (D.map g).left (D.obj i).hom (D.obj j).hom (Over.w _).symm K.obj q =
        (v.e i).inv ≫ v.H.map g.op ≫ (v.e j).hom := by
    rw [v.hm g]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
    rfl
  refine ⟨fun {i j} g ↦ ?_, fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · rw [hm, hs, hs, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      ← v.B.w g.op]
    rfl
  · obtain ⟨⟨i⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit hv' (v.eY.inv x)
    refine ⟨i, (v.e i).hom y, ?_⟩
    rw [hs]
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, Iso.hom_inv_id_apply]
    have hy' : (v.B.ι.app (op i)).hom y = v.eY.inv.hom x := hy
    rw [hy', Iso.inv_hom_id_apply]
  · have hz : (v.B.ι.app (op i)).hom ((v.e i).inv.hom y) = (v.B.ι.app (op i)).hom 0 := by
      rw [hs] at hy
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at hy
      rw [map_zero]
      have h := congrArg v.eY.inv.hom hy
      rwa [Iso.hom_inv_id_apply, map_zero] at h
    obtain ⟨⟨j⟩, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hv' _ _).1 hz
    refine ⟨j, g.unop, ?_⟩
    rw [hm]
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    have hg' : (v.H.map g).hom ((v.e i).inv.hom y) = (v.H.map g).hom 0 := hg
    rw [Quiver.Hom.op_unop, hg', map_zero, map_zero]

end AlgebraicGeometry.Etale
