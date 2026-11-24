/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyTriangleLaws
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import all WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Mathlib.CategoryTheory.Presentable.Directed

/-! # Continuity for a supplied fixed-base cohomology cocone

## References

* Stacks Project, Tags 09YQ and 0032
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

/-- The canonical cocone of fixed-base cohomology is a colimit. This asserts only the
universal property for supplied diagram and cocone data; it does not construct them
(Stacks, Tags 09YQ and 0032). -/
theorem nonempty_isColimit_cofiltered_fixed_base_cohomology
    {J : Type u} [SmallCategory J] [IsCofiltered J] {S : Scheme.{u}}
    (D : J ⥤ Scheme.{u}) (π : D ⟶ (Functor.const J).obj S)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (t : c.pt ⟶ S)
    (ht : ∀ j : J, t = c.π.app j ≫ π.app j)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (H : Jᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ j : J, H.obj (op j) ≅
      AddCommGrpCat.of (Sheaf.H (((π.app j)^*[AddCommGrpCat.{u + 1}]).obj G) q))
    (hH : ∀ (j k : J) (f : j ⟶ k), H.map f.op =
      (eH k).hom ≫ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (D.map f) (π.app k) (π.app j)
          (by
            have h := (π.naturality f).symm
            change π.app j ≫ 𝟙 S = D.map f ≫ π.app k at h
            exact (Category.comp_id _).symm.trans h) G q) ≫ (eH j).inv)
    (B : Cocone H)
    (eB : B.pt ≅ AddCommGrpCat.of
      (Sheaf.H (((t)^*[AddCommGrpCat.{u + 1}]).obj G) q))
    (hB : ∀ j : J, B.ι.app (op j) ≫ eB.hom =
      (eH j).hom ≫ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (c.π.app j) (π.app j) t (ht j) G q)) :
    Nonempty (IsColimit B) := by
  obtain ⟨I, hI, hdir, hne, R, hR⟩ := IsFiltered.exists_directed Jᵒᵖ
  let D' := R.leftOp ⋙ D
  let (i : Iᵒᵖ) : CompactSpace (D'.obj i) := inferInstanceAs
    (CompactSpace (D.obj (R.obj i.unop).unop))
  let (i : Iᵒᵖ) : QuasiSeparatedSpace (D'.obj i) := inferInstanceAs
    (QuasiSeparatedSpace (D.obj (R.obj i.unop).unop))
  let (i j : Iᵒᵖ) (f : i ⟶ j) : IsAffineHom (D'.map f) := inferInstanceAs
    (IsAffineHom (D.map (R.map f.unop).unop))
  let c' := c.whisker R.leftOp
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv R.leftOp c).symm hc
  let v := fun i : I ↦ π.app (R.obj i).unop
  have wv : ∀ (i j : I) (f : i ⟶ j), v j = D'.map f.op ≫ v i := by
    intro i j f
    simp [v, D']
  have wLimit : ∀ i : I, t = c'.π.app (op i) ≫ v i := fun i ↦ ht (R.obj i).unop
  let H' := R ⋙ H
  let B' := B.whisker R
  suffices h : Nonempty (IsColimit B') from
    h.map (Functor.Final.isColimitWhiskerEquiv R B)
  set_option backward.isDefEq.respectTransparency true in
    apply continuity_constant_pullback D' c' hc' S G v wv t wLimit q H'
      (fun i ↦ eH (R.obj i).unop) ?_ B' eB ?_
    · intro i j f
      simpa only [H', D', v, cohomologyTriangleMap, AddCommGrpCat.ofHom_comp,
        Category.assoc, Functor.comp_map, Functor.leftOp_map, Quiver.Hom.op_unop,
        Functor.comp_obj, Opposite.op_unop]
        using hH (R.obj j).unop (R.obj i).unop (R.map f).unop
    · intro i
      simpa only [B', c', v, cohomologyTriangleMap, AddCommGrpCat.ofHom_comp,
        Category.assoc, Cocone.whisker_ι, Cone.whisker_π, Opposite.op_unop,
        Functor.whiskerLeft_app, Functor.leftOp_obj]
        using hB (R.obj i).unop

end AlgebraicGeometry.Etale
