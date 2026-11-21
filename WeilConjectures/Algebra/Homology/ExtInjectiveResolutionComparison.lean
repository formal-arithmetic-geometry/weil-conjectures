/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.Algebra.Homology.ExtInjectiveEdgeQuasiIso

/-! # Computing projective Ext using an injective resolution

Projectively defined `Ext` is the cohomology of `Hom` into an injective resolution,
naturally in the first argument.

## References

* Stacks Project, Tag 0954, proof of Lemma 47.8.2
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite

namespace ModuleCat

/-- The complex `Hom(X,K)` as a functor contravariant in the module `X`. -/
def homComplexDiagram {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj X := (((linearCoyoneda R (ModuleCat.{u} R)).obj X).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K
  map f := (NatTrans.mapHomologicalComplex
    ((linearCoyoneda R (ModuleCat.{u} R)).map f) (ComplexShape.up ℕ)).app K
  map_id X := by
    ext n g
    rfl
  map_comp f g := by
    ext n h
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem isoExt_naturality
    {R : Type u} [CommRing R] {X X' M : ModuleCat.{u} R}
    (g : X' ⟶ X) (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    (f : P'.complex ⟶ P.complex) (hf : f.f 0 ≫ P.π.f 0 = P'.π.f 0 ≫ g) (q : ℕ) :
    ((Ext R (ModuleCat.{u} R) q).flip.obj M).map g.op ≫ (P'.isoExt q M).hom =
      (P.isoExt q M).hom ≫ HomologicalComplex.homologyMap (resolutionHomPrecomp f M) q := by
  let F := ((linearYoneda R (ModuleCat.{u} R)).obj M).rightOp
  have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality g P' P f hf F q
  have h' := congrArg Quiver.Hom.unop h
  dsimp only [unop_comp] at h'
  have hc := congrArg Quiver.Hom.unop
    (HomologicalComplex.homologyOp_hom_naturality (resolutionHomPrecomp f M) q)
  let c := HomologicalComplex.homologyUnop ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    P.complex) q
  let c' := HomologicalComplex.homologyUnop ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    P'.complex) q
  let a := ((F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R)ᵒᵖ (ComplexShape.down ℕ) q).map f).unop
  dsimp only [unop_comp, Quiver.Hom.unop_op] at hc
  change c.hom ≫ a = HomologicalComplex.homologyMap (resolutionHomPrecomp f M) q ≫ c'.hom at hc
  have hc' : a ≫ c'.inv = c.inv ≫ HomologicalComplex.homologyMap (resolutionHomPrecomp f M) q := by
    rw [← cancel_epi c.hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change ((F.leftDerived q).map g).unop ≫
    ((P'.isoLeftDerivedObj F q).inv.unop ≫ c'.inv) =
    ((P.isoLeftDerivedObj F q).inv.unop ≫ c.inv) ≫ _
  rw [← Category.assoc, h', Category.assoc, hc', ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Projectively defined Ext is the cohomology of Hom into an injective
resolution, naturally in the first argument.
-/
theorem nonempty_ext_iso_injectiveResolution_homology
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (E : InjectiveResolution M) (q : ℕ) :
    Nonempty ((Ext R (ModuleCat.{u} R) q).flip.obj M ≅
      homComplexDiagram E.cocomplex ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q) := by
  classical
  let P (X : (ModuleCat.{u} R)ᵒᵖ) := projectiveResolution X.unop
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q
  have hp (X : (ModuleCat.{u} R)ᵒᵖ) :
      IsIso (H.map (resolutionHomProjectiveEdge (P X) E)) := by
    have := resolutionHomProjectiveEdge_quasiIso (P X) E
    change IsIso (HomologicalComplex.homologyMap (resolutionHomProjectiveEdge (P X) E) q)
    infer_instance
  have hi (X : (ModuleCat.{u} R)ᵒᵖ) :
      IsIso (H.map (resolutionHomInjectiveEdge (P X) E)) := by
    have := resolutionHomInjectiveEdge_quasiIso (P X) E
    change IsIso (HomologicalComplex.homologyMap (resolutionHomInjectiveEdge (P X) E) q)
    infer_instance
  let e (X : (ModuleCat.{u} R)ᵒᵖ) := (P X).isoExt q M ≪≫
    asIso (H.map (resolutionHomProjectiveEdge (P X) E)) ≪≫
    (asIso (H.map (resolutionHomInjectiveEdge (P X) E))).symm
  refine ⟨NatIso.ofComponents e ?_⟩
  intro X Y g
  let f := ProjectiveResolution.lift g.unop (P Y) (P X)
  have hf := ProjectiveResolution.lift_commutes_zero g.unop (P Y) (P X)
  have h₁ := isoExt_naturality (M := M) g.unop (P X) (P Y) f hf q
  have h₂ := H.congr_map (projectiveEdge_naturality (P X) (P Y) E f)
  have h₃ := H.congr_map (injectiveEdge_naturality g.unop (P X) (P Y) E f hf)
  simp only [Functor.map_comp] at h₂ h₃
  change ((Ext R (ModuleCat.{u} R) q).flip.obj M).map g ≫
    ((P Y).isoExt q M).hom = ((P X).isoExt q M).hom ≫
      H.map (resolutionHomPrecomp f M) at h₁
  change H.map (resolutionHomInjectiveEdge (P X) E) ≫
    H.map (resolutionHomTotalPrecomp f E.cocomplex) =
      (homComplexDiagram E.cocomplex ⋙ H).map g ≫
        H.map (resolutionHomInjectiveEdge (P Y) E) at h₃
  change _ ≫ (e Y).hom = (e X).hom ≫ _
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  rw [← cancel_mono (H.map (resolutionHomInjectiveEdge (P Y) E))]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← h₃, Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← Category.assoc, h₁, Category.assoc, ← h₂]

end ModuleCat

