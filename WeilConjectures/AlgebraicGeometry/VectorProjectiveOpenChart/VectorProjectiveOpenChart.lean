/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
import WeilConjectures.AlgebraicGeometry.VectorProjectiveCompletion.VectorProjectiveDehomogenization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.AlgebraicGeometry.Cover.Directed
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded

/-! # The vector chart in any symmetric-algebra projective realization

Source: Stacks Project, Constructions, Tags 01OA and 01NG; the affine chart and
cover-gluing arguments of `VectorProjectivePresentation` and `VectorProjectiveCompletion`.
(blueprint: lem-pur-vector-projective-open-chart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pointwise
namespace AlgebraicGeometry.VectorProjectiveOpenChart
open VectorProjectiveCompletion

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private def inverseAffineCover {X S : Scheme.{u}} (p : X ⟶ S) : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun V : S.affineOpens ↦ p ⁻¹ᵁ V.1) (by
    change (⨆ V : S.affineOpens, p ⁻¹ᵁ V.1) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    rfl)
private instance inverseAffineCoverPreorder {X S : Scheme.{u}} (p : X ⟶ S) :
    Preorder (inverseAffineCover p).I₀ := inferInstanceAs (Preorder S.affineOpens)
private instance inverseAffineCoverDirected {X S : Scheme.{u}} (p : X ⟶ S) :
    (inverseAffineCover p).LocallyDirected where
  trans {V W} h := X.homOfLE (p.preimage_mono (leOfHom h))
  trans_id V := by
    apply (cancel_mono (p ⁻¹ᵁ V.1).ι).mp
    change _ = 𝟙 _ ≫ _
    simp
  trans_comp h k := by apply (cancel_mono (p ⁻¹ᵁ _).ι).mp; simp
  w h := by simp [inverseAffineCover]
  directed {V W} z := by
    let z₀ : X := (pullback.fst (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι ≫ (p ⁻¹ᵁ V.1).ι) z
    have hV : p z₀ ∈ V.1 := (pullback.fst (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι z).2
    have hW : p z₀ ∈ W.1 := by
      dsimp only [z₀]
      rw [pullback.condition]
      exact (pullback.snd (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι z).2
    obtain ⟨U, hUV, hUW, hzU⟩ :=
      Scheme.GradedAlgebraData.exists_affineOpens_le V W (p z₀) hV hW
    refine ⟨U, homOfLE hUV, homOfLE hUW, ⟨z₀, hzU⟩, ?_⟩
    apply (pullback.fst (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι ≫
      (p ⁻¹ᵁ V.1).ι).isOpenEmbedding.injective
    change (pullback.lift (X.homOfLE (p.preimage_mono hUV))
      (X.homOfLE (p.preimage_mono hUW)) _ ≫
      pullback.fst (p ⁻¹ᵁ V.1).ι (p ⁻¹ᵁ W.1).ι ≫ (p ⁻¹ᵁ V.1).ι)
        ⟨z₀, hzU⟩ = z₀
    rw [pullback.lift_fst_assoc, Scheme.homOfLE_ι]
    rfl
  property_trans h := by infer_instance

private theorem glue_affine_charts {X S Y : Scheme.{u}} (p : X ⟶ S) (r : Y ⟶ S)
    (f : ∀ V : S.affineOpens, (p ⁻¹ᵁ V.1).toScheme ⟶ Y)
    (hf : ∀ {U V : S.affineOpens} (h : U ≤ V),
      X.homOfLE (p.preimage_mono h) ≫ f V = f U)
    (hover : ∀ V : S.affineOpens, f V ≫ r = (p ⁻¹ᵁ V.1).ι ≫ p)
    (hopen : ∀ V : S.affineOpens, IsOpenImmersion (f V)) :
    ∃ j : X ⟶ Y, IsOpenImmersion j ∧ j ≫ r = p ∧
      (∀ V : S.affineOpens, (p ⁻¹ᵁ V.1).ι ≫ j = f V) ∧
      (∀ j' : X ⟶ Y, (∀ V : S.affineOpens, (p ⁻¹ᵁ V.1).ι ≫ j' = f V) → j' = j) := by
  let C := inverseAffineCover p
  let j := C.glueMorphismsOfLocallyDirected f (fun h ↦ hf (leOfHom h))
  have hj (V : S.affineOpens) : (p ⁻¹ᵁ V.1).ι ≫ j = f V :=
    C.map_glueMorphismsOfLocallyDirected f _ V
  have hjr : j ≫ r = p := by
    apply C.hom_ext
    intro V
    change (p ⁻¹ᵁ V.1).ι ≫ j ≫ r = (p ⁻¹ᵁ V.1).ι ≫ p
    rw [← Category.assoc, hj, hover]
  have hinj : Function.Injective j := by
    intro x y hxy
    have hbase : p x = p y := by
      rw [← hjr]
      simpa only [Scheme.Hom.comp_apply] using congrArg r hxy
    obtain ⟨V, hV⟩ := Scheme.GradedAlgebraData.exists_affineOpens_mem (p x)
    let xv : (p ⁻¹ᵁ V.1).toScheme := ⟨x, hV⟩
    let yv : (p ⁻¹ᵁ V.1).toScheme := ⟨y, by change p y ∈ V.1; rw [← hbase]; exact hV⟩
    have hfv : f V xv = f V yv := by
      rw [← hj]
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using hxy
    have := hopen V
    exact congrArg Subtype.val ((f V).isOpenEmbedding.injective hfv)
  refine ⟨j, IsOpenImmersion.of_openCover_source j C hinj ?_, hjr, hj, ?_⟩
  · intro V
    change IsOpenImmersion ((p ⁻¹ᵁ V.1).ι ≫ j)
    rw [hj]
    exact hopen V
  · intro j' hj'
    apply C.hom_ext
    intro V
    exact (hj' V).trans (hj V).symm


/-- The relative spectrum of Sym(F) is an open subscheme over S of every specified
symmetric-algebra realization of Proj Sym(O plus F), including rank zero.
Source: Stacks Project, Constructions, Tags 01OA and 01NG; blueprint
`def-pur-vector-bundle-thom-class`, projective completion paragraph.
(blueprint: lem-pur-vector-projective-open-chart).

Proof: evaluation of the product of module sheaves gives R times F(U), naturally
in affine U. Transport the given graded section equivalences along this product
comparison to obtain a presentation of Sym(R plus F(U)). Apply the existing
frame-independent dehomogenization theorem to that presentation. Composing its
Spec chart with the vector-bundle affine chart gives an open immersion over U.
The restriction identities glue these maps over the locally directed affine-basis
cover. Equality over S reduces injectivity to injectivity on one affine chart;
the source-cover criterion therefore makes the glued map an open immersion. -/
theorem exists_openChartForRealization (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (A : S.SymmetricGradedAlgebraData (SheafOfModules.unit S.ringCatSheaf ⨯ F)) :
    ∃ j : VectorBundleZeroSection.scheme S d F ⟶ A.data.relProj,
      IsOpenImmersion j ∧ j ≫ A.data.relProjHom = VectorBundleZeroSection.π S d F := by
  classical
  let P := makePresentation S F A
  obtain ⟨ht, a, hgen, hcoeff, hrest⟩ := exists_affineDehomogenization S F P
  have hscalar (V : S.affineOpens) (r : Γ(S, V.1)) :
      (a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) r)).val =
        algebraMap (P.algebra.obj V) (Localization.Away (t P V))
          (algebraMap Γ(S, V.1) (P.algebra.obj V) r) := by
    rw [hcoeff, HomogeneousLocalization.val_algebraMap,
      Localization.mk_one_eq_algebraMap]
  have hascalar (V : S.affineOpens) (r : Γ(S, V.1)) :
      a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) r) =
        algebraMap Γ(S, V.1)
          (HomogeneousLocalization.Away (P.algebra.grading V) (t P V)) r := by
    apply HomogeneousLocalization.val_injective
    rw [hscalar, HomogeneousLocalization.val_algebraMap,
      Localization.mk_one_eq_algebraMap]
  have hchartIso (V : S.affineOpens) : IsIso
      (Spec.map (CommRingCat.ofHom (a V).symm.toRingHom)) := by
    have : IsIso (CommRingCat.ofHom (a V).symm.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (a V).symm.bijective
    infer_instance
  have hchartOpen (V : S.affineOpens) : IsOpenImmersion (chartMap P ht a V) := by
    have := hchartIso V
    unfold chartMap
    infer_instance
  have hchartOver (V : S.affineOpens) : chartMap P ht a V ≫ P.algebra.relProjHom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1)
        (SymmetricAlgebraSheaf.sections F (op V.1)))) ≫ V.2.isoSpec.inv ≫ V.1.ι := by
    simp only [chartMap, Category.assoc, P.algebra.relProjι_relProjHom]
    change Spec.map _ ≫ Proj.awayι _ _ _ _ ≫
      (Proj.toSpecOfAlgebra (P.algebra.grading V) ≫ V.2.isoSpec.inv) ≫ V.1.ι = _
    rw [Category.assoc, Proj.awayι_toSpecOfAlgebra_assoc, ← Spec.map_comp_assoc]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (a V).symm_apply_eq.mpr (hascalar V r).symm
  let p := VectorBundleZeroSection.π S d F
  let X := VectorBundleZeroSection.scheme S d F
  let localMap (V : S.affineOpens) : (p ⁻¹ᵁ V.1).toScheme ⟶ P.algebra.relProj :=
    VectorBundleZeroSection.affineChart S d F V ≫ chartMap P ht a V
  have hlocal (V : S.affineOpens) : IsOpenImmersion (localMap V) := by
    have := hchartOpen V
    have := (VectorBundleZeroSection.affineChart_spec S d F V).1
    dsimp only [localMap]
    infer_instance
  have hover (V : S.affineOpens) : localMap V ≫ P.algebra.relProjHom =
      (p ⁻¹ᵁ V.1).ι ≫ p := by
    dsimp only [localMap]
    rw [Category.assoc, hchartOver]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ V.1.ι)
        (VectorBundleZeroSection.affineChart_spec S d F V).2.1 |>.trans
          (morphismRestrict_ι p V.1)
  have hcompat {U V : S.affineOpens} (h : U ≤ V) :
      X.homOfLE (p.preimage_mono h) ≫ localMap V = localMap U := by
    have he := VectorBundleZeroSection.affineChart_naturality S d F U V h
    simp only [Scheme.Hom.resLE_id] at he
    dsimp only [localMap]
    rw [← Category.assoc, he, Category.assoc, hrest U V h]
  obtain ⟨j, hjopen, hjover, _, _⟩ :=
    glue_affine_charts p P.algebra.relProjHom localMap hcompat hover hlocal
  exact ⟨j, hjopen, hjover⟩

end AlgebraicGeometry.VectorProjectiveOpenChart
