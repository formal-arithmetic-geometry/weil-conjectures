/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.RelativeGradedLineMap.RelativeGradedLineMap
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
import WeilConjectures.AlgebraicGeometry.PullbackTensorUnitSection
import all WeilConjectures.AlgebraicGeometry.BoundaryCoefficientDegreeSplit
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.RelativeGradedLineMap.RelativeGradedMapAffineChart
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.Proj.ProjCanonicalMapTwistComparison
import WeilConjectures.AlgebraicGeometry.Proj.ProjQcOpenTwistAmple
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.Ample.AmpleRestrictClosedImmersion

/-!
# Graded immersion criterion for ampleness

Source: Stacks Project, Morphisms, Tag 01VJ, implication (6) implies (1), with
Constructions, Tag 01O9 (blueprint: lem-trf-graded-immersion-ample-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem boundary_adj_eq {X Y : Scheme.{u}} (j : X ⟶ Y) :
    Classical.choose (exists_tensorPullbackAdjunction j) =
      tensorPullbackSectionAdjunction j := by
  apply (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction j)).2
  intro M U s
  exact (Classical.choose_spec (exists_tensorPullbackAdjunction j)) M (op U) s

private theorem boundary_unit_transport {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((boundaryPullbackComparison j).app M).hom.app (j ⁻¹ᵁ U)
      (((tensorPullbackSectionAdjunction j).unit.app M).app U s) =
        pullbackSection j s := by
  unfold boundaryPullbackComparison
  rw [boundary_adj_eq]
  exact congrArg (fun f ↦ f.app U s)
    ((tensorPullbackSectionAdjunction j).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction j) M)

private theorem evaluate_add
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules}
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    {W : Scheme.{u}} (j : W ⟶ Z) (V : S.affineOpens)
    (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (n : ℕ) (a b : A.grading V n) :
    ψ.evaluate j V q n (a + b) = ψ.evaluate j V q n a + ψ.evaluate j V q n b := by
  simp only [RelativeGradedLineMap.evaluate, map_add]

private theorem evaluate_one
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules}
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    {W : Scheme.{u}} (j : W ⟶ Z) (V : S.affineOpens)
    (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1)) :
    ψ.evaluate j V q 0 ⟨1, SetLike.one_mem_graded (A.grading V)⟩ =
      unitSectionsEquiv ⊤ 1 := by
  unfold RelativeGradedLineMap.evaluate
  rw [ψ.one]
  change (pullbackObjUnitIso j).hom.app ⊤
    (((boundaryPullbackComparison j).app _).hom.app ⊤
      (((tensorPullback j).obj _).presheaf.map (homOfLE q).op
        (((tensorPullbackSectionAdjunction j).unit.app _).app _
          (unitSectionsEquiv _ 1)))) = _
  have hc := Hom.app_presheaf_map
    ((boundaryPullbackComparison j).app (unit Z)).hom (homOfLE q)
    (((tensorPullbackSectionAdjunction j).unit.app (unit Z)).app (h ⁻¹ᵁ V.1)
      (unitSectionsEquiv _ 1))
  rw [hc, boundary_unit_transport j (unit Z)]
  have hu := Hom.app_presheaf_map (pullbackObjUnitIso j).hom (homOfLE q)
    (pullbackSection j (unitSectionsEquiv (h ⁻¹ᵁ V.1) 1))
  rw [hu]
  change (unit W).presheaf.map (homOfLE q).op
    ((pullbackObjUnitIso j).hom.app (j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
      (pullbackSection j (M := unit Z) (1 : Γ(Z, h ⁻¹ᵁ V.1)))) = _
  rw [pullbackObjUnitIso_hom_app_pullbackSection]
  change W.presheaf.map (homOfLE q).op (j.app (h ⁻¹ᵁ V.1) 1) = 1
  rw [map_one, map_one]

private theorem boundary_tensor_unit {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M N : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (boundaryPullbackTensorIso j M N).hom.app (j ⁻¹ᵁ U)
      (((tensorPullbackSectionAdjunction j).unit.app (M ⊗ N)).app U
        (tmulSection s t)) =
      tmulSection (X := X) (M := (tensorPullback j).obj M)
        (N := (tensorPullback j).obj N)
        (((tensorPullbackSectionAdjunction j).unit.app M).app U s)
        (((tensorPullbackSectionAdjunction j).unit.app N).app U t) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((((boundaryPullbackComparison j).app M).hom ⊗ₘ
      ((boundaryPullbackComparison j).app N).hom).app (j ⁻¹ᵁ U))).1
  rw [tensorHom_app_tmulSection, boundary_unit_transport, boundary_unit_transport]
  have hc : (boundaryPullbackTensorIso j M N).hom ≫
      (((boundaryPullbackComparison j).app M).hom ⊗ₘ
        ((boundaryPullbackComparison j).app N).hom) =
      ((boundaryPullbackComparison j).app (M ⊗ N)).hom ≫
        Functor.OplaxMonoidal.δ (pullback j) M N := by
    simp only [boundaryPullbackTensorIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id, tensorHom_id,
      id_whiskerRight, Category.comp_id, Functor.Monoidal.μIso_inv]
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, hc, Hom.comp_app,
    ConcreteCategory.comp_apply, boundary_unit_transport]
  exact pullback_δ_app_unit_tmulSection j M N U s t

private theorem power_add_hom {X Y : Scheme.{u}} (j : X ⟶ Y)
    (L : Y.Modules) (m n : ℕ) :
    (tensorPullback j).map (L.tensorPowAddIso m n).inv ≫
      (boundaryPullbackPowIso j L (m + n)).hom =
    (boundaryPullbackTensorIso j (L.tensorPow m) (L.tensorPow n)).hom ≫
      ((boundaryPullbackPowIso j L m).hom ⊗ₘ
        (boundaryPullbackPowIso j L n).hom) ≫
      (((tensorPullback j).obj L).tensorPowAddIso m n).inv := by
  apply (cancel_epi (((boundaryPullbackPowIso j L m).inv ⊗ₘ
    (boundaryPullbackPowIso j L n).inv) ≫
    (boundaryPullbackTensorIso j (L.tensorPow m) (L.tensorPow n)).inv)).mp
  simp only [Category.assoc]
  rw [reassoc_of% pullback_power_add]
  simp only [Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]

private theorem evaluate_mul
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules}
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    {W : Scheme.{u}} (j : W ⟶ Z) (V : S.affineOpens)
    (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (m n : ℕ) (a : A.grading V m) (b : A.grading V n) :
    ψ.evaluate j V q (m + n)
      ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      (((tensorPullback j).obj L).tensorPowAddIso m n).inv.app ⊤
        (tmulSection (ψ.evaluate j V q m a) (ψ.evaluate j V q n b)) := by
  unfold RelativeGradedLineMap.evaluate
  rw [ψ.mul]
  have hn := congrArg (fun f ↦ f.app (h ⁻¹ᵁ V.1)
    (tmulSection (ψ.component V m a) (ψ.component V n b)))
    ((tensorPullbackSectionAdjunction j).unit_naturality
      (L.tensorPowAddIso m n).inv)
  change (((tensorPullback j).map (L.tensorPowAddIso m n).inv).app
    (j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (((tensorPullbackSectionAdjunction j).unit.app _).app _
      (tmulSection (ψ.component V m a) (ψ.component V n b)))) = _ at hn
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hn
  refine (congrArg (fun s ↦ (boundaryPullbackPowIso j L (m + n)).hom.app ⊤
    (((tensorPullback j).obj (L.tensorPow (m + n))).presheaf.map
      (homOfLE q).op s)) hn.symm).trans ?_
  have hrmap := Hom.app_presheaf_map
    ((tensorPullback j).map (L.tensorPowAddIso m n).inv) (homOfLE q)
    (((tensorPullbackSectionAdjunction j).unit.app
      (L.tensorPow m ⊗ L.tensorPow n)).app (h ⁻¹ᵁ V.1)
        (tmulSection (ψ.component V m a) (ψ.component V n b)))
  rw [← hrmap]
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, power_add_hom]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  have hc := Hom.app_presheaf_map
    (boundaryPullbackTensorIso j (L.tensorPow m) (L.tensorPow n)).hom (homOfLE q)
    (((tensorPullbackSectionAdjunction j).unit.app
      (L.tensorPow m ⊗ L.tensorPow n)).app (h ⁻¹ᵁ V.1)
        (tmulSection (ψ.component V m a) (ψ.component V n b)))
  rw [hc, boundary_tensor_unit j (L.tensorPow m) (L.tensorPow n)]
  rw [tmulSection_map, tensorHom_app_tmulSection]
  rfl

private theorem exists_graded_map
    {R : Type u} [CommRing R] (𝒜 : ℕ → AddSubgroup R) [GradedRing 𝒜]
    {T : Scheme.{u}} (M : T.Modules) [M.IsInvertible]
    (f : ∀ n, 𝒜 n →+ SectionRingComponent M n)
    (hone : f 0 ⟨1, SetLike.one_mem_graded 𝒜⟩ = unitSectionsEquiv ⊤ 1)
    (hmul : ∀ m n (a : 𝒜 m) (b : 𝒜 n),
      f (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
        (M.tensorPowAddIso m n).inv.app ⊤ (tmulSection (f m a) (f n b))) :
    ∃ φ : 𝒜 →+*ᵍ sectionRingGrade M,
      ∀ n (a : 𝒜 n), φ.toRingHom a = DirectSum.of (SectionRingComponent M) n (f n a) := by
  classical
  let g n := (DirectSum.of (SectionRingComponent M) n).comp (f n)
  have hg1 : g 0 ⟨1, SetLike.one_mem_graded 𝒜⟩ = 1 := by
    change DirectSum.of (SectionRingComponent M) 0
      (f 0 ⟨1, SetLike.one_mem_graded 𝒜⟩) = 1
    rw [hone]
    rfl
  have hgm {m n} (a : 𝒜 m) (b : 𝒜 n) :
      g (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ = g m a * g n b := by
    change DirectSum.of (SectionRingComponent M) (m + n)
      (f (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩) = _
    rw [hmul]
    exact (DirectSum.of_mul_of (f m a) (f n b)).symm
  let F := (DirectSum.toSemiring g hg1 hgm).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom
  have hF (n) (a : 𝒜 n) : F a = DirectSum.of (SectionRingComponent M) n (f n a) := by
    change DirectSum.toSemiring g hg1 hgm (DirectSum.decompose 𝒜 (a : R)) = _
    rw [DirectSum.decompose_coe, DirectSum.toSemiring_of]
    rfl
  refine ⟨{ toRingHom := F, map_mem := ?_ }, hF⟩
  intro n a ha
  exact ⟨f n ⟨a, ha⟩, (hF n ⟨a, ha⟩).symm⟩

private theorem exists_evaluation_map
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules}
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    {W : Scheme.{u}} (j : W ⟶ Z) (V : S.affineOpens)
    (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (hM : ((tensorPullback j).obj L).IsInvertible) :
    let M := (tensorPullback j).obj L
    let 𝒜 : ℕ → AddSubgroup (A.obj V) := fun n ↦ (A.grading V n).toAddSubgroup
    letI : GradedRing 𝒜 := { (inferInstance : GradedRing (A.grading V)) with }
    ∃ φ : 𝒜 →+*ᵍ sectionRingGrade M,
      ∀ (n : ℕ) (a : A.grading V n),
        φ.toRingHom a = DirectSum.of (SectionRingComponent M) n (ψ.evaluate j V q n a) := by
  classical
  dsimp only
  let 𝒜 : ℕ → AddSubgroup (A.obj V) := fun n ↦ (A.grading V n).toAddSubgroup
  let hgrade : GradedRing (A.grading V) := A.gradedAlgebra V
  let : GradedRing 𝒜 := { hgrade with }
  let f (n : ℕ) : 𝒜 n →+ SectionRingComponent ((tensorPullback j).obj L) n :=
    { toFun := fun a ↦ ψ.evaluate j V q n ⟨a.val, a.property⟩
      map_zero' := by
        change ψ.evaluate j V q n 0 = 0
        simp only [RelativeGradedLineMap.evaluate, map_zero]
      map_add' := fun a b ↦ evaluate_add ψ j V q n _ _ }
  exact exists_graded_map 𝒜 ((tensorPullback j).obj L) f
    (evaluate_one ψ j V q) (evaluate_mul ψ j V q)

private theorem fixed_affine_generation
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules}
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    (hgen : ψ.GeneratesEverywhere) (V : S.affineOpens)
    (x : Z) (hxV : x ∈ h ⁻¹ᵁ V.1) :
    ∃ (n : ℕ), 0 < n ∧ ∃ a : A.grading V n,
      (L.tensorPow n).presheaf.germ (h ⁻¹ᵁ V.1) x hxV (ψ.component V n a) ∉
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk x)) •
          (⊤ : Submodule (Z.presheaf.stalk x) ((L.tensorPow n).presheaf.stalk x)) := by
  classical
  obtain ⟨U, hxU, n, hn, a, ha⟩ := hgen x
  refine ⟨n, hn, ?_⟩
  by_contra hbad
  push Not at hbad
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show h x ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
  let w : S.affineOpens := ⟨W, hW⟩
  have hwU : w ≤ U := fun y hy ↦ (hWU hy).1
  have hwV : w ≤ V := fun y hy ↦ (hWU hy).2
  let N : Submodule (Z.presheaf.stalk x) ((L.tensorPow n).presheaf.stalk x) :=
    (IsLocalRing.maximalIdeal (Z.presheaf.stalk x)) • ⊤
  let f := (S.presheaf.map (homOfLE (X := S.Opens) hwV).op).hom
  let halg : Algebra Γ(S, w.1) (A.obj w) := A.algebra w
  let := f.toAlgebra
  let : Algebra Γ(S, V.1) (A.obj w) :=
    ((@algebraMap Γ(S, w.1) (A.obj w) _ _ halg).comp f).toAlgebra
  have : IsScalarTower Γ(S, V.1) Γ(S, w.1) (A.obj w) := .of_algebraMap_eq' rfl
  have hbc := A.isGradedBaseChangeAlong hwV
  change (A.res hwV).IsGradedBaseChange at hbc
  have hall (b : A.grading w n) :
      (L.tensorPow n).presheaf.germ (h ⁻¹ᵁ w.1) x hxW (ψ.component w n b) ∈ N := by
    induction b using (hbc.isBaseChange n).inductionOn with
    | zero =>
      change (L.tensorPow n).presheaf.germ _ x hxW (ψ.component w n 0) ∈ N
      rw [map_zero, map_zero]
      exact N.zero_mem
    | tmul b =>
      change (L.tensorPow n).presheaf.germ _ x hxW
        (ψ.component w n ⟨A.res hwV b, _⟩) ∈ N
      rw [ψ.restriction]
      have hg := (L.tensorPow n).presheaf.germ_res_apply
        (homOfLE (h.preimage_mono hwV)) x (show x ∈ h ⁻¹ᵁ w.1 from hxW)
        (ψ.component V n b)
      exact hg.symm ▸ hbad b
    | smul s b hb =>
      change (L.tensorPow n).presheaf.germ _ x hxW (ψ.component w n (s • b)) ∈ N
      rw [ψ.smul, germ_smul]
      exact N.smul_mem _ hb
    | add b c hb hc =>
      change (L.tensorPow n).presheaf.germ _ x hxW (ψ.component w n (b + c)) ∈ N
      rw [map_add, map_add]
      exact N.add_mem hb hc
  have hb := hall ⟨A.res hwU a, (A.res hwU).map_mem a.property⟩
  rw [ψ.restriction] at hb
  have hg := (L.tensorPow n).presheaf.germ_res_apply
    (homOfLE (h.preimage_mono hwU)) x (show x ∈ h ⁻¹ᵁ w.1 from hxW)
    (ψ.component U n a)
  exact ha (hg ▸ hb)

private theorem residue_zero_iff {X : Scheme.{u}} (N : X.Modules)
    (U : X.Opens) (s : Γ(N, U)) (x : X) (hx : x ∈ U) :
    residueValue s x hx = 0 ↔ N.presheaf.germ U x hx s ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (N.presheaf.stalk x)) := by
  change (1 : IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
    N.presheaf.germ U x hx s = 0 ↔ _
  rw [← (TensorProduct.quotTensorEquivQuotSMul
    ↑(N.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).map_eq_zero_iff]
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

private theorem nonvanishing_pullback_open {X Y : Scheme.{u}} (j : X ⟶ Y)
    (N : Y.Modules) [N.IsInvertible] (U : Y.Opens)
    (q : (⊤ : X.Opens) ≤ j ⁻¹ᵁ U) (s : Γ(N, U)) (x : X) :
    x ∈ nonvanishingLocus ((tensorPullback j).obj N)
      (((tensorPullback j).obj N).presheaf.map (homOfLE q).op
        (((tensorPullbackSectionAdjunction j).unit.app N).app U s)) ↔
    N.presheaf.germ U (j x) (q trivial) s ∉
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (j x))) •
        (⊤ : Submodule (Y.presheaf.stalk (j x)) (N.presheaf.stalk (j x))) := by
  classical
  let P := (tensorPullback j).obj N
  let t : Γ(P, j ⁻¹ᵁ U) :=
    ((tensorPullbackSectionAdjunction j).unit.app N).app U s
  obtain ⟨e, he⟩ := (invertible_pullback_tensor j).2.2.2.2.2.2.1 N x
  let := (j.residueFieldMap x).hom.toAlgebra
  have hinj : Function.Injective e.hom := (ModuleCat.mono_iff_injective e.hom).mp
    inferInstance
  have hres : residueValue (P.presheaf.map (homOfLE q).op t) x trivial =
      residueValue t x (q trivial) := by
    change (1 : IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
      P.presheaf.germ ⊤ x trivial (P.presheaf.map (homOfLE q).op t) = _
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  have hz : residueValue (P.presheaf.map (homOfLE q).op t) x trivial = 0 ↔
      residueValue s (j x) (q trivial) = 0 := by
    rw [hres, ← (map_eq_zero_iff e.hom.hom hinj)]
    have he' := he U (q trivial) s
    dsimp only at he'
    rw [boundary_adj_eq] at he'
    change e.hom (residueValue t x (q trivial)) = _ at he'
    exact (congrArg (fun z ↦ z = 0) he').to_iff.trans (by
      exact Module.FaithfullyFlat.one_tmul_eq_zero_iff (Y.residueField (j x))
        (residueFiber N (j x)) _)
  change ¬ _ ↔ ¬ _
  exact not_congr ((residue_zero_iff P ⊤ _ x trivial).symm.trans
    (hz.trans (residue_zero_iff N U s (j x) (q trivial))))

private theorem evaluation_cover
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules} [L.IsInvertible]
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    (hgen : ψ.GeneratesEverywhere) (V : S.affineOpens) :
    ∀ x : (h ⁻¹ᵁ V.1).toScheme, ∃ (n : ℕ) (a : A.grading V n),
      0 < n ∧ x ∈ nonvanishingLocus
        (((tensorPullback (h ⁻¹ᵁ V.1).ι).obj L).tensorPow n)
        (ψ.evaluate (h ⁻¹ᵁ V.1).ι V (by simp) n a) := by
  intro x
  obtain ⟨n, hn, a, ha⟩ := fixed_affine_generation ψ hgen V x.val x.property
  refine ⟨n, a, hn, ?_⟩
  unfold RelativeGradedLineMap.evaluate
  rw [nonvanishingLocus_iso]
  exact (nonvanishing_pullback_open (h ⁻¹ᵁ V.1).ι (L.tensorPow n)
    (h ⁻¹ᵁ V.1) (by simp) (ψ.component V n a) x).2 ha

private theorem isAmple_of_positive_tensorPow {X : Scheme.{u}}
    (M : X.Modules) [M.IsInvertible] (d : ℕ) (hd : 0 < d)
    (hM : IsAmple X (M.tensorPow d)) : IsAmple X M := by
  refine ⟨hM.1, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, U, hx, hU, hs⟩ := hM.2 x
  let e := (M.tensorPowMulIso d n).symm
  refine ⟨d * n, Nat.mul_pos hd hn, e.hom.app ⊤ s, U, hx, hU, ?_⟩
  intro y
  exact (hs y).trans (Set.ext_iff.mp (nonvanishingLocus_iso e s) y).symm

/-- If the positive-degree generation locus is all of `Z` and its canonical Proj map is an
immersion, the invertible module is ample over every affine open of the base.  The graded
algebra is arbitrary: it need not be generated in degree one and its degree-zero part need
not be the structure sheaf.

Source: Stacks Project, Morphisms, Tag 01VJ, implication (6) implies (1); Constructions,
Tag 01O9 (blueprint: lem-trf-graded-immersion-ample-criterion).

Proof:
1. Fix an affine open `V` and put `T = h ⁻¹ᵁ V`. The relative Proj chart contains
`r(T)` since `r` is over `S`. Lift to this chart and transport the grading from
submodules to additive subgroups by the identity graded-ring isomorphism.
Construct its normalized graded section map by transporting the unit and product
identities through the pullback comparisons and extending through the direct sum.
Degreewise base-change induction localizes the given generation condition to `V`;
the fibre comparison preserves this nonvanishing after pullback. The affine chart
formula theorem (lem-trf-relative-graded-map-affine-chart) then supplies the
basic-open and fraction formulas.
2. `T` is quasi-compact, since `h` is quasi-compact and `V` is affine. The lifted map
is an immersion by cancellation of the chart open immersion. Apply
lemma-nagata-immersion-shrink-to-closed-exists to factor it as a closed immersion
`i : T ⟶ Y` followed by a quasi-compact open immersion into `Proj A(V)`.
3. The canonical-map twist comparison (lem-trf-proj-canonical-map-twist-comparison)
gives `d > 0` and identifications of the pullbacks of `O(dk)` with `M^(dk)` for
all `k > 0`, where `M` is the tensor pullback of `L` to `T`.
4. The quasi-compact-open twist theorem (lem-trf-proj-qc-open-twist-ample) gives
`e > 0` for which every `O_Y(ek)` is invertible and ample. Take `k = d` and pull
back along `i` using lem-trf-ample-restrict-closed-immersion. The composition and
open-restriction comparisons identify this ample pullback with the pullback of
`O(ed)`. Step 3 with `k = e`, and `ed = de`, identify it with `M^(de)`.
This uses the ampleness clause for every multiple directly.
5. The private proved helper reinterprets any affine nonvanishing section of
`(M^(de))^n` as a section of `M^(de*n)` using `tensorPowMulIso`; isomorphisms preserve
nonvanishing loci. Thus the same affine cover proves that `M` is ample.
Empty charts and arbitrary positive degrees are allowed throughout. -/
theorem graded_immersion_ample_criterion
    {Z S : Scheme.{u}} (h : Z ⟶ S) [QuasiCompact h]
    (L : Z.Modules) [L.IsInvertible] (A : S.GradedAlgebraData)
    (ψ : RelativeGradedLineMap h A L) (hgen : ψ.GeneratesEverywhere)
    (r : Z ⟶ A.relProj) (hr : ψ.IsCanonicalMap r) [IsImmersion r] :
    ∀ (V : S.Opens), IsAffineOpen V →
      ∃ hL : ((tensorPullback (h ⁻¹ᵁ V).ι).obj L).IsInvertible,
        @IsAmple (h ⁻¹ᵁ V).toScheme
          ((tensorPullback (h ⁻¹ᵁ V).ι).obj L) hL := by
  classical
  intro V hV
  let T := (h ⁻¹ᵁ V).toScheme
  let M := (tensorPullback (h ⁻¹ᵁ V).ι).obj L
  have hM : M.IsInvertible := ((invertible_pullback_tensor _).1 L).2
  have : CompactSpace T := isCompact_iff_compactSpace.mp (h.isCompact_preimage hV.isCompact)
  refine ⟨hM, ?_⟩
  let v : S.affineOpens := ⟨V, hV⟩
  let 𝒜 : ℕ → AddSubgroup (A.obj v) := fun n ↦ (A.grading v n).toAddSubgroup
  let hgrade : GradedRing (A.grading v) := A.gradedAlgebra v
  let : GradedRing 𝒜 := { hgrade with }
  let γ : A.grading v →+*ᵍ 𝒜 :=
    { toRingHom := RingHom.id _
      map_mem := fun ha ↦ ha }
  let δ : 𝒜 →+*ᵍ A.grading v :=
    { toRingHom := RingHom.id _
      map_mem := fun ha ↦ ha }
  have hγ : (HomogeneousIdeal.irrelevant (A.grading v)).toIdeal ≤
      Ideal.map γ.toRingHom (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
    intro a ha
    exact Ideal.mem_map_of_mem γ.toRingHom ha
  have hδ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.map δ.toRingHom (HomogeneousIdeal.irrelevant (A.grading v)).toIdeal := by
    intro a ha
    exact Ideal.mem_map_of_mem δ.toRingHom ha
  let E : Proj 𝒜 ≅ Proj (A.grading v) :=
    { hom := Proj.map γ hγ
      inv := Proj.map δ hδ
      hom_inv_id := by
        rw [← Proj.map_comp]
        exact (Proj.map_congr (show γ.comp δ = .id _ from
          GradedRingHom.ext fun _ ↦ rfl) _ _).trans Proj.map_id
      inv_hom_id := by
        rw [← Proj.map_comp]
        exact (Proj.map_congr (show δ.comp γ = .id _ from
          GradedRingHom.ext fun _ ↦ rfl) _ _).trans Proj.map_id }
  have hrange : Set.range ((h ⁻¹ᵁ V).ι ≫ r).base ⊆ Set.range (A.relProjι v).base := by
    rintro _ ⟨x, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, ← A.relProjHom_preimage v]
    change A.relProjHom (r ((h ⁻¹ᵁ V).ι x)) ∈ V
    rw [← Scheme.Hom.comp_apply, hr.1]
    exact x.property
  let ρ₀ := IsOpenImmersion.lift (A.relProjι v) ((h ⁻¹ᵁ V).ι ≫ r) hrange
  let ρ := ρ₀ ≫ E.inv
  have hρ : ρ ≫ E.hom ≫ A.relProjι v = (h ⁻¹ᵁ V).ι ≫ r := by
    simp [ρ, Category.assoc, ρ₀, IsOpenImmersion.lift_fac]
  have : IsImmersion (ρ ≫ E.hom ≫ A.relProjι v) := by rw [hρ]; infer_instance
  have : IsImmersion ρ := IsImmersion.of_comp ρ (E.hom ≫ A.relProjι v)
  obtain ⟨φ, hφ⟩ := exists_evaluation_map ψ (h ⁻¹ᵁ V).ι v (by simp [v]) hM
  have hcover : ∀ z : T, ∃ (n : ℕ) (a : A.obj v) (ha : a ∈ 𝒜 n),
      0 < n ∧ z ∈ nonvanishingLocus (M.tensorPow n) ((φ.toRingHom a) n) := by
    intro z
    obtain ⟨n, a, hn, ha⟩ := evaluation_cover ψ hgen v z
    refine ⟨n, a, a.property, hn, ?_⟩
    rw [hφ]
    simpa only [DirectSum.of_eq_same] using ha
  obtain ⟨hpre, hformula⟩ := ψ.affine_chart_formulas r hr v hM ρ hρ φ hφ hcover
  obtain ⟨d, hd, hθ⟩ := exists_proj_canonical_map_twist_comparison 𝒜 T M φ
    hcover ρ hpre hformula
  obtain ⟨Y, i, hY, hi, hfac⟩ := ρ.exists_isCompact_isClosedImmersion
  have : IsClosedImmersion i := hi
  have : CompactSpace Y.toScheme := isCompact_iff_compactSpace.mp hY
  obtain ⟨e, he, hample⟩ := exists_common_degree_twist_ample 𝒜 Y.ι
  obtain ⟨hN, hNamp, _⟩ := hample d hd
  have := hN
  have hP := isAmple_tensorPullback_of_isClosedImmersion _ hNamp i
  obtain ⟨θ, _⟩ := hθ e he
  let F := Proj.twist 𝒜 (Int.ofNat (e * d))
  let c : (tensorPullback ρ).obj F ≅ (tensorPullback i).obj (F.restrict Y.ι) :=
    (tensorPullbackCompositionIso i Y.ι ρ hfac).app F ≪≫
      (tensorPullback i).mapIso
        (((boundaryPullbackComparison Y.ι).app F) ≪≫
          ((restrictFunctorIsoPullback Y.ι).app F).symm)
  let b : (tensorPullback i).obj (F.restrict Y.ι) ≅ M.tensorPow (d * e) :=
    c.symm ≪≫ (tensorPullback ρ).mapIso
      (eqToIso (congrArg (Proj.twist 𝒜) (by simp [Nat.mul_comm]))) ≪≫ θ
  have : ((tensorPullback i).obj (F.restrict Y.ι)).IsInvertible :=
    ((invertible_pullback_tensor i).1 _).2
  exact isAmple_of_positive_tensorPow M (d * e) (Nat.mul_pos hd he)
    ((isAmple_iff_of_iso b).mp hP)

end AlgebraicGeometry.Scheme.Modules
