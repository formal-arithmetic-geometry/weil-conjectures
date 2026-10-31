/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
import all WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! Uniform lower bounds for the two tensors occurring in compact support.

Source: blueprint paragraph (3), bounds part of
`lem-sp-tower-compact-support-projection-formula`.
(blueprint: lem-sp-tower-compact-support-projection-formula)

Use the uniform Tor interval of the first input and a cohomological lower bound
of the second input. Exact pullback preserves the latter bound. At each finite
level, compare the recorded tensor with the canonical derived tensor using K-flat
models, and apply the bounded-flat tensor estimate. Exact evaluation detects the
resulting tower bound. The open projection isomorphism and exact extension by zero
then give the same lower bound for the second tensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerProjection

open SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded level tensor has the usual Tor-amplitude lower bound.
Compare both tensor constructions on K-flat representatives, identify the
resolution-based Tor predicate with the abstract one, and apply the source
bounded-flat tensor estimate. -/
private theorem finite_tensor_bound (b : Base l E) (T : Scheme.{u}) (n : ℕ)
    (K L : proEtaleDerivedCategory T (R l E n)) (a z m : ℤ)
    (ht : HasProEtaleTorAmplitude T (R l E n) K a z) (hL : L.IsGE m) :
    (((b.calculus T).levelClosed n).tensor.obj (K, L)).IsGE (a + m) := by
  classical
  let R₀ := proEtaleConstantRing T (R l E n)
  let A := proEtaleRingModules T R₀
  let := SheafOfModules.isMonoidal_W_independentCoefficients R₀
  let := SheafOfModules.monoidalCategory R₀
  let := SheafOfModules.symmetricCategory R₀
  let := SheafOfModules.tensorPreadditive R₀
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R₀)).some
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R₀
  have : IsGrothendieckAbelian.{u + 1} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (ProEt.topology T) _
  have : ∀ X Y : GradedObject ℤ A, GradedObject.HasTensor X Y := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  have : ∀ X Y Z W : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  have : DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso A (.up ℤ)) := by infer_instance
  have htor : _root_.DerivedCategory.torAmplitudeIn A a z K := by
    apply (scalarExtension_abstract_tor_iff K a z ht.1 ?_).mp ht
    intro G
    obtain ⟨P, f, hp, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral G
    exact ⟨P, f, hf, hp⟩
  have : L.IsGE m := hL
  have hb := DerivedCategory.isGE_tensor_of_torAmplitudeIn htor L m
  let G := DerivedCategory.Q.objPreimage K
  let H := DerivedCategory.Q.objPreimage L
  obtain ⟨P, f, hp, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral G
  obtain ⟨Q, g, hq, _, hg, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral H
  have : QuasiIso f := hf
  have : QuasiIso g := hg
  let eP := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let eQ := asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso L
  have hpk : P.IsKFlatIndependentCoefficients :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hp
  have hqk : Q.IsKFlatIndependentCoefficients :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).mpr hq
  have hk : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mpr
      (hp N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic A).prop_of_iso (β_ _ _) hr, hr⟩
  let e := (MonoidalCategory.tensorIso eP.symm eQ.symm) ≪≫
    DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P Q hk ≪≫
    WeilConjectures.SemilinearSections.tensorModelIso
      (ProEt.topology T) R₀ ((b.calculus T).levelClosed n)
      ((b.calculus T).levelTensorModels n) P Q hpk hqk ≪≫
    ((b.calculus T).levelClosed n).tensor.mapIso (eP.prod eQ)
  exact DerivedCategory.TStructure.t.isGE_of_iso e (a + m)

/-- Evaluate the counit of realization, then use the section-normalized
comparison already proved for the ordinary coefficient towers. -/
private def evaluation_comparison (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (K : D l E T) (n : ℕ) :
    (Ev l E T n).obj K ≅ (spDerivedCoefficientEvaluation l E T A n).obj
      ((realization l E b T A).inverse.obj K) :=
  (Ev l E T n).mapIso ((realization l E b T A).counitIso.app K).symm ≪≫
    (sp_realization_evaluation l E b T A n).app _

/-- Exact evaluations detect lower bounds: transport to the original towers,
apply componentwise detection of zero homology, and transport back. -/
private theorem tower_isGE_of_evaluations (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (K : D l E T) (m : ℤ)
    (h : ∀ n, ((Ev l E T n).obj K).IsGE m) : K.IsGE m := by
  let := A.hasDerived
  have := b.realizationAdditive T
  have hK : ((realization l E b T A).inverse.obj K).IsGE m :=
    sp_tower_isGE_of_levels l E T A _ m (by
      intro n i hi
      exact ((DerivedCategory.isGE_iff _ m).mp (h n) i hi).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso
          (evaluation_comparison l E b T A K n)).symm)
  have hR : (((realization l E b T A).inverse ⋙
      (realization l E b T A).functor).obj K).IsGE m :=
    (b.realization T).functor.isGE_mapDerivedCategory_obj
      ((realization l E b T A).inverse.obj K) m
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((realization l E b T A).counitIso.app K) m

/-- The two compact-support tensor inputs are bounded below.
Source: paragraph (3), `lem-sp-tower-compact-support-projection-formula`.
Proof: choose a uniform Tor interval [v,w] for C and a cohomological lower bound a
for B. Exact pullback preserves a. The bounded-flat tensor theorem gives v+a at
every coefficient level, and exact evaluations detect this bound on the tower.
The open projection isomorphism identifies the second tensor with exact extension
by zero of the first one, so v+a works for both.
(blueprint: lem-sp-tower-compact-support-projection-formula) -/
theorem tower_compact_support_projection_bounds
    (b : Base l E) (o : Operations l E b)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : SpCoefficientTowersAbelian l E X.left)
    (AY : SpCoefficientTowersAbelian l E Y.left)
    (C : D l E X.left) (B : D l E Y.left)
    (_hC : constructibleTor l E b X.left AX C)
    (_hB : constructibleTor l E b Y.left AY B) :
    (∃ m : ℤ, ((tensor l E b X.left).obj
      (C, (pull l E b (o.geometry f.left)).obj B)).IsGE m) ∧
    (∃ m : ℤ, ((tensor l E b c.Z).obj
      ((openD l E b (o.openOp c.i)).obj C,
        (pull l E b (o.geometry c.g)).obj B)).IsGE m) := by
  classical
  let := AX.hasDerived
  let := AY.hasDerived
  have := b.realizationAdditive X.left
  have := b.realizationAdditive Y.left
  obtain ⟨a, z, v, w, haz, hvw, hC⟩ := _hC.2
  obtain ⟨a', z', v', w', haz', hvw', hB⟩ := _hB.2
  have hB₀ : ((realization l E b Y.left AY).inverse.obj B).IsGE a' :=
    sp_tower_isGE_of_levels l E Y.left AY _ a'
      (fun n i hi ↦ (hB n).1 i (Or.inl hi))
  have hR : (((realization l E b Y.left AY).inverse ⋙
      (realization l E b Y.left AY).functor).obj B).IsGE a' :=
    (b.realization Y.left).functor.isGE_mapDerivedCategory_obj
      ((realization l E b Y.left AY).inverse.obj B) a'
  have hB₁ : B.IsGE a' := DerivedCategory.TStructure.t.isGE_of_iso
    ((realization l E b Y.left AY).counitIso.app B) a'
  let P := (pull l E b (o.geometry f.left)).obj B
  have hP : P.IsGE a' := (o.geometry f.left).pull.isGE_mapDerivedCategory_obj B a'
  let K := (tensor l E b X.left).obj (C, P)
  have hK : K.IsGE (v + a') := by
    apply tower_isGE_of_evaluations l E b X.left AX K (v + a')
    intro n
    have ht : HasProEtaleTorAmplitude X.left (R l E n)
        ((Ev l E X.left n).obj C) v w :=
      sp_tor_of_iso X.left _ (evaluation_comparison l E b X.left AX C n).symm
        (hC n).2
    have he : ((Ev l E X.left n).obj P).IsGE a' :=
      (ev l E X.left n).isGE_mapDerivedCategory_obj P a'
    have hlevel : ((((Ev l E X.left n).prod (Ev l E X.left n)) ⋙
        ((b.calculus X.left).levelClosed n).tensor).obj (C, P)).IsGE (v + a') :=
      finite_tensor_bound l E b X.left n _ _ v w a' ht he
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (((b.calculus X.left).tensorEvaluation n).app (C, P)).symm (v + a')
  refine ⟨⟨v + a', hK⟩, v + a', ?_⟩
  let eP : (pull l E b (o.geometry c.i)).obj
      ((pull l E b (o.geometry c.g)).obj B) ≅ P :=
    (o.comp c.i c.g).app B ≪≫
      (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).app B
  let e := o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B) ≪≫
    (openD l E b (o.openOp c.i)).mapIso
      ((tensor l E b X.left).mapIso ((Iso.refl C).prod eP))
  have := (o.openOp c.i).extension.isGE_mapDerivedCategory_obj K (v + a')
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm (v + a')

end AlgebraicGeometry.ProEtale.SpTowerProjection
