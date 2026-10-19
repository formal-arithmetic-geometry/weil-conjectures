/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SystemLevelLeftExtension
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
Canonical tensor reductions of strict semilinear coefficient systems.

Source: coefficient-tower lemma, clauses (2)--(3), and Stacks Tags 06YS, 06XN, 06YY.
The ordinary tensor adjuncts satisfy the unit and composition laws by adjunction
injectivity and the normalized pure-tensor formulas. A flat-term K-flat resolution
extends the scalar coherence comparisons to every complex: naturality reduces equality
to the resolution and its quasi-isomorphism is inverted. Compose those comparisons
with the strict ordinary reductions and descend the resulting natural transformation
through derived localization. The lifting formula determines its value on complexes;
localization extensionality, naturality and the ordinary tensor identities prove the
derived unit and associativity formulas. No simultaneous resolution of systems is used.
(blueprint: lem-sp-system-coefficient-reductions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe t v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type t} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  (S : SystemScalarAssignment (J := J))
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u})

/-- The ordinary tensor adjunct of the strict transition. -/
def systemOrdinaryReduction {m n : ℕ} (h : m ≤ n) :
    systemEvaluation B n ⋙ systemTensor S B h ⟶ systemEvaluation B m where
  app M := ((systemTensorAdj S B h).homEquiv _ _).symm (M.transition h)
  naturality {_M _N} f :=
    (systemTensorAdj S B h).homEquiv_naturality_right_square
      (f.app n) _ _ (f.app m) (f.comm h)

private theorem ordinaryReduction_unit {m n : ℕ} (h : m ≤ n)
    (M : StrictRingSystem B) (U : Cᵒᵖ) (x : (M.level n).val.obj U) :
    ((systemOrdinaryReduction S B h).app M).val.app U
      (systemModelTmul (S (B.map (homOfLE h).op)).model (M.level n) U 1 x) =
      (M.transition h).val.app U x := by
  have hh := ((systemTensorAdj S B h).homEquiv _ _).apply_symm_apply (M.transition h)
  have hh' := congrArg (fun f ↦ f.val.app U x) hh
  change ((systemOrdinaryReduction S B h).app M).val.app U
    (((systemTensorAdj S B h).unit.app (M.level n)).val.app U x) = _ at hh'
  rwa [(S (B.map (homOfLE h).op)).unit_normalized] at hh'

variable (D : SystemTensorCoherence S)

/-- Equal-index ordinary reduction is the normalized tensor unitor. -/
theorem systemOrdinaryReduction_identity (n : ℕ) (M : StrictRingSystem B) :
    (systemOrdinaryReduction S B (Nat.le_refl n)).app M =
      (D.ordinaryUnit B n).hom.app (M.level n) := by
  apply ((systemTensorAdj S B (Nat.le_refl n)).homEquiv _ _).injective
  change (systemTensorAdj S B (Nat.le_refl n)).homEquiv _ _
    (((systemTensorAdj S B (Nat.le_refl n)).homEquiv _ _).symm
      (M.transition (Nat.le_refl n))) = _
  rw [Equiv.apply_symm_apply]
  ext U x
  change (M.transition (Nat.le_refl n)).val.app U x =
    ((D.ordinaryUnit B n).hom.app (M.level n)).val.app U
      (((systemTensorAdj S B (Nat.le_refl n)).unit.app (M.level n)).val.app U x)
  rw [(S (B.map (homOfLE (Nat.le_refl n)).op)).unit_normalized,
    D.unit_normalized, one_smul, M.identity]

/-- Successive ordinary reductions compose under the balanced tensor associator. -/
theorem systemOrdinaryReduction_comp {r m n : ℕ} (h : r ≤ m) (k : m ≤ n)
    (M : StrictRingSystem B) :
    (systemTensor S B h).map ((systemOrdinaryReduction S B k).app M) ≫
        (systemOrdinaryReduction S B h).app M =
      (D.ordinaryAssoc B h k).hom.app (M.level n) ≫
        (systemOrdinaryReduction S B (h.trans k)).app M := by
  apply ((systemTensorAdj S B h).homEquiv _ _).injective
  apply ((systemTensorAdj S B k).homEquiv _ _).injective
  ext U x
  simp only [Adjunction.homEquiv_apply]
  change ((systemOrdinaryReduction S B h).app M).val.app U
      (((systemTensor S B h).map ((systemOrdinaryReduction S B k).app M)).val.app U
        (((systemTensorAdj S B h).unit.app ((systemTensor S B k).obj (M.level n))).val.app U
          (((systemTensorAdj S B k).unit.app (M.level n)).val.app U x))) =
    ((systemOrdinaryReduction S B (h.trans k)).app M).val.app U
      (((D.ordinaryAssoc B h k).hom.app (M.level n)).val.app U
        (((systemTensorAdj S B h).unit.app ((systemTensor S B k).obj (M.level n))).val.app U
          (((systemTensorAdj S B k).unit.app (M.level n)).val.app U x)))
  have hn := congrArg (fun f ↦ f.val.app U
    (((systemTensorAdj S B k).unit.app (M.level n)).val.app U x))
    ((systemTensorAdj S B h).unit.naturality ((systemOrdinaryReduction S B k).app M))
  change
    (((systemTensorAdj S B h).unit.app (M.level m)).val.app U)
        (((systemOrdinaryReduction S B k).app M).val.app U
          (((systemTensorAdj S B k).unit.app (M.level n)).val.app U x)) =
      (((systemTensor S B h).map ((systemOrdinaryReduction S B k).app M)).val.app U)
        (((systemTensorAdj S B h).unit.app ((systemTensor S B k).obj (M.level n))).val.app U
          (((systemTensorAdj S B k).unit.app (M.level n)).val.app U x)) at hn
  rw [← hn]
  rw [(S (B.map (homOfLE k).op)).unit_normalized,
    ordinaryReduction_unit, (S (B.map (homOfLE h).op)).unit_normalized,
    ordinaryReduction_unit]
  rw [(S (B.map (homOfLE h).op)).unit_normalized, D.assoc_normalized]
  simp only [map_one, mul_one]
  rw [ordinaryReduction_unit]
  exact (M.compose h k U x).symm

private theorem natTrans_ext_kflat {R : Sheaf J CommRingCat.{u}}
    {A : Type*} [Category A]
    {F G : CochainComplex (systemLevel (Functor.const ℕᵒᵖ |>.obj R) 0) ℤ ⥤ A}
    (α β : F ⟶ G)
    (hinv : ∀ {P Q} (f : P ⟶ Q), QuasiIso f → IsIso (F.map f))
    (h : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      (∀ i, IsFlatOnSite (R := R) (P.X i)) → α.app P = β.app P) : α = β := by
  ext P
  obtain ⟨K, q, hK, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  have hh : ∀ i, IsFlatOnSite (R := R) (K.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (K.X i)).symm (hflat i)
  have := hinv q hq
  rw [← cancel_epi (F.map q), α.naturality, β.naturality, h K hK hh]

/-- The derived tensor unitor comparison holds on every complex. -/
theorem systemTensorUnit_rep_all (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) :
    (D.derivedUnit B n).hom.app (DerivedCategory.Q.obj P) =
      (S (B.map (homOfLE (Nat.le_refl n)).op)).model.ε.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (D.ordinaryUnit B n) (.up ℤ)).hom.app P) := by
  let α : DerivedCategory.Q ⋙ systemDerivedTensor S B (Nat.le_refl n) ⟶
      DerivedCategory.Q := Functor.whiskerLeft DerivedCategory.Q (D.derivedUnit B n).hom
  let β : DerivedCategory.Q ⋙ systemDerivedTensor S B (Nat.le_refl n) ⟶
      DerivedCategory.Q :=
    (S (B.map (homOfLE (Nat.le_refl n)).op)).model.ε ≫
      Functor.whiskerRight
        (NatIso.mapHomologicalComplex (D.ordinaryUnit B n) (.up ℤ)).hom DerivedCategory.Q
  have hh : α = β := natTrans_ext_kflat α β
    (fun f hf ↦ by
      let _ := hf
      dsimp only [Functor.comp_map]
      infer_instance)
    (fun K hK hflat ↦ D.derivedUnit_rep B n K ⟨hK, hflat⟩)
  exact NatTrans.congr_app hh P

/-- The derived balanced associator comparison holds on every complex. -/
theorem systemTensorAssoc_rep_all {r m n : ℕ} (h : r ≤ m) (k : m ≤ n)
    (P : CochainComplex (systemLevel B n) ℤ) :
    (D.derivedAssoc B h k).hom.app (DerivedCategory.Q.obj P) ≫
        (S (B.map (homOfLE (h.trans k)).op)).model.ε.app P =
      (systemDerivedTensor S B h).map ((S (B.map (homOfLE k).op)).model.ε.app P) ≫
        (S (B.map (homOfLE h).op)).model.ε.app
          (((systemTensor S B k).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (D.ordinaryAssoc B h k) (.up ℤ)).hom.app P) := by
  let α := Functor.whiskerLeft DerivedCategory.Q (D.derivedAssoc B h k).hom ≫
    (S (B.map (homOfLE (h.trans k)).op)).model.ε
  let β := Functor.whiskerRight (S (B.map (homOfLE k).op)).model.ε
      (systemDerivedTensor S B h) ≫
    Functor.whiskerLeft ((systemTensor S B k).mapHomologicalComplex (.up ℤ))
      (S (B.map (homOfLE h).op)).model.ε ≫
    Functor.whiskerRight
      (NatIso.mapHomologicalComplex (D.ordinaryAssoc B h k) (.up ℤ)).hom DerivedCategory.Q
  have hh : α = β := natTrans_ext_kflat α β
    (fun f hf ↦ by
      let _ := hf
      dsimp only [Functor.comp_map]
      infer_instance)
    (fun K hK hflat ↦ D.derivedAssoc_rep B h k K ⟨hK, hflat⟩)
  exact NatTrans.congr_app hh P

section ExactPresentation
variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  (F : A ⥤ StrictRingSystem B) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Reduction for a strict system presented by an exact functor. -/
def presentedOrdinaryReduction {m n : ℕ} (h : m ≤ n) :
    (F ⋙ systemEvaluation B n) ⋙ systemTensor S B h ⟶ F ⋙ systemEvaluation B m :=
  Functor.whiskerLeft F (systemOrdinaryReduction S B h)

/-- The canonical comparison and strict tensor reduction on complexes. -/
def presentedReductionOnComplexes {m n : ℕ} (h : m ≤ n) :
    DerivedCategory.Q ⋙ (F ⋙ systemEvaluation B n).mapDerivedCategory ⋙
        systemDerivedTensor S B h ⟶
      DerivedCategory.Q ⋙ (F ⋙ systemEvaluation B m).mapDerivedCategory :=
  Functor.whiskerRight (F ⋙ systemEvaluation B n).mapDerivedCategoryFactors.hom
      (systemDerivedTensor S B h) ≫
    Functor.whiskerLeft ((F ⋙ systemEvaluation B n).mapHomologicalComplex (.up ℤ))
      (S (B.map (homOfLE h).op)).model.ε ≫
    Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (presentedOrdinaryReduction S B F h) (.up ℤ))
      DerivedCategory.Q ≫
    (F ⋙ systemEvaluation B m).mapDerivedCategoryFactors.inv

/-- Descend the comparison followed by strict reduction through localization. -/
def presentedDerivedReduction {m n : ℕ} (h : m ≤ n) :
    (F ⋙ systemEvaluation B n).mapDerivedCategory ⋙ systemDerivedTensor S B h ⟶
      (F ⋙ systemEvaluation B m).mapDerivedCategory := by
  let L := (F ⋙ systemEvaluation B n).mapDerivedCategory ⋙ systemDerivedTensor S B h
  let R := (F ⋙ systemEvaluation B m).mapDerivedCategory
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (DerivedCategory.Q ⋙ L) L := ⟨Iso.refl _⟩
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (DerivedCategory.Q ⋙ R) R := ⟨Iso.refl _⟩
  exact Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    _ _ L R (presentedReductionOnComplexes S B F h)

/-- The descended map has the prescribed comparison on every complex. -/
theorem presentedDerivedReduction_rep {m n : ℕ} (h : m ≤ n)
    (P : CochainComplex A ℤ) :
    (presentedDerivedReduction S B F h).app (DerivedCategory.Q.obj P) =
      (systemDerivedTensor S B h).map
        ((F ⋙ systemEvaluation B n).mapDerivedCategoryFactors.hom.app P) ≫
      (S (B.map (homOfLE h).op)).model.ε.app
        (((F ⋙ systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (presentedOrdinaryReduction S B F h) (.up ℤ)).app P) ≫
      (F ⋙ systemEvaluation B m).mapDerivedCategoryFactors.inv.app P := by
  simp [presentedDerivedReduction, Localization.liftNatTrans_app,
    presentedReductionOnComplexes]

/-- Identity reduction is the canonical derived tensor unitor. -/
theorem presentedDerivedReduction_identity (n : ℕ)
    (M : DerivedCategory A) :
    (presentedDerivedReduction S B F (Nat.le_refl n)).app M =
      (D.derivedUnit B n).hom.app ((F ⋙ systemEvaluation B n).mapDerivedCategory.obj M) := by
  have he : presentedDerivedReduction S B F (Nat.le_refl n) =
      Functor.whiskerLeft (F ⋙ systemEvaluation B n).mapDerivedCategory
        (D.derivedUnit B n).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro P
    have hord :
        (NatTrans.mapHomologicalComplex
          (presentedOrdinaryReduction S B F (Nat.le_refl n)) (.up ℤ)).app P =
        (NatIso.mapHomologicalComplex (D.ordinaryUnit B n) (.up ℤ)).hom.app
          (((F ⋙ systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P) := by
      ext i : 1
      exact systemOrdinaryReduction_identity S B D n (F.obj (P.X i))
    rw [← cancel_mono ((F ⋙ systemEvaluation B n).mapDerivedCategoryFactors.hom.app P)]
    simp only [presentedDerivedReduction_rep, Category.assoc, Iso.inv_hom_id_app,
      Functor.whiskerLeft_app]
    erw [hord, ← systemTensorUnit_rep_all]
    exact (D.derivedUnit B n).hom.naturality
      ((F ⋙ systemEvaluation B n).mapDerivedCategoryFactors.hom.app P)
  exact NatTrans.congr_app he M

/-- Composing derived reductions agrees with the normalized derived tensor associator.
Source: coefficient-tower lemma, proof of clause (3), and Stacks Tags 06YS and 06XN
(blueprint: lem-sp-system-coefficient-reductions).

Proof: use localization extensionality and the explicit reduction comparison on a
complex. Cancel the evaluation comparison isomorphisms. Move the associator past the
source comparison by naturality; its comparison on all complexes follows by a
flat-term K-flat resolution. Naturality of the scalar comparison then brings the two
ordinary reductions together. Their ordinary composition equation is the normalized
balanced tensor formula combined with the strict-system composition law. -/
theorem presentedDerivedReduction_comp {r m n : ℕ} (h : r ≤ m) (k : m ≤ n)
    (M : DerivedCategory A) :
    (systemDerivedTensor S B h).map ((presentedDerivedReduction S B F k).app M) ≫
        (presentedDerivedReduction S B F h).app M =
      (D.derivedAssoc B h k).hom.app
          ((F ⋙ systemEvaluation B n).mapDerivedCategory.obj M) ≫
        (presentedDerivedReduction S B F (h.trans k)).app M := by
  let α := Functor.whiskerRight (presentedDerivedReduction S B F k)
      (systemDerivedTensor S B h) ≫ presentedDerivedReduction S B F h
  let β := Functor.whiskerLeft (F ⋙ systemEvaluation B n).mapDerivedCategory
      (D.derivedAssoc B h k).hom ≫ presentedDerivedReduction S B F (h.trans k)
  have he : α = β := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro P
    change (systemDerivedTensor S B h).map
        ((presentedDerivedReduction S B F k).app (DerivedCategory.Q.obj P)) ≫
          (presentedDerivedReduction S B F h).app (DerivedCategory.Q.obj P) = _
    have hord :
        (((systemTensor S B h).mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (presentedOrdinaryReduction S B F k)
            (.up ℤ)).app P)) ≫
          (NatTrans.mapHomologicalComplex (presentedOrdinaryReduction S B F h)
            (.up ℤ)).app P =
        (NatIso.mapHomologicalComplex (D.ordinaryAssoc B h k) (.up ℤ)).hom.app
          (((F ⋙ systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (NatTrans.mapHomologicalComplex (presentedOrdinaryReduction S B F (h.trans k))
            (.up ℤ)).app P := by
      ext i : 1
      exact systemOrdinaryReduction_comp S B D h k (F.obj (P.X i))
    rw [← cancel_mono ((F ⋙ systemEvaluation B r).mapDerivedCategoryFactors.hom.app P)]
    simp only [β, NatTrans.comp_app, Functor.whiskerLeft_app,
      presentedDerivedReduction_rep, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_app]
    erw [← (systemDerivedTensor S B h).map_comp_assoc
      ((F ⋙ systemEvaluation B m).mapDerivedCategoryFactors.inv.app P)
      ((F ⋙ systemEvaluation B m).mapDerivedCategoryFactors.hom.app P),
      Iso.inv_hom_id_app]
    erw [(systemDerivedTensor S B h).map_id, Category.id_comp]
    erw [← reassoc_of% (D.derivedAssoc B h k).hom.naturality
      ((F ⋙ systemEvaluation B n).mapDerivedCategoryFactors.hom.app P)]
    erw [reassoc_of% systemTensorAssoc_rep_all S B D h k
      (((F ⋙ systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P)]
    erw [reassoc_of% (S (B.map (homOfLE h).op)).model.ε.naturality
      ((NatTrans.mapHomologicalComplex (presentedOrdinaryReduction S B F k)
        (.up ℤ)).app P)]
    erw [← DerivedCategory.Q.map_comp, hord, DerivedCategory.Q.map_comp]
    erw [Category.comp_id]
    rfl
  exact NatTrans.congr_app he M

end ExactPresentation
end SheafOfModules
