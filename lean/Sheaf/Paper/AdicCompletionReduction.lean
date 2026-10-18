/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NH and D4
-/
module

public import Sheaf.Paper.AdicReductionAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.KoszulQuotientLimit
import Sheaf.Paper.KoszulCompletionScalarComparison
import Sheaf.Paper.NilpotentKoszulCompletionUnit

/-!
# Reduction of adic completion

Source: Weil conjectures blueprint, proper base change, order 1260,
`lemma-weil-pbc-adic-completion-reduction.md`
(blueprint: lemma-weil-pbc-adic-completion-reduction).

The completion object and its evaluation are those of the landed strict product-cone
construction. Its reduction is computed on an arbitrary K-flat model of that object.
The comparison is defined by the derived scalar adjunction, using its unit, so the
isomorphism assertion concerns the specified evaluation map. Positive level a is n+1.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme

set_option linter.style.haveILetI false in
/-- Naturality of the exact scalar-restriction localization comparison.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction).
Proof: this is the inverse naturality square of mapDerivedCategoryFactors. -/
private theorem adicDerivedRestrictFactors_naturality (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ}
    (f : P ⟶ Q) :
    (adicLocalization X A).map
        (((SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) ≫ (adicDerivedRestrictFactors X φ Q).inv =
      (adicDerivedRestrictFactors X φ P).inv ≫
        (adicDerivedRestrict X φ).map ((adicLocalization X B).map f) := by
  have : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X A))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X B))
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  exact (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapDerivedCategoryFactors
    |>.inv.naturality f

/-- Evaluation from the specified strict product-cone limit at level n+1.
Source: order 1260, statement (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionEvaluation (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ) :
    adicCompletionObject X d M ⟶ adicReductionSequence X d M n :=
  (adicLocalization X Λ).map
    (adicCompletionProjection X d M ≫ Pi.π (adicReductionComplex X d M) n)

/-- The adjoint of evaluation, with the quotient coefficient action retained.
Source: order 1260, displayed map (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionReduction (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (n : ℕ) :
    adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶
      adicReduction X d M ⟨n + 1, Nat.succ_pos n⟩ :=
  (adicReductionHomEquiv X d N n _).symm
    (adicCompletionEvaluation X d M n ≫
      (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
        (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).inv)

/-- Reduction of the completion unit is a right inverse of evaluation's adjoint.
Source: blueprint order 1260, final proof sentence; evaluate the completion unit and
apply injectivity of the scalar Hom equivalence.
(blueprint: lem-weil-pbc-adic-completion-reduction-restricted). -/
private theorem adicCompletionReduction_unit (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (n : ℕ) :
    adicReductionMap X d M N n (adicCompletionMap X d M) ≫
      adicCompletionReduction X d M N n = 𝟙 _ := by
  let R := adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  apply (adicReductionHomEquiv X d M n _).injective
  change adicReductionDerivedUnit X d M n ≫ R.map _ =
    adicReductionDerivedUnit X d M n ≫ R.map (𝟙 _)
  rw [Functor.map_comp, ← Category.assoc, adicReductionMap_unit]
  have he : adicReductionDerivedUnit X d N n ≫
      R.map (adicCompletionReduction X d M N n) =
        adicCompletionEvaluation X d M n ≫
          (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
            (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).inv :=
    (adicReductionHomEquiv X d N n _).apply_symm_apply _
  rw [Category.assoc, he, ← Category.assoc]
  rw [show adicCompletionMap X d M ≫ adicCompletionEvaluation X d M n =
      M.realization.inv ≫ (adicLocalization X Λ).map
        (adicReductionAugmentation X d M n) from adicCompletionMap_projection X d M n]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact Category.assoc _ _ _

/-- Perfect scalar comparison identifies reduction of the Koszul completion unit with
its nilpotent-quotient counterpart. The graded tower calculation makes that unit an
isomorphism. The adjunction unit identity then makes the specified evaluation adjoint
its inverse. Source: order 1260, proof steps 1--5
(blueprint: lem-weil-pbc-adic-completion-reduction-restricted). -/
theorem adicCompletionReduction_restricted_isIso (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (n : ℕ) :
    IsIso ((adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map
      (adicCompletionReduction X d M N n)) := by
  classical
  obtain ⟨r, f, hf⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  have hf' : Ideal.span (Set.range f) = d.ideal := hf
  obtain ⟨v, w, c, _, _, _, _, _, _, hc, _⟩ := koszulQuotientLimit X Λ d r f hf'
  obtain ⟨P⟩ := adicKFlatModel_exists X Λ
    ((adicLocalization X Λ).obj (koszulCompletionComplex X Λ r f M.complex))
  obtain ⟨e, he⟩ := koszulCompletionScalarComparison X d r f M P n
  have hb (j : Fin r) :
      (Ideal.Quotient.mk (d.ideal ^ (n + 1)) (f j)) ^ (n + 1) = 0 := by
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.pow_mem_pow
    rw [← hf']
    exact Ideal.subset_span (Set.mem_range_self j)
  have hu : IsIso ((adicLocalization X (Λ ⧸ d.ideal ^ (n + 1))).map
      (koszulCompletionUnitComplex X (Λ ⧸ d.ideal ^ (n + 1)) r
        (fun j ↦ Ideal.Quotient.mk (d.ideal ^ (n + 1)) (f j))
        (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex))) :=
    nilpotentKoszulCompletionUnit_isIso X _ r _ (n + 1) (Nat.succ_pos n) hb _
  have hcomp : IsIso (adicReductionMap X d M P n
      (M.realization.inv ≫ (adicLocalization X Λ).map
        (koszulCompletionUnitComplex X Λ r f M.complex)) ≫ e.hom) := by
    rw [he]
    exact hu
  have hi := (isIso_comp_right_iff _ e.hom).1 hcomp
  have hj := adicReductionMap_isIso X d P N n (c K M).hom
  have hk : IsIso (adicReductionMap X d M N n (adicCompletionMap X d M)) := by
    rw [← hc K M, adicReductionMap_comp X d M P N]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hi hj
  have hl : IsIso (adicCompletionReduction X d M N n) := by
    apply (isIso_comp_left_iff
      (adicReductionMap X d M N n (adicCompletionMap X d M)) _).1
    rw [adicCompletionReduction_unit]
    infer_instance
  infer_instance

set_option linter.style.haveILetI false in
/-- Exact restriction is conservative on the derived categories. Reflect the vanishing of
the cone degree by degree through the exact underlying sheaf functor, using derived
change of rings. Source: order 1260, proof step 6
(blueprint: lem-weil-pbc-adic-derived-restrict-conservative). -/
theorem adicDerivedRestrict_reflectsIsomorphisms (X : Scheme.{t})
    {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :
    ∀ {Y Z : proEtaleDerivedCategory X B} (f : Y ⟶ Z),
      IsIso ((adicDerivedRestrict (X := X) (A := A) (B := B) φ).map f) → IsIso f := by
  have hs : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  have hw : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  letI : HasDerivedCategory.{t + 2, t + 1, t + 2}
      (SheafOfModules.{t + 1} (adicModuleRing X A)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{t + 2, t + 1, t + 2}
      (SheafOfModules.{t + 1} (adicModuleRing X B)) :=
    HasDerivedCategory.standard _
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  let UA := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X A)
  let UB := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X B)
  let F := SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)
  letI : F.Additive := inferInstance
  have hF : F.ReflectsIsomorphisms := by
    have hcomp : (F ⋙ UA).ReflectsIsomorphisms := by
      change UB.ReflectsIsomorphisms
      infer_instance
    letI := hcomp
    exact reflectsIsomorphisms_of_comp F UA
  letI := hF
  intro Y Z f hf
  change IsIso ((F.mapDerivedCategory).map f) at hf
  rw [DerivedCategory.isIso_iff]
  intro i
  have hi : IsIso (F.map ((DerivedCategory.homologyFunctor
      (SheafOfModules.{t + 1} (adicModuleRing X B)) i).map f)) := by
    exact (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) f).2
      (by
        change IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{t + 1} (adicModuleRing X A)) i).map
          ((F.mapDerivedCategory).map f))
        infer_instance)
  exact isIso_of_reflects_iso _ F

set_option linter.style.haveILetI false
/-- Every finite reduction of completion is the original reduction via evaluation's
adjoint. The restricted Koszul calculation and conservativity of exact scalar restriction
imply the unreduced isomorphism (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
theorem adicCompletionReduction_isIso (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (n : ℕ) : IsIso (adicCompletionReduction X d M N n) := by
  letI := adicCompletionReduction_restricted_isIso X d M N n
  letI : (adicDerivedRestrict X
      (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).ReflectsIsomorphisms :=
    ⟨fun f hf ↦ adicDerivedRestrict_reflectsIsomorphisms X
      (Ideal.Quotient.mk (d.ideal ^ (n + 1))) f hf⟩
  exact isIso_of_reflects_iso _ (adicDerivedRestrict X
    (Ideal.Quotient.mk (d.ideal ^ (n + 1))))

/-- The strict reduction of a chain map between the chosen models.
Source: order 1260, functoriality in proof step 6
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionComplexMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionComplex X d M n ⟶ adicReductionComplex X d M' n :=
  ((SheafOfModules.restrictScalars.{t + 1}
    (adicModuleMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (adicChangeHom X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) f)

/-- Quotient transitions are natural in the original complex.
Source: order 1260, proof step 6.
Proof: both paths send r tensor m to q(r) tensor f(m). The local tensor generators
characterize the sheaf maps and therefore their chain maps uniquely.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicReductionComplexMap_step (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionComplexMap X d M M' f (n + 1) ≫
        adicReductionComplexStep X d M' n =
      adicReductionComplexStep X d M n ≫ adicReductionComplexMap X d M M' f n := by
  exact adicTransitionComplex_naturality X d.ideal f
    ⟨n + 1 + 1, Nat.succ_pos _⟩ ⟨n + 1, Nat.succ_pos _⟩ (Nat.le_succ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Quotient augmentation commutes with maps of the chosen models.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction).
Proof: naturality of module sheafification applied to the sectionwise tensor map sends
one tensor m to one tensor f(m). The uniquely specified augmentation has that formula. -/
private theorem adicReductionAugmentation_naturality (X : Scheme.{t})
    {Λ : Type t} [CommRing Λ] (d : CompleteCoefficientDatum Λ)
    {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionAugmentation X d M n ≫ adicReductionComplexMap X d M M' f n =
      f ≫ adicReductionAugmentation X d M' n := by
  have : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  ext p U m
  have hM := (Classical.choose_spec (adicReductionAugmentation_exists X d M n)).1 p U m
  have hM' := (Classical.choose_spec (adicReductionAugmentation_exists X d M' n)).1
    p U ((f.f p).val.app U m)
  change (SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} (adicConstantMap X
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) (M.complex.X p) (f.f p)).val.app U
      ((adicReductionAugmentation X d M n).f p |>.val.app U m) = _
  dsimp only [adicReductionAugmentation] at ⊢
  rw [hM]
  change _ = ((adicReductionAugmentation X d M' n).f p).val.app U
    ((f.f p).val.app U m)
  dsimp only [adicReductionAugmentation] at ⊢
  rw [hM']
  let φ := adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let a : SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ (M.complex.X p) ⟶
      SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ (M'.complex.X p) :=
    { app := fun W ↦ (ModuleCat.extendScalars (φ.hom.app W).hom).map ((f.f p).val.app W)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{t, t + 1, t + 1} φ _ (f.f p) }
  have hn := (PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1))).obj)).unit.naturality a
  have hx := congrArg (fun g ↦ g.app U
    ((1 : (adicConstantRing X (Λ ⧸ d.ideal ^ (n + 1))).obj.obj U)
      ⊗ₜ[(adicConstantRing X Λ).obj.obj U, (φ.hom.app U).hom] m)) hn
  change (((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1))).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ (M'.complex.X p))).app U
        ((ModuleCat.extendScalars (φ.hom.app U).hom).map ((f.f p).val.app U)
          ((1 : (adicConstantRing X (Λ ⧸ d.ideal ^ (n + 1))).obj.obj U)
            ⊗ₜ[(adicConstantRing X Λ).obj.obj U, (φ.hom.app U).hom] m))) = _ at hx
  erw [ModuleCat.ExtendScalars.map_tmul] at hx
  exact hx.symm

/-- Completion of a model map, using the same product map in both cone coordinates.
Source: order 1260, proof step 6; the strict cone construction at order 1258
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionModelMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) :
    adicCompletionObject X d M ⟶ adicCompletionObject X d M' :=
  (adicLocalization X Λ).map
    (adicCompletionTowerMap X d M M' (adicReductionComplexMap X d M M' f)
      (adicReductionComplexMap_step X d M M' f))

/-- The abstract reduction of a represented morphism is its strict scalar extension.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction).
Proof: apply the defining Hom equivalence. Naturality of the quotient augmentation and
of the exact scalar-restriction comparison identifies the two resulting units. -/
private theorem adicReductionMap_model (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionMap X d M M' n
        (M.realization.inv ≫ (adicLocalization X Λ).map f ≫ M'.realization.hom) =
      (adicLocalization X (Λ ⧸ d.ideal ^ (n + 1))).map
        (adicChangeHom X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) f) := by
  apply (adicReductionHomEquiv X d M n _).injective
  simp only [adicReductionMap, Equiv.apply_symm_apply]
  change (M.realization.inv ≫ (adicLocalization X Λ).map f ≫ M'.realization.hom) ≫
      adicReductionDerivedUnit X d M' n =
    adicReductionDerivedUnit X d M n ≫
      (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map _
  dsimp only [adicReductionDerivedUnit]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← adicDerivedRestrictFactors_naturality]
  simp only [← Category.assoc, ← Functor.map_comp]
  congr 2
  exact (adicLocalization X Λ).congr_map
    (adicReductionAugmentation_naturality X d M M' f n).symm

/-- Evaluation on the strict cone commutes with a map of models.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction).
Proof: use the first coordinate formula of adicCompletionTowerMap_exists, compose with
one product projection, and localize. -/
private theorem adicCompletionEvaluation_naturality (X : Scheme.{t})
    {Λ : Type t} [CommRing Λ] (d : CompleteCoefficientDatum Λ)
    {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicCompletionModelMap X d M M' f ≫ adicCompletionEvaluation X d M' n =
      adicCompletionEvaluation X d M n ≫
        (adicLocalization X Λ).map (adicReductionComplexMap X d M M' f n) := by
  have h := (Classical.choose_spec (adicCompletionTowerMap_exists X d M M'
    (adicReductionComplexMap X d M M' f) (adicReductionComplexMap_step X d M M' f))).1.1
  change (adicLocalization X Λ).map _ ≫ (adicLocalization X Λ).map _ =
    (adicLocalization X Λ).map _ ≫ (adicLocalization X Λ).map _
  simp only [← Functor.map_comp]
  apply (adicLocalization X Λ).congr_map
  change adicCompletionTowerMap X d M M'
    (adicReductionComplexMap X d M M' f) (adicReductionComplexMap_step X d M M' f) ≫ _ = _ at h
  rw [← Category.assoc, h, Category.assoc, Limits.Pi.map_π, ← Category.assoc]

/-- The comparison is natural on all K-flat representatives. Since those representatives
localize to the derived category, this is functoriality in K, including the inverse maps
of quasi-isomorphisms; no particular resolution or boundedness is required.
Source: order 1260, functoriality clause and proof step 6.
Proof: scalar extension's unit is natural, with formula m ↦ 1 tensor m. Evaluation from
the cone is natural for the product map in both coordinates, by
adicCompletionTowerMap_exists. Thus the two sides have the same adjoint under
adicReductionHomEquiv, namely evaluation followed by the scalar-restricted reduction
of f. Injectivity of that equivalence gives equality. K-flat resolutions and
lem-pur-derived-change-of-rings identify model changes canonically, so the equality
passes through roofs and inverts quasi-isomorphisms.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicCompletionReduction_naturality (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (N' : AdicKFlatModel X Λ (adicCompletionObject X d M'))
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionMap X d N N' n (adicCompletionModelMap X d M M' f) ≫
        adicCompletionReduction X d M' N' n =
      adicCompletionReduction X d M N n ≫
        adicReductionMap X d M M' n
          (M.realization.inv ≫ (adicLocalization X Λ).map f ≫ M'.realization.hom) := by
  let R := adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  have hunit (A : proEtaleDerivedCategory X Λ)
      (P : AdicKFlatModel X Λ A)
      (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1)))
      (g : A ⟶ R.obj H) :
      adicReductionDerivedUnit X d P n ≫
        R.map ((adicReductionHomEquiv X d P n H).symm g) = g :=
    (adicReductionHomEquiv X d P n H).apply_symm_apply g
  apply (adicReductionHomEquiv X d N n _).injective
  change adicReductionDerivedUnit X d N n ≫ R.map _ =
    adicReductionDerivedUnit X d N n ≫ R.map _
  simp only [Functor.map_comp, ← Category.assoc]
  rw [show adicReductionDerivedUnit X d N n ≫
      R.map (adicReductionMap X d N N' n (adicCompletionModelMap X d M M' f)) =
      adicCompletionModelMap X d M M' f ≫ adicReductionDerivedUnit X d N' n from
    hunit _ N _ _]
  simp only [Category.assoc]
  rw [show adicReductionDerivedUnit X d N' n ≫
      R.map (adicCompletionReduction X d M' N' n) =
      adicCompletionEvaluation X d M' n ≫
        (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
          (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M'.complex)).inv from
    hunit _ N' _ _]
  rw [← Category.assoc, adicCompletionEvaluation_naturality]
  rw [Category.assoc]
  change adicCompletionEvaluation X d M n ≫
    (adicLocalization X Λ).map
      (((SheafOfModules.restrictScalars.{t + 1}
          (adicModuleMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
        (adicChangeHom X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) f)) ≫ _ = _
  rw [adicDerivedRestrictFactors_naturality]
  rw [adicReductionMap_model]
  simp only [← Category.assoc]
  congr 1
  exact (hunit _ N _ _).symm


end AlgebraicGeometry.Scheme
