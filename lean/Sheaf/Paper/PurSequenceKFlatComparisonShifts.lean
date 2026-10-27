/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.PurSequenceKFlatComparisonData
import Sheaf.Paper.PurSequenceReductionUniversal
import Sheaf.Paper.PurSequenceReductionShifts
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # K-flat quotient-sequence comparison and coherent shifts

Source: Stacks 06YY, 06YS, 06YT, 0G7D and 012Z.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory TensorProduct
namespace WeilConjectures

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientFiniteDerivedExtension scalarReductionExtension
  coefficientFiniteReductionModel purSequenceShiftIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem resolutionComparison
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (A : PurSequenceKFlatComparison l E W S O) :
    Nonempty (PurSequenceKFlatResolutionComparison l E W S O A) := by
  classical
  let e (Q : CochainComplex (scalarReductionSource l E W) ℤ) (hQ) (flatQ) :=
    (A.representative Q hQ flatQ).choose
  have he (Q : CochainComplex (scalarReductionSource l E W) ℤ) (hQ) (flatQ) :
      A.reductionCounit.app Q = (e Q hQ flatQ).hom ∧
      CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction Q hQ
        ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q) (e Q hQ flatQ)
        (fun n ↦ (NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).app Q) :=
    (A.representative Q hQ flatQ).choose_spec
  let red (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (q : Q ⟶ P) [QuasiIso q] (hQ) (flatQ) :=
    (S.reduction.mapIso (asIso (DerivedCategory.Q.map q))).symm ≪≫ e Q hQ flatQ
  have red_formula (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (q : Q ⟶ P) [QuasiIso q] (hQ) (flatQ) :
      (red P Q q hQ flatQ).hom =
        inv (S.reduction.map (DerivedCategory.Q.map q)) ≫ A.reductionCounit.app Q := by
    simp only [red, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv,
      Functor.map_inv, (he Q hQ flatQ).1]
  have pull_formula (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (q : Q ⟶ P) [QuasiIso q] (hQ) (flatQ) :
      (A.α.app (DerivedCategory.Q.obj P) ≪≫ red P Q q hQ flatQ).hom =
        inv (A.L.map (DerivedCategory.Q.map q)) ≫ A.ε.app Q := by
    rw [Iso.trans_hom, red_formula P Q q hQ flatQ, A.comparison]
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply (cancel_epi (A.L.map (DerivedCategory.Q.map q))).1
    simp only [IsIso.hom_inv_id_assoc, Iso.app_hom]
    rw [A.α.hom.naturality_assoc]
    simp
  have natural (P P' Q Q' : CochainComplex (scalarReductionSource l E W) ℤ)
      (q : Q ⟶ P) (q' : Q' ⟶ P') [QuasiIso q] [QuasiIso q']
      (hQ) (flatQ) (hQ') (flatQ') (v : Q ⟶ Q') (h : P ⟶ P')
      (sq : v ≫ q' = q ≫ h) :
      (red P Q q hQ flatQ).hom ≫ DerivedCategory.Q.map
          ((O.pullback.mapHomologicalComplex (.up ℤ)).map v) =
        S.reduction.map (DerivedCategory.Q.map h) ≫ (red P' Q' q' hQ' flatQ').hom := by
    rw [red_formula P Q q hQ flatQ, red_formula P' Q' q' hQ' flatQ']
    apply (cancel_epi (S.reduction.map (DerivedCategory.Q.map q))).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [← S.reduction.map_comp, ← DerivedCategory.Q.map_comp, ← sq,
      DerivedCategory.Q.map_comp, S.reduction.map_comp]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact (A.reductionCounit.naturality v).symm
  refine ⟨{
    pullback := fun P Q q _ hQ flatQ ↦ A.α.app (DerivedCategory.Q.obj P) ≪≫
      red P Q q hQ flatQ
    reduction := red
    pullback_formula := pull_formula
    reduction_formula := red_formula
    comparison := by intros; rfl
    maps := ?_
    finite_evaluation := ?_
    same_comparison := ?_
    three := ?_ }⟩
  · intro P P' Q Q' q q' _ _ hQ flatQ hQ' flatQ' v h sq
    refine ⟨?_, natural P P' Q Q' q q' hQ flatQ hQ' flatQ' v h sq⟩
    dsimp only [Iso.trans_hom, Iso.app_hom]
    rw [Category.assoc, natural P P' Q Q' q q' hQ flatQ hQ' flatQ' v h sq,
      ← Category.assoc, ← A.α.hom.naturality]
    simp only [Category.assoc]
  · intro P Q q _ hQ flatQ n
    dsimp only [red, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv]
    rw [Functor.map_comp, Functor.map_inv]
    have hn := (he Q hQ flatQ).2.1 n
    simp only [Category.assoc, Iso.app_hom] at hn ⊢
    rw [hn]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply (cancel_epi ((coefficientSequenceDerivedEvaluation l E W n).map
      (S.reduction.map (DerivedCategory.Q.map q)))).1
    simp only [Functor.map_inv, IsIso.hom_inv_id_assoc]
    have hnatur := (S.reductionEvaluation n).hom.naturality_assoc
      (DerivedCategory.Q.map q)
      (inv ((coefficientFiniteDerivedExtension l E W n).map (DerivedCategory.Q.map q)))
    dsimp only [Functor.comp_map] at hnatur
    rw [hnatur]
    simp
  · intro P Q Q' q q' _ _ hQ flatQ hQ' flatQ'
    ext
    simp
  · intro P Q Q' Q'' q q' q'' _ _ _ hQ flatQ hQ' flatQ' hQ'' flatQ''
    ext
    simp

private theorem shiftKFlat
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (r : ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
      (Q⟦r⟧) := by
  let R := completedIntegralCommRingSheafUnrestricted l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro T hT
  have ht := hQ T hT
  have hs : (CochainComplex.mapBifunctor T Q (MonoidalCategory.curriedTensor _)⟦r⟧).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
    rw [← HomotopyCategory.shift_quotient_obj]
    exact (HomotopyCategory.subcategoryAcyclic (scalarReductionSource l E W)).le_shift r _ ht
  intro i
  exact (hs i).of_iso
    (CochainComplex.mapBifunctorShift₂Iso T Q (MonoidalCategory.curriedTensor _) r).symm

set_option linter.unusedVariables false in
/-- The quotient-projection comparison is normalized on a single K-flat strict system
and preserves the specified cochain shifts.
Source: Stacks 06YY, 06YS, 06YT, 0G7D; homology.tex, Tag 012Z; blueprint
`sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`
(blueprint: lem-pur-sequence-kflat-comparison-shifts).

Proof, following the node:
1. For the ringed constant-system projection, ordinary pullback is the strict system
Q tensor B_n, with differential d_Q tensor 1 and quotient transition 1 tensor rho.
Apply lem-weil-pbc-ringed-topoi-derived-pullback to obtain the universal counit,
which is invertible on flat-term K-flat complexes.
2. By lem-sp-strict-coefficient-tensor-descent, both this universal functor and the
supplied calculus reduction are normalized descents of that same resolving functor.
Flat-term resolutions exist by lem-pc-kflat-resolution. Uniqueness of descent gives
alpha, uniquely characterized by its counit square, on all derived morphisms.
3. For a resolution q, compose the counit with the inverse of L(Qq), respectively
R(Qq). Naturality gives the squares for maps of resolutions; cancellation gives
three-resolution coherence. Exact evaluation and lem-pur-derived-change-of-rings
give the canonical finite comparison and retain the actual quotient transitions.
4. On T^p tensor Q^(q+r), multiply by (-1)^(r*p). The source differential has
coefficients 1 and (-1)^(p+r); the target shifted differential has coefficients
(-1)^r and (-1)^(r+p). The sign on the first summand changes by (-1)^r,
so the displayed map intertwines both differentials and is its own inverse.
The summand formula commutes with maps and extends to the unbounded direct sum.
5. An acyclic T tensors acyclically with Q; step 4 identifies the tensor with Q[r]
with a shift of this acyclic complex. Thus Q[r] remains K-flat. Its terms are the
same reindexed flat modules. Shifting preserves quasi-isomorphisms, so q[r] is
again a flat-term K-flat resolution.
6. Ordinary pullback and every finite scalar extension shift by the identity on
Q^(i+r) tensor B_n, with differential (-1)^r(d_Q tensor 1). The resolution maps
u^(i+r) tensor 1 and transitions 1 tensor rho commute with those identities.
Alpha is the identity on this common model; descent gives the same square for
all derived inputs and morphisms.
7. At zero the signs are 1, addition multiplies (-1)^(r*p) and (-1)^(s*p) to
(-1)^((r+s)*p), and inverse shifts give 1. These are precisely the zero/addition
coherences in CommShift, including inverse shifts. No coefficient-map flatness,
boundedness, completeness or normalized-system assumption enters the argument. -/
theorem purSequenceKFlatComparisonShifts
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W) :
    (∃ A : PurSequenceKFlatComparison l E W S O,
      Nonempty (PurSequenceKFlatResolutionComparison l E W S O A) ∧
      Nonempty (PurSequenceKFlatShiftComparison l E W S O A)) ∧
    (∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (q : Q ⟶ P) [QuasiIso q]
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
      (flatQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          (Q.X i)) (r : ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          (Q⟦r⟧) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          ((Q⟦r⟧).X i)) ∧ QuasiIso (q⟦r⟧')) ∧
    (∃ s : ∀ T : CochainComplex (scalarReductionSource l E W) ℤ,
        (purSequenceTensorRight l E W T).CommShift ℤ,
      (∀ T, PurSequenceTensorShiftFormula l E W T (s T)) ∧
      ∀ (T T' : CochainComplex (scalarReductionSource l E W) ℤ) (f : T ⟶ T')
        (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ),
        (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).map (Prod.mkHom f (𝟙 (Q⟦r⟧))) ≫
          (purSequenceShiftIso (purSequenceTensorRight l E W T') (s T') r).hom.app Q =
        (purSequenceShiftIso (purSequenceTensorRight l E W T) (s T) r).hom.app Q ≫
          ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).map (Prod.mkHom f (𝟙 Q)))⟦r⟧') := by
  obtain ⟨ε, hε, hr⟩ := purSequenceReductionUniversal l E W F hl S hS O
  let A : PurSequenceKFlatComparison l E W S O := {
    L := S.reduction
    ε := ε
    universal := hε
    α := Iso.refl _
    reductionCounit := ε
    comparison := by simp
    reductionUniversal := hε
    representative := hr
    unique := by
      intro β hb
      apply Iso.ext
      have := hε
      apply S.reduction.leftDerived_ext ε
        (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ))
      simpa using hb.symm }
  refine ⟨⟨A, resolutionComparison l E W S O A,
    purSequenceReductionShifts l E W F hl S hS O A⟩, ?_, ?_⟩
  · intro P Q q _ hQ flatQ r
    exact ⟨shiftKFlat l E W Q hQ r, (fun i ↦ flatQ (i + r)), inferInstance⟩
  · let R := completedIntegralCommRingSheafUnrestricted l E W
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    let B := MonoidalCategory.curriedTensor (scalarReductionSource l E W)
    have total (T Q : CochainComplex (scalarReductionSource l E W) ℤ) :
        CochainComplex.HasMapBifunctor T Q B := inferInstance
    have : B.Additive := inferInstance
    have : ∀ M, (B.obj M).Additive := fun _ ↦ inferInstance
    let e (T : CochainComplex (scalarReductionSource l E W) ℤ) :
        B.map₂CochainComplex.obj T ≅ purSequenceTensorRight l E W T :=
      (Functor.currying.unitIso.app B.map₂CochainComplex).app T
    let hs (T : CochainComplex (scalarReductionSource l E W) ℤ) :
        (purSequenceTensorRight l E W T).CommShift ℤ :=
      Functor.CommShift.ofIso (e T) ℤ
    have hid (T Q : CochainComplex (scalarReductionSource l E W) ℤ) :
        HomologicalComplex.mapBifunctorMap (𝟙 T) (𝟙 Q) B (.up ℤ) = 𝟙 _ := by
      simp [HomologicalComplex.mapBifunctorMap]
    have hsmul {M N : scalarReductionSource l E W} (a : ℤ) (f : M ⟶ N)
        (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
        (a • f).val.app V x = a • f.val.app V x := by
      change (a • f.val).app V x = _
      rw [PresheafOfModules.zsmul_app]
      rfl
    have hshift (T Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ) :
        (purSequenceShiftIso (purSequenceTensorRight l E W T) (hs T) r).hom.app Q =
          (CochainComplex.mapBifunctorShift₂Iso T Q B r).hom := by
      simp only [purSequenceShiftIso, hs,
        Functor.CommShift.ofIso_commShiftIso_hom_app]
      change 𝟙 _ ≫ ((B.map₂CochainComplex.obj T).commShiftIso r).hom.app Q ≫
        (shiftFunctor _ r).map (𝟙 _) = _
      simp only [Category.id_comp]
      rfl
    refine ⟨hs, ?_, ?_⟩
    · intro T
      unfold PurSequenceTensorShiftFormula
      intro Q r p q k hpq V x y
      have h := CochainComplex.ι_mapBifunctorShift₂Iso_hom_f T Q B r p q k hpq
        (q + r) (k + r) rfl rfl
      simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
        Iso.refl_hom, Iso.refl_inv, Category.comp_id] at h
      erw [(B.obj (T.X p)).map_id] at h
      simp only [Units.smul_def, Category.id_comp] at h
      let z := ((SheafOfModules.tensorObjIsoSheafification (R := R)
        (T.X p) (Q.X (q + r))).inv.val.app V)
        (((PresheafOfModules.sheafificationAdjunction.{max u (t+1)}
          (𝟙 ((sheafCompose (Scheme.ProEt.topology W)
            (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
          ((T.X p).val ⊗ (Q.X (q + r)).val)).app V
          (x ⊗ₜ[R.obj.obj V] y))
      have hh := congrArg (fun f ↦ f.val.app V z) h
      simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply, hsmul, Int.mul_comm] at hh
      rw [hshift]
      change (((CochainComplex.mapBifunctorShift₂Iso T Q B r).hom.f k).val.app V)
          ((CochainComplex.ιMapBifunctor T (Q⟦r⟧) B p q k hpq).val.app V z) =
        (r * p).negOnePow •
          ((CochainComplex.ιMapBifunctor T Q B p (q + r) (k + r) _).val.app V z)
      change _ = ((r * p).negOnePow : ℤ) •
        ((CochainComplex.ιMapBifunctor T Q B p (q + r) (k + r) _).val.app V z)
      convert hh using 1 <;> rfl
    · intro T T' f Q r
      have ht := NatTrans.shift_app_comm (B.map₂CochainComplex.map f) r Q
      simp only [hshift]
      change (HomologicalComplex.mapBifunctorMap f (𝟙 (Q⟦r⟧)) B (.up ℤ) ≫
          HomologicalComplex.mapBifunctorMap (𝟙 T') (𝟙 (Q⟦r⟧)) B (.up ℤ)) ≫
            (CochainComplex.mapBifunctorShift₂Iso T' Q B r).hom =
        (CochainComplex.mapBifunctorShift₂Iso T Q B r).hom ≫
          (shiftFunctor _ r).map (HomologicalComplex.mapBifunctorMap f (𝟙 Q) B (.up ℤ) ≫
            HomologicalComplex.mapBifunctorMap (𝟙 T') (𝟙 Q) B (.up ℤ))
      rw [hid, Category.comp_id, hid, Category.comp_id]
      exact ht.symm

end WeilConjectures
