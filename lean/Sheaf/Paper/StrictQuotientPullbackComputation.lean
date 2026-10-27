/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.CompletedTowerPullback
import all Sheaf.Paper.CompletedTowerPullback
import all Sheaf.Paper.AdicCoefficientDatum

/-! # Resolved strict quotient pullback with its specified augmentation

Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, completed-pullback invocation;
Stacks Tag 06XN, dual part (blueprint: lem-cbc-strict-quotient-pullback-computation).
The positive exponent n+1 is indexed by n : ℕ, as in the coefficient datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- A K-flat flat-term representative over the actual completed coefficient sheaf.
Flatness means exactness of tensoring, without identifying site universes.
Source: Stacks 06XN and 06YS (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
structure CbcStrictKFlatRepresentative (T : Scheme.{u}) where
  complex : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ
  kflat : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T d) complex
  flat : ∀ q : ℤ, exactFunctor _ _
    (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory (pbcAdicCompletion T d))
      (complex.X q))

/-- The existing strict quotient complex, with its existing quotient transitions.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictReduction (T : Scheme.{u}) := completedReductionComplexTowerFunctor T d

/-- The constant strict complex, with identity transitions.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictDelta (T : Scheme.{u}) :=
  (completedTowerConstant d T).mapHomologicalComplex (.up ℤ)

/-- The original quotient augmentation, induced by the section map x ↦ 1 tensor x.
The coefficient-first convention is the scalar-extension presentation of x tensor 1.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictAugmentation (T : Scheme.{u})
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    (cbcStrictDelta d T).obj P ⟶ (cbcStrictReduction d T).obj P :=
  letI := completedReductionModuleTowerFunctor_additive T d
  (NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T) (.up ℤ)).app P

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Apply the projection-defined module pullback to a strict tower complex.
Source: Stacks 099N (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictPull := (completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)

variable (LF : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ : DerivedCategory.Qh ⋙ LF ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

/-- The specified universal counit on actual strict cochain representatives.
Source: Stacks 06XN (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictCounit (H : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :=
  Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) LF τ H

/-- A strict quasi-isomorphic resolution with objectwise K-flat flat-term source.
No lift of the quotient augmentation is part of this data.
Source: Stacks 06XN, 06YS (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
structure CbcStrictQuotientResolution (P : CbcStrictKFlatRepresentative d Y) where
  complex : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ
  arrow : complex ⟶ (cbcStrictReduction d Y).obj P.complex
  quasiIso : QuasiIso arrow
  kflat : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
    (R := pbcAdicCompletion Y d)
    ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
      (op n)).mapHomologicalComplex (.up ℤ)).obj complex)
  flat : ∀ (n : ℕ) (q : ℤ), exactFunctor _ _
    (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory (pbcAdicCompletion Y d))
      (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).obj (complex.X q)))

/-- The counit formula chi_r = tau_H composed with L(Qr) inverse.
Its inverse of L(Qr) exists because r is a quasi-isomorphism, independently of G(r).
Source: Stacks 06XN (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictResolutionMap (P : CbcStrictKFlatRepresentative d Y)
    (r : CbcStrictQuotientResolution d P) :
    LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P.complex)) ⟶
      DerivedCategory.Q.obj ((cbcStrictPull d g).obj r.complex) :=
  letI := r.quasiIso
  inv (LF.map (DerivedCategory.Q.map r.arrow)) ≫ cbcStrictCounit d g LF τ r.complex

/-- The augmentation transported through the invertible counit on the constant complex.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictPulledAugmentation (P : CbcStrictKFlatRepresentative d Y)
    (δ : LF.obj (DerivedCategory.Q.obj ((cbcStrictDelta d Y).obj P.complex)) ≅
      DerivedCategory.Q.obj ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex))) :
    DerivedCategory.Q.obj ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex)) ⟶
      LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P.complex)) :=
  δ.inv ≫ LF.map (DerivedCategory.Q.map (cbcStrictAugmentation d Y P.complex))

/-- The representative map B(f) on pulled-back constant complexes.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictConstantMap {P P' : CbcStrictKFlatRepresentative d Y}
    (f : P.complex ⟶ P'.complex) :=
  DerivedCategory.Q.map ((cbcStrictPull d g).map ((cbcStrictDelta d Y).map f))

/-- The representative map D(f) on derived pulled-back quotient complexes.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictReductionMap {P P' : CbcStrictKFlatRepresentative d Y}
    (f : P.complex ⟶ P'.complex) :=
  LF.map (DerivedCategory.Q.map ((cbcStrictReduction d Y).map f))

private theorem counitOnComplex_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    {H K : CochainComplex C ℤ} (f : H ⟶ K) :
    L.map (DerivedCategory.Q.map f) ≫ F.leftDerivedCounitOnComplex L ε K =
      F.leftDerivedCounitOnComplex L ε H ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let π := HomotopyCategory.quotient C (.up ℤ)
  let π' := HomotopyCategory.quotient D (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Fh := F.mapHomotopyCategory (.up ℤ)
  let α : DerivedCategory.Q ⋙ L ⟶ Fc ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv L ≫
      (Functor.associator π DerivedCategory.Qh L).hom ≫ Functor.whiskerLeft π ε ≫
      (Functor.associator π Fh DerivedCategory.Qh).inv ≫
      Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      (Functor.associator Fc π' DerivedCategory.Qh).hom ≫
      Functor.whiskerLeft Fc (DerivedCategory.quotientCompQhIso D).hom
  have h := α.naturality f
  dsimp only [α, π, π', Fc, Fh, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map] at h
  simpa only [Category.id_comp, Category.comp_id, Category.assoc,
    Functor.leftDerivedCounitOnComplex] using h

private theorem inverseSquare
    {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ e'.hom = e.hom ≫ b) : e.inv ≫ a = b ≫ e'.inv := by
  apply (cancel_epi e.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem transportedSquare
    {C : Type*} [Category C] {A B A' B' R R' : C}
    (e : A ≅ B) (e' : A' ≅ B') (a : A ⟶ R) (a' : A' ⟶ R')
    (s : A ⟶ A') (b : B ⟶ B') (r : R ⟶ R')
    (ha : a ≫ r = s ≫ a') (hs : s ≫ e'.hom = e.hom ≫ b) :
    (e.inv ≫ a) ≫ r = b ≫ e'.inv ≫ a' := by
  rw [Category.assoc, ha, ← Category.assoc, inverseSquare e e' s b hs, Category.assoc]

private theorem mappedSquare
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} (a : A ⟶ B) (a' : A' ⟶ B')
    (s : A ⟶ A') (r : B ⟶ B') (h : a ≫ r = s ≫ a') :
    F.map a ≫ F.map r = F.map s ≫ F.map a' := by
  rw [← F.map_comp, h, F.map_comp]

private theorem comparisonAugmentation
    {C : Type*} [Category C] {A B D W : C} (e : A ≅ B) (f : A ≅ D) (w : W ⟶ A) :
    (w ≫ e.hom) ≫ (e.symm ≪≫ f).hom = w ≫ f.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

private theorem comparisonCocycle
    {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (f : A ≅ D) (g : A ≅ E) :
    (e.symm ≪≫ f).hom ≫ (f.symm ≪≫ g).hom = (e.symm ≪≫ g).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

private theorem comparisonSelf
    {C : Type*} [Category C] {A B : C} (e : A ≅ B) :
    (e.symm ≪≫ e).hom = 𝟙 B := by
  exact e.inv_hom_id

private theorem isIsoOfSquare
    {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (a : A ⟶ A') (b : B ⟶ B') [IsIso a]
    (h : a ≫ e'.hom = e.hom ≫ b) : IsIso b := by
  have : IsIso (e.hom ≫ b) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom b

private theorem resolutionAugmentation
    {C : Type*} [Category C] {R H B GH GR : C}
    (w : B ⟶ R) (r : H ⟶ R) [IsIso r] (tH : H ⟶ GH) (tR : R ⟶ GR)
    (t : GH ⟶ GR) (a : B ⟶ GR) (hr : r ≫ tR = tH ≫ t) (ha : w ≫ tR = a) :
    w ≫ (inv r ≫ tH) ≫ t = a := by
  simp only [Category.assoc]
  rw [← hr]
  simpa only [IsIso.inv_hom_id_assoc] using ha

attribute [local irreducible] completedReductionModuleTowerFunctor

/-- Computation on every strict resolution retains the actual quotient augmentation.
Source: blueprint CBC completed-pullback invocation; Stacks 06XN, dual part
(blueprint: lem-cbc-strict-quotient-pullback-computation).

Proof:
1. The existing quotient transitions preserve 1, so the augmentation is a strict chain
map and natural in P. Levelwise G takes Delta P to Delta G(P), with identity transitions.
2. The diagram K-flat replacement theorem supplies the resolving class and invariance
of quasi-isomorphisms on it. Additive G preserves shifts and cones. Apply the resolving-
class theorem. Uniqueness of universal pairs transfers its invertible counit components
at H and Delta P to the specified pair LF,tau.
3. Invert LF(Qr), compose with tau_H, and use counit naturality at r and at a_P.
This gives Q'G(r) chi_r w_P = Q'G(a_P), without inverting tau_R(P) or G(r).
4. The comparison from r to s is chi_r inverse followed by chi_s. Cancellation proves
its compatibility with the augmented maps, its identity and the three-resolution cocycle.
5. Counit naturality and R(f) a_P = a_P' Delta(f) give naturality of w.
6. Derived change of rings makes R(f) a quasi-isomorphism for quasi-isomorphic K-flat
representatives. Tower cohomology is levelwise. Diagram pullback invariance makes B(f)
invertible. Inverting the naturality square proves compatibility with localization and,
by conjugating with chi, with every resolved presentation. -/
theorem strictQuotientPullbackComputation
    (_hpair : LF.IsLeftDerivedFunctor τ
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))) :
    ∃ (δ : ∀ P : CbcStrictKFlatRepresentative d Y,
        LF.obj (DerivedCategory.Q.obj ((cbcStrictDelta d Y).obj P.complex)) ≅
          DerivedCategory.Q.obj
            ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex)))
      (χ : ∀ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P),
        LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P.complex)) ≅
          DerivedCategory.Q.obj ((cbcStrictPull d g).obj r.complex)),
      (∀ P : CbcStrictKFlatRepresentative d Y,
        (δ P).hom = cbcStrictCounit d g LF τ ((cbcStrictDelta d Y).obj P.complex)) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P),
        (χ P r).hom = cbcStrictResolutionMap d g LF τ P r) ∧
      (∀ P : CbcStrictKFlatRepresentative d Y,
        ((completedTowerConstant d X).mapHomologicalComplex (.up ℤ)).obj
            (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P.complex) =
          (cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex)) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P),
        cbcStrictPulledAugmentation d g LF P (δ P) ≫ (χ P r).hom ≫
            DerivedCategory.Q.map ((cbcStrictPull d g).map r.arrow) =
          DerivedCategory.Q.map
            ((cbcStrictPull d g).map (cbcStrictAugmentation d Y P.complex))) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r s : CbcStrictQuotientResolution d P),
        (cbcStrictPulledAugmentation d g LF P (δ P) ≫ (χ P r).hom) ≫
            ((χ P r).symm ≪≫ χ P s).hom =
          cbcStrictPulledAugmentation d g LF P (δ P) ≫ (χ P s).hom) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r s t : CbcStrictQuotientResolution d P),
        ((χ P r).symm ≪≫ χ P s).hom ≫ ((χ P s).symm ≪≫ χ P t).hom =
          ((χ P r).symm ≪≫ χ P t).hom) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P),
        ((χ P r).symm ≪≫ χ P r).hom = 𝟙 _) ∧
      (∀ (P P' : CbcStrictKFlatRepresentative d Y) (f : P.complex ⟶ P'.complex),
        cbcStrictPulledAugmentation d g LF P (δ P) ≫ cbcStrictReductionMap d LF f =
          cbcStrictConstantMap d g f ≫ cbcStrictPulledAugmentation d g LF P' (δ P')) ∧
      (∀ (P P' : CbcStrictKFlatRepresentative d Y) (f : P.complex ⟶ P'.complex),
        QuasiIso f →
        ∃ (b : DerivedCategory.Q.obj
              ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex)) ≅
            DerivedCategory.Q.obj
              ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P'.complex)))
          (e : LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P.complex)) ≅
            LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P'.complex))),
          b.hom = cbcStrictConstantMap d g f ∧ e.hom = cbcStrictReductionMap d LF f ∧
          b.inv ≫ cbcStrictPulledAugmentation d g LF P (δ P) =
            cbcStrictPulledAugmentation d g LF P' (δ P') ≫ e.inv) := by
  let := _hpair
  let := completedReductionModuleTowerFunctor_additive Y d
  let F := completedTowerModulePullback g d
  let := completedTowerModulePullback_finiteLimits g d
  let := completedTowerModulePullback_finiteColimits g d
  have : IsIso τ := exactPullbackCounit_isIso F LF τ
  have hcc (H : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :
      IsIso (cbcStrictCounit d g LF τ H) := by
    exact exactComplexCounit_isIso F LF τ H
  have hq {P P' : CbcStrictKFlatRepresentative d Y} (f : P.complex ⟶ P'.complex)
      (hf : QuasiIso f) : QuasiIso ((cbcStrictReduction d Y).map f) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    apply quasiIso_map_of_functor_eq _ _ (level_complex_eq Y d n.unop) f
    exact quasiIso_composite_map
      (reductionChange Y (completedReductionProjection Y d n.unop))
      (reductionRestrict Y (completedReductionProjection Y d n.unop)) f
      (reductionChange_quasiIso Y (completedReductionProjection Y d n.unop)
        f P.kflat P'.kflat hf)
  have hn {H K : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ}
      (f : H ⟶ K) :
      LF.map (DerivedCategory.Q.map f) ≫ cbcStrictCounit d g LF τ K =
        cbcStrictCounit d g LF τ H ≫
          DerivedCategory.Q.map ((cbcStrictPull d g).map f) := by
    exact counitOnComplex_naturality _ LF τ f
  let δ (P : CbcStrictKFlatRepresentative d Y) :=
    @asIso _ _ _ _ (cbcStrictCounit d g LF τ ((cbcStrictDelta d Y).obj P.complex))
      (hcc _)
  have hresIso (P : CbcStrictKFlatRepresentative d Y)
      (r : CbcStrictQuotientResolution d P) :
      IsIso (cbcStrictResolutionMap d g LF τ P r) := by
    have := r.quasiIso
    have := hcc r.complex
    dsimp only [cbcStrictResolutionMap]
    infer_instance
  let χ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P) :=
    @asIso _ _ _ _ (cbcStrictResolutionMap d g LF τ P r) (hresIso P r)
  have hχ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P) :
      (χ P r).hom = cbcStrictResolutionMap d g LF τ P r := by
    rfl
  have haug (P : CbcStrictKFlatRepresentative d Y) :
      cbcStrictPulledAugmentation d g LF P (δ P) ≫
          cbcStrictCounit d g LF τ ((cbcStrictReduction d Y).obj P.complex) =
        DerivedCategory.Q.map ((cbcStrictPull d g).map
          (cbcStrictAugmentation d Y P.complex)) := by
    dsimp only [cbcStrictPulledAugmentation]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ (δ P).inv ≫ k)
        (hn (cbcStrictAugmentation d Y P.complex))).trans ((δ P).inv_hom_id_assoc _))
  have hnat (P P' : CbcStrictKFlatRepresentative d Y) (f : P.complex ⟶ P'.complex) :
      cbcStrictPulledAugmentation d g LF P (δ P) ≫ cbcStrictReductionMap d LF f =
        cbcStrictConstantMap d g f ≫ cbcStrictPulledAugmentation d g LF P' (δ P') := by
    have ha : cbcStrictAugmentation d Y P.complex ≫ (cbcStrictReduction d Y).map f =
        (cbcStrictDelta d Y).map f ≫ cbcStrictAugmentation d Y P'.complex :=
      (NatTrans.mapHomologicalComplex
        (completedReductionModuleUnit d Y) (.up ℤ)).naturality f |>.symm
    have ht := hn ((cbcStrictDelta d Y).map f)
    have hm : LF.map (DerivedCategory.Q.map (cbcStrictAugmentation d Y P.complex)) ≫
        cbcStrictReductionMap d LF f =
        LF.map (DerivedCategory.Q.map ((cbcStrictDelta d Y).map f)) ≫
          LF.map (DerivedCategory.Q.map (cbcStrictAugmentation d Y P'.complex)) := by
      dsimp only [cbcStrictReductionMap]
      exact mappedSquare (DerivedCategory.Q ⋙ LF)
        (cbcStrictAugmentation d Y P.complex) (cbcStrictAugmentation d Y P'.complex)
        ((cbcStrictDelta d Y).map f) ((cbcStrictReduction d Y).map f) ha
    dsimp only [cbcStrictPulledAugmentation]
    exact transportedSquare (δ P) (δ P') _ _ _ _ _ hm ht
  refine ⟨δ, χ, fun _ ↦ rfl, hχ,
    fun P ↦ completedPullbackConstantComplex_eq g d P.complex, ?_, ?_, ?_, ?_, hnat, ?_⟩
  · intro P r
    have := r.quasiIso
    exact resolutionAugmentation
      (cbcStrictPulledAugmentation d g LF P (δ P))
      (LF.map (DerivedCategory.Q.map r.arrow)) _ _ _ _ (hn r.arrow) (haug P)
  · intro P r s
    exact comparisonAugmentation (χ P r) (χ P s) _
  · intro P r s t
    exact comparisonCocycle (χ P r) (χ P s) (χ P t)
  · intro P r
    exact comparisonSelf (χ P r)
  · intro P P' f hf
    have := hq f hf
    have : IsIso (cbcStrictReductionMap d LF f) := by
      dsimp only [cbcStrictReductionMap]
      infer_instance
    have : IsIso (cbcStrictConstantMap d g f) := by
      have : QuasiIso ((cbcStrictDelta d Y).map f) := by
        have := hf
        dsimp only [cbcStrictDelta]
        infer_instance
      exact isIsoOfSquare (δ P) (δ P')
        (LF.map (DerivedCategory.Q.map ((cbcStrictDelta d Y).map f))) _
        (hn ((cbcStrictDelta d Y).map f))
    refine ⟨asIso (cbcStrictConstantMap d g f), asIso (cbcStrictReductionMap d LF f),
      rfl, rfl, ?_⟩
    exact inverseSquare (asIso (cbcStrictConstantMap d g f))
      (asIso (cbcStrictReductionMap d LF f)) _ _ (hnat P P' f)

end AlgebraicGeometry.Scheme
