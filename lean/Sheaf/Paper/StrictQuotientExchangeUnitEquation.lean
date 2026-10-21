/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.QuotientExchangeScalarComparisons
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import all Sheaf.CategoryTheory.ExchangeMateCube
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.Paper.StrictPerfectTowerProjection
import Sheaf.Paper.StrictReductionPullbackSquare
import Sheaf.Paper.StrictTowerMateEvaluation
import Sheaf.Paper.StrictProjectionCoaugmentation

/-! # The strict perfect-coefficient exchange and its coaugmentation

Source: Stacks Project, sites-cohomology.tex, Tags 0E48 and 0944;
strict augmented perfect-diagram refinement, agent supplied
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation).

All towers are objects of the derived category of strict module diagrams.
The presentation data below fix maps on complexes before localization.

## Main definitions and statements

`strictQuotientExchangeUnitEquation` states the exchange and coaugmentation equations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Keep normalized representative proofs in the public definitions.
set_option backward.proofsInPublic true
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w uData vData wData xData yData zData

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.StrictQuotientExchange

variable {S T X Y : RingedTensorCorner.{u, w}}
  (f : RingedTensorEdge S X) (g : RingedTensorEdge S T)
  (h : RingedTensorEdge X Y) (e : RingedTensorEdge T Y)
  [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
  [PreservesFiniteLimits g.pullback] [PreservesFiniteColimits g.pullback]
  [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
  [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
  [HasDerivedCategory.{w} S.projectionTowers]
  [HasDerivedCategory.{w} T.projectionTowers]
  [HasDerivedCategory.{w} X.projectionTowers]
  [HasDerivedCategory.{w} Y.projectionTowers]

variable [g.pushforward.Additive] [h.pushforward.Additive]
  [HasCountableProducts S.mateDerived] [HasCountableProducts T.mateDerived]
  [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
  {lS : StrictProjectionLimit S} {lT : StrictProjectionLimit T}
  {lX : StrictProjectionLimit X} {lY : StrictProjectionLimit Y}
  {dg : StrictProjectionDirectImage g lT lS} {dh : StrictProjectionDirectImage h lY lX}

variable {f g h e}

/-- Pointwise local perfectness of the strict coefficient sequence.
Source: Stacks 08G5, 0944
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def HasPerfectLevels (A : RingedTensorCorner.{u, w})
    (Q : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ) : Prop :=
  letI : HasSheafify A.topology AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  letI : ∀ U : A.site, HasSheafify (A.topology.over U) AddCommGrpCat.{u} :=
    fun _U ↦ GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  letI : ∀ U : A.site, (A.topology.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _U ↦ inferInstance
  letI : A.topology.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  ∀ n : ℕᵒᵖ, IsPerfectOnRingedSiteOfUniverses.{u, u, 0, w} A.ring
    (DerivedCategory.Q.obj (Q.obj n))

/-- Invertibility of the two canonical projection maps.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def ProjectionIsomorphisms {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh) : Prop :=
  ∀ K : T.mateDerived,
    IsIso (firstProjection q ag K) ∧ IsIso (secondProjection q ah K)

/-- Equality with the actual square mate as a whole strict-tower morphism.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def IsTowerMate {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] : Prop :=
  conjugate q ag ah K = (towerMate f g h e s ag ah).app (input q K)

/-- The ambient coefficient-tensor square mate under normalized evaluation.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def IsEvaluatedMate {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] : Prop :=
  ∀ n : ℕᵒᵖ,
    (ev X lX n).map (conjugate q ag ah K) ≫ (evaluatedTarget q dh K n).hom =
      (evaluatedSource q dg K n).hom ≫
        s.exchange.app ((ev T lT n).obj (input q K))

/-- The strict augmentation and inverse-limit coaugmentation equation.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def HasCoaugmentationEquation {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (jX : ConstantLimit X lX) (jY : ConstantLimit Y lY)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] : Prop :=
  (kappa q.atX.r lX jX).app (f.left.obj (g.right.obj K)) ≫ gamma q ag ah K =
    s.exchange.app K ≫ h.right.map ((kappa q.atY.r lY jY).app (e.left.obj K))

/-- Naturality of the displayed derived-limit exchange in the input complex.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def IsNaturalGamma {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh) : Prop :=
  ∀ (K K' : T.mateDerived) [IsIso (firstProjection q ag K)]
    [IsIso (firstProjection q ag K')] (a : K ⟶ K'),
    (completion q.atX.r lX).map (f.left.map (g.right.map a)) ≫ gamma q ag ah K' =
      gamma q ag ah K ≫ h.right.map ((completion q.atY.r lY).map (e.left.map a))

/-- All strict exchange, evaluation, quotient and coaugmentation conclusions.
This is the conjunction of the displayed named equations, with no further data.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def FullEquation {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (jX : ConstantLimit X lX) (jY : ConstantLimit Y lY) : Prop :=
    ProjectionIsomorphisms q ag ah ∧
    (∀ (K : T.mateDerived) [IsIso (firstProjection q ag K)],
      IsTowerMate q ag ah K ∧ IsEvaluatedMate q ag ah K ∧ QuotientEquation q ag ah K ∧
        HasCoaugmentationEquation q ag ah jX jY K) ∧
    IsNaturalGamma q ag ah

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] DerivedCategory.Q HomologicalComplex₂.total
  HomologicalComplex.mapBifunctorMap CochainComplex.kInjectiveResolutionFunctor
  CochainComplex.toKInjectiveResolution
attribute [local irreducible] total evComparison exactLeft firstProjection
  secondProjection conjugate limitComparison gamma evaluatedSource evaluatedTarget
  forgetQuotient RingedTensorSquare.exchange RingedTensorSquare.derivedComparison

private theorem projection_is_mate {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) [e.pushforward.Additive]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers]
    [HasCountableProducts A.mateDerived] [HasCountableProducts B.mateDerived]
    {QA : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ}
    {QB : ℕᵒᵖ ⥤ CochainComplex B.mateModules ℤ}
    {zA : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ QA}
    {zB : (Functor.const ℕᵒᵖ).obj B.mateUnitComplex ⟶ QB}
    {rA : Reduction A QA zA} {rB : Reduction B QB zB}
    {lA : StrictProjectionLimit A} {lB : StrictProjectionLimit B}
    {d : StrictProjectionDirectImage e lB lA}
    (a : TowerAdjunction e d) (p : PullReduction e rA rB) (E : B.mateDerived) :
    (mateEquiv e.derivedAdjunction a.adjunction
      (TwoSquare.mk rA.functor e.left (towerLeft e) rB.functor p.pull.hom)).app E =
        projection e a p E := by
  apply (a.adjunction.homEquiv _ _).symm.injective
  change (towerLeft e).map (_) ≫ a.adjunction.counit.app _ = _
  rw [mateEquiv_counit]
  exact ((a.adjunction.homEquiv _ _).symm_apply_apply _).symm

private theorem tower_mate {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s)
    (hf : IsIso f.ringMap) (hg : IsIso g.ringMap)
    (hh : IsIso h.ringMap) (he : IsIso e.ringMap)
    (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] :
    IsTowerMate q ag ah K := by
  have hcub := exchangeMate_cube_all_normalized
    g.derivedAdjunction h.derivedAdjunction ag.adjunction ah.adjunction
    q.atS.r.functor q.atT.r.functor q.atX.r.functor q.atY.r.functor
    q.pg.pull.symm q.pf.pull.symm q.pe.pull.symm q.ph.pull.symm
    s.derivedComparison.hom (towerSquare f g h e s).hom
    (strictReductionPullbackSquare s q hf hg hh he) K
    (projection g ag q.pg K) (projection h ah q.ph (e.left.obj K))
    (s.exchange.app K) ((towerMate f g h e s ag ah).app (input q K))
    (by unfold RingedTensorSquare.exchange; rfl) (by rfl)
    (projection_is_mate g ag q.pg K)
    (projection_is_mate h ah q.ph (e.left.obj K))
  have hcomm : q.atX.r.functor.map (s.exchange.app K) ≫ secondProjection q ah K =
      firstProjection q ag K ≫ (towerMate f g h e s ag ah).app (input q K) := by
    simpa only [firstProjection, secondProjection,
      Iso.symm_hom, Category.assoc] using hcub
  apply (cancel_epi (firstProjection q ag K)).1
  simpa only [IsTowerMate, conjugate, ← Category.assoc, IsIso.hom_inv_id,
    Category.id_comp] using hcomm

private theorem mate_of_counit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {F : A ⥤ B} {R : B ⥤ A} {F' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : F ⊣ R) (adj' : F' ⊣ R')
    (a : A ⥤ A') (b : B ⥤ B') (p : F ⋙ b ≅ a ⋙ F')
    (r : R ⋙ a ⟶ b ⋙ R')
    (hr : ∀ E : B, b.map (adj.counit.app E) =
      p.hom.app (R.obj E) ≫ F'.map (r.app E) ≫ adj'.counit.app (b.obj E))
    (E : B) :
    (mateEquiv adj adj' (TwoSquare.mk a F F' b p.inv)).app E = r.app E := by
  apply (adj'.homEquiv _ _).symm.injective
  change F'.map (_) ≫ adj'.counit.app _ = _
  rw [mateEquiv_counit, hr]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem inverse_square
    {C : Type*} [Category C] {A0 A1 A2 B0 B1 B2 : C}
    (i : A0 ≅ A1) (j : A1 ≅ A2) (k : B0 ≅ B1) (l : B1 ≅ B2)
    (x : A0 ⟶ B0) (y : A2 ⟶ B2)
    (h : x ≫ k.hom ≫ l.hom = i.hom ≫ j.hom ≫ y) :
    j.inv ≫ i.inv ≫ x = y ≫ l.inv ≫ k.inv := by
  apply (cancel_mono (k.hom ≫ l.hom)).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

omit [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
  [PreservesFiniteLimits g.pullback] [PreservesFiniteColimits g.pullback]
  [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
  [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
  [HasDerivedCategory S.projectionTowers] [HasDerivedCategory T.projectionTowers]
  [HasDerivedCategory X.projectionTowers] [HasDerivedCategory Y.projectionTowers]
  [g.pushforward.Additive] [h.pushforward.Additive]
  [HasCountableProducts S.mateDerived] [HasCountableProducts T.mateDerived]
  [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived] in
private theorem quotient_mate
    {s : RingedTensorSquare S T X Y g f e h}
    {QS : CochainComplex S.mateModules ℤ} {QT : CochainComplex T.mateModules ℤ}
    {QX : CochainComplex X.mateModules ℤ} {QY : CochainComplex Y.mateModules ℤ}
    (aS : QuotientAt S QS) (aT : QuotientAt T QT)
    (aX : QuotientAt X QX) (aY : QuotientAt Y QY)
    (fq : RingedTensorEdge (quotientCorner aS) (quotientCorner aX))
    (gq : RingedTensorEdge (quotientCorner aS) (quotientCorner aT))
    (hq : RingedTensorEdge (quotientCorner aX) (quotientCorner aY))
    (eq : RingedTensorEdge (quotientCorner aT) (quotientCorner aY))
    (sq : RingedTensorSquare _ _ _ _ gq fq eq hq)
    (c : QuotientComparisons (s := s) aS aT aX aY fq gq hq eq sq)
    (J : (quotientCorner aT).mateDerived) :
    (forgetQuotient aX).map (sq.exchange.app J) ≫
        c.rh.hom.app (eq.left.obj J) ≫ h.right.map (c.le.hom.app J) =
      c.lf.hom.app (gq.right.obj J) ≫ f.left.map (c.rg.hom.app J) ≫
        s.exchange.app ((forgetQuotient aT).obj J) := by
  have hc (M : (quotientCorner aS).mateDerived) :
      h.left.map (c.lf.inv.app M) ≫ c.lh.inv.app (fq.left.obj M) ≫
        (forgetQuotient aY).map (sq.derivedComparison.hom.app M) =
      s.derivedComparison.hom.app ((forgetQuotient aS).obj M) ≫
        e.left.map (c.lg.inv.app M) ≫ c.le.inv.app (gq.left.obj M) := by
    exact inverse_square (C := Y.mateDerived)
      (c.lh.app (fq.left.obj M)) (h.left.mapIso (c.lf.app M))
      (c.le.app (gq.left.obj M)) (e.left.mapIso (c.lg.app M))
      ((forgetQuotient aY).map (sq.derivedComparison.hom.app M))
      (s.derivedComparison.hom.app ((forgetQuotient aS).obj M)) (c.square M)
  have hg := mate_of_counit gq.derivedAdjunction g.derivedAdjunction
    (forgetQuotient aS) (forgetQuotient aT) c.lg c.rg.hom c.counit_g J
  have hh := mate_of_counit hq.derivedAdjunction h.derivedAdjunction
    (forgetQuotient aX) (forgetQuotient aY) c.lh c.rh.hom c.counit_h (eq.left.obj J)
  have hcub := exchangeMate_cube_all_normalized gq.derivedAdjunction hq.derivedAdjunction
    g.derivedAdjunction h.derivedAdjunction
    (forgetQuotient aS) (forgetQuotient aT) (forgetQuotient aX) (forgetQuotient aY)
    c.lg c.lf c.le c.lh sq.derivedComparison.hom s.derivedComparison.hom hc J
    (c.rg.hom.app J) (c.rh.hom.app (eq.left.obj J))
    (sq.exchange.app J) (s.exchange.app ((forgetQuotient aT).obj J))
    (by unfold RingedTensorSquare.exchange; rfl)
    (by unfold RingedTensorSquare.exchange; rfl) hg hh
  exact hcub

private theorem quotient_diagram
    {C : Type*} [Category C]
    {A0 A1 A2 A3 B0 B1 B2 B3 U V : C}
    (a1 : A0 ⟶ B0) (a2 : B0 ⟶ B1) (a3 : B1 ⟶ B2)
    (l1 : A0 ⟶ A1) (l2 : A1 ⟶ A2) (b0 : A2 ⟶ B2)
    (iS : A2 ⟶ A3) (iT : B2 ⟶ B3) (b1 : A3 ⟶ B3)
    (source : U ≅ A3) (target : V ≅ B3) (v : U ⟶ V)
    (hm : a1 ≫ a2 ≫ a3 = l1 ≫ l2 ≫ b0)
    (hn : iS ≫ b1 = b0 ≫ iT)
    (he : v ≫ target.hom = source.hom ≫ b1) :
    a1 ≫ a2 ≫ a3 ≫ iT ≫ target.inv =
      l1 ≫ l2 ≫ iS ≫ source.inv ≫ v := by
  apply (cancel_mono target.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he]
  simp only [Iso.inv_hom_id_assoc]
  rw [reassoc_of% hm, ← hn]

private theorem quotient_of_evaluated {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)]
    (heval : IsEvaluatedMate q ag ah K) : QuotientEquation q ag ah K := by
  intro n aS aT aX aY fq gq hq eq sq c J i
  apply quotient_diagram (C := X.mateDerived)
    (A0 := (forgetQuotient aX).obj (fq.left.obj (gq.right.obj J)))
    (A1 := f.left.obj ((forgetQuotient aS).obj (gq.right.obj J)))
    (A2 := f.left.obj (g.right.obj ((forgetQuotient aT).obj J)))
    (A3 := f.left.obj (g.right.obj ((ev T lT n).obj (input q K))))
    (B0 := (forgetQuotient aX).obj (hq.right.obj (eq.left.obj J)))
    (B1 := h.right.obj ((forgetQuotient aY).obj (eq.left.obj J)))
    (B2 := h.right.obj (e.left.obj ((forgetQuotient aT).obj J)))
    (B3 := h.right.obj (e.left.obj ((ev T lT n).obj (input q K))))
    (U := (ev X lX n).obj (upper q dg K))
    (V := (ev X lX n).obj (lower q dh K))
    ((forgetQuotient aX).map (sq.exchange.app J))
    (c.rh.hom.app (eq.left.obj J)) (h.right.map (c.le.hom.app J))
    (c.lf.hom.app (gq.right.obj J)) (f.left.map (c.rg.hom.app J))
    (s.exchange.app ((forgetQuotient aT).obj J))
    (f.left.map (g.right.map i.hom)) (h.right.map (e.left.map i.hom))
    (s.exchange.app ((ev T lT n).obj (input q K)))
    (evaluatedSource q dg K n) (evaluatedTarget q dh K n)
    ((ev X lX n).map (conjugate q ag ah K))
  · exact quotient_mate aS aT aX aY fq gq hq eq sq c J
  · exact s.exchange.naturality i.hom
  · exact heval n

private theorem cancel_limit_conjugate
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {A B N E F : C} {Z : D}
    (H : A ⟶ B) [IsIso H] (b : A ⟶ N) (P : N ⟶ E)
    (t : E ≅ F) (c : Z ≅ L.obj E) :
    L.map H ≫ L.map (inv H ≫ b ≫ P ≫ t.hom) ≫
        (c ≪≫ L.mapIso t).inv = L.map b ≫ L.map P ≫ c.inv := by
  simp only [Functor.map_comp, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  rw [← L.map_comp_assoc, IsIso.hom_inv_id, L.map_id, Category.id_comp]
  simp only [← L.map_comp_assoc, Iso.hom_inv_id, L.map_id, Category.id_comp]

private theorem gamma_eq {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] :
    gamma q ag ah K =
      (completion q.atX.r lX).map (s.exchange.app K) ≫
        lX.L.map (projection h ah q.ph (e.left.obj K)) ≫
          (dh.a.inv.app (q.atY.r.functor.obj (e.left.obj K))) := by
  unfold gamma conjugate secondProjection limitComparison completion
  exact cancel_limit_conjugate lX.L (firstProjection q ag K)
    (q.atX.r.functor.map (s.exchange.app K))
    (projection h ah q.ph (e.left.obj K))
    (dh.Rt.mapIso (q.pe.pull.symm.app K))
    (dh.a.app (q.atY.r.functor.obj (e.left.obj K)))

private theorem projection_natural {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) [e.pushforward.Additive]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers]
    [HasCountableProducts A.mateDerived] [HasCountableProducts B.mateDerived]
    {QA : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ}
    {QB : ℕᵒᵖ ⥤ CochainComplex B.mateModules ℤ}
    {zA : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ QA}
    {zB : (Functor.const ℕᵒᵖ).obj B.mateUnitComplex ⟶ QB}
    {rA : Reduction A QA zA} {rB : Reduction B QB zB}
    {lA : StrictProjectionLimit A} {lB : StrictProjectionLimit B}
    {d : StrictProjectionDirectImage e lB lA}
    (a : TowerAdjunction e d) (p : PullReduction e rA rB)
    {E E' : B.mateDerived} (v : E ⟶ E') :
    rA.functor.map (e.right.map v) ≫ projection e a p E' =
      projection e a p E ≫ d.Rt.map (rB.functor.map v) := by
  apply a.adjunction.homEquiv_naturality_left_square
  have hn := p.pull.hom.naturality (e.right.map v)
  dsimp only [Functor.comp_map] at hn
  change (towerLeft e).map (rA.functor.map (e.right.map v)) ≫
      p.pull.hom.app (e.right.obj E') ≫ _ = _
  have hc := e.derivedAdjunction.counit.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [← Category.assoc, hn, Category.assoc, ← rB.functor.map_comp,
    hc, rB.functor.map_comp, Category.assoc]

set_option maxHeartbeats 800000 in
-- The naturality statement compares the two associated composites of six derived functors.
private theorem naturalGamma {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh) :
    IsNaturalGamma q ag ah := by
  let p : h.right ⋙ q.atX.r.functor ⟶ q.atY.r.functor ⋙ dh.Rt :=
    { app := projection h ah q.ph
      naturality := fun _ _ v ↦ projection_natural h ah q.ph v }
  let v : (g.right ⋙ f.left) ⋙ completion q.atX.r lX ⟶
      e.left ⋙ completion q.atY.r lY ⋙ h.right :=
    Functor.whiskerRight s.exchange (completion q.atX.r lX) ≫
      Functor.whiskerLeft e.left (Functor.whiskerRight p lX.L) ≫
      Functor.whiskerLeft (e.left ⋙ q.atY.r.functor) dh.a.inv
  intro K K' _ _ a
  rw [gamma_eq q ag ah K, gamma_eq q ag ah K']
  exact v.naturality a

private theorem coaugmentation_diagram
    {C : Type*} [Category C] {A B N E F G : C}
    (k : A ⟶ B) (b : A ⟶ N) (i : N ⟶ E) (rb : B ⟶ E)
    (p : E ⟶ F) (c : G ≅ F) (j : N ⟶ G)
    (hn : k ≫ rb = b ≫ i) (hp : i ≫ p = j ≫ c.hom) :
    k ≫ (rb ≫ p ≫ c.inv) = b ≫ j := by
  rw [← Category.assoc k rb, hn, Category.assoc, ← Category.assoc i p, hp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Strict perfect-coefficient exchange, its evaluated and quotient-ring mates, and
its coaugmentation equation after total derived inverse limit.
Source: Stacks Project, sites-cohomology.tex, Tags 0E48 and 0944; strict augmented
perfect-diagram/coaugmentation refinement, agent supplied
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation).Proof:
1. Use the small diagram-site realization and normalized evaluation comparisons
(lem-weil-pbc-diagram-site-realization, lem-weil-pbc-tower-derived-evaluation-normalization).
The constant-direct-image comparison is fixed by the ordinary counit, so the
constant-tower mate is Delta of the ambient mate
(lem-weil-pbc-constant-tower-pushforward-normalization).
2. Evaluate H and H'. Each evaluation is the perfect-coefficient projection map
of lem-sbc-ringed-site-perfect-projection-formula (Stacks 0944). Pullback preserves
local perfectness by lem-weil-pbc-strict-perfect-ringed-pullback-model and a covering
argument. Cones are acyclic levelwise by lem-weil-tower-category-levelwise-abelian;
therefore H and H' are isomorphisms of derived strict towers.
3. Apply lem-weil-pbc-ringed-exchange-tensor-coherence on the diagram topoi to
Delta K and the coefficient diagram. It gives beta H = H' R(b). Cancel H.
This proves equality of whole-tower morphisms without using evaluations to detect equality.
4. Evaluate the actual mate, using the counit-preserving comparisons. Its transpose
is the ambient square comparison followed by the ambient counit. For quotient
coefficients, apply lem-pur-diagram-ring-restriction-pushforward and
lem-sfb-ringed-comparison-tensor-adjunction. The composite-counit and ring-square
normalizations identify the restricted quotient mate with this evaluated mate.
5. Naturality of the projection map in coefficients, and its identity value at the
unit (lem-weil-pbc-ringed-projection-mate-exact), give H' i_X = R_h(i_Y) chi_h
as an equation before taking limits, for the actual strict augmentation.
6. Naturality of the canonical direct-image/limit comparison, normalized on constant
towers, gives c inverse Rlim(H') kappa_X = R_h(kappa_Y)
(lem-weil-ringed-tower-pushforward-limit-comparison,
lem-weil-pbc-constant-tower-pushforward-normalization,
lem-weil-pbc-ringed-strict-tower-homotopy-limit).
7. Naturality of the augmentation gives C_X(b) kappa_M = kappa_N b. Substitute
v H = H' R_X(b) into c inverse Rlim(v) Rlim(H) kappa_M. The result is
R_h(kappa_Y) b. Naturality in K follows from naturality of every construction.
No completeness, reflector, cartesianness, or geometric-finiteness hypothesis enters. -/
theorem strictQuotientExchangeUnitEquation
    (s : RingedTensorSquare S T X Y g f e h)
    (q : Coefficients f g h e s)
    (hperfect : HasPerfectLevels S q.atS.Q)
    (hf : IsIso f.ringMap) (hg : IsIso g.ringMap)
    (hh : IsIso h.ringMap) (he : IsIso e.ringMap)
    (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (jX : ConstantLimit X lX) (jY : ConstantLimit Y lY) :
    FullEquation q ag ah jX jY := by
  let : f.pushforward.Additive := f.moduleAdjunction.right_adjoint_additive
  let : HasSheafify S.topology AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : ∀ U : S.site, HasSheafify (S.topology.over U) AddCommGrpCat.{u} :=
    fun _ ↦ GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : ∀ U : S.site, (S.topology.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  let : S.topology.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let : HasSheafify T.topology AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : ∀ U : T.site, HasSheafify (T.topology.over U) AddCommGrpCat.{u} :=
    fun _ ↦ GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : ∀ U : T.site, (T.topology.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  let : T.topology.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let : HasSheafify X.topology AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : ∀ U : X.site, HasSheafify (X.topology.over U) AddCommGrpCat.{u} :=
    fun _ ↦ GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : ∀ U : X.site, (X.topology.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  let : X.topology.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let : HasSheafify Y.topology AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : ∀ U : Y.site, HasSheafify (Y.topology.over U) AddCommGrpCat.{u} :=
    fun _ ↦ GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : ∀ U : Y.site, (Y.topology.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  let : Y.topology.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have hpX := (strictPerfectTowerProjection f hf q.pf hperfect).1
  have hgproj := (strictPerfectTowerProjection g hg q.pg hperfect).2 lS lT dg ag
  have hhproj := (strictPerfectTowerProjection h hh q.ph hpX).2 lX lY dh ah
  have hi : ProjectionIsomorphisms q ag ah := by
    intro K
    let := hgproj K
    let := hhproj (e.left.obj K)
    constructor
    · unfold firstProjection
      infer_instance
    · unfold secondProjection
      infer_instance
  refine ⟨hi, ?_, naturalGamma q ag ah⟩
  intro K _
  have ht := tower_mate q hf hg hh he ag ah K
  have hev : IsEvaluatedMate q ag ah K := by
    unfold IsEvaluatedMate
    rw [show conjugate q ag ah K = _ from ht]
    exact strictTowerMateEvaluation s q ag ah K
  refine ⟨ht, hev, quotient_of_evaluated q ag ah K hev, ?_⟩
  change (kappa q.atX.r lX jX).app _ ≫ gamma q ag ah K = _
  rw [gamma_eq]
  have hn := (kappa q.atX.r lX jX).naturality (s.exchange.app K)
  dsimp only [Functor.id_map] at hn
  exact coaugmentation_diagram
    ((kappa q.atX.r lX jX).app (f.left.obj (g.right.obj K)))
    (s.exchange.app K) ((kappa q.atX.r lX jX).app (h.right.obj (e.left.obj K)))
    ((completion q.atX.r lX).map (s.exchange.app K))
    (lX.L.map (projection h ah q.ph (e.left.obj K)))
    (dh.a.app (q.atY.r.functor.obj (e.left.obj K)))
    (h.right.map ((kappa q.atY.r lY jY).app (e.left.obj K)))
    hn.symm (strictProjectionCoaugmentation h hh ah q.ph jX jY (e.left.obj K))

end SheafOfModules.StrictQuotientExchange
