/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionEvaluationFactors
import all WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionFormulaCoherence
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionRealization

/-! # Finite evaluation of the proper/open system projection

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open IntegralSystemRealization

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (d : SixFunctorOperationDatum D C E n hn) (m : ℕ)

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor

namespace SystemEvaluationProof
open WeilConjectures.SystemProjectionFormula
open CategoryTheory.Limits
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] properProjection finiteProperProjection finiteOpenTensorInv
  pullbackTensorDerivedEvaluation pullbackTensorSystemComparison
  canonicalFinitePullbackTensor CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint
set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem system_projection_evaluation
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (z : Realizations l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : X ⟶ Spec (.of D.k)) (tY : Y ⟶ Spec (.of D.k))
    (cf : Compactification f) (n : ℕ)
    (M : System l E X) (N : System l E Y)
    :
    (coefficientSequenceDerivedEvaluation l E Y n).map
        (projection l E o z.compositors z.openComparisons cf M N) ≫
      (evaluateSupport l E o cf n).hom.app
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N)) ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) cf).map
        (((calculus l E X).evaluationTensor n).hom.app (M, (pull l E f).obj N) ≫
          (finiteIntrinsicDerivedTensor l E X n).map
            (Prod.mkHom (𝟙 _) ((pullbackTensorDerivedEvaluation l E f n).hom.app N))) =
    ((calculus l E Y).evaluationTensor n).hom.app ((support l E o cf).obj M, N) ≫
      (finiteIntrinsicDerivedTensor l E Y n).map
        (Prod.mkHom ((evaluateSupport l E o cf n).hom.app M) (𝟙 _)) ≫
      finiteProjection l E D hl cf tX tY n
        ((coefficientSequenceDerivedEvaluation l E X n).obj M)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  -- Use one expression for the factored morphism before comparing its pullback functors.
  rcases cf with ⟨W, pg, oi, h, hp, hi⟩
  subst f
  let := hp
  let := hi
  let cf : Compactification (oi ≫ pg) := ⟨W, pg, oi, rfl, hp, hi⟩
  let := residueInvertible l D hl X tX
  let := residueInvertible l D hl Y tY
  let := residueInvertible l D hl cf.Z (cf.g ≫ tY)
  let EX := coefficientSequenceDerivedEvaluation l E X n
  let EY := coefficientSequenceDerivedEvaluation l E Y n
  let EZ := coefficientSequenceDerivedEvaluation l E cf.Z n
  let TX := (calculus l E X).systemClosed.tensor
  let tx : normalizedDVRDerived l E X n × normalizedDVRDerived l E X n ⥤
      normalizedDVRDerived l E X n := finiteIntrinsicDerivedTensor l E X n
  let Pi : normalizedDVRDerived l E cf.Z n ⥤ normalizedDVRDerived l E X n :=
    finiteDerivedPullback l E n cf.i
  let J : normalizedDVRDerived l E X n ⥤ normalizedDVRDerived l E cf.Z n :=
    (sfIntrinsicExtensionByZero cf.i
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
  let R : normalizedDVRDerived l E cf.Z n ⥤ normalizedDVRDerived l E Y n :=
    proEtaleConstantDerivedDirectImage cf.g (Padic.coefficientExtensionRing l E (n + 1))
  let ex : TX ⋙ EX ≅ (EX.prod EX) ⋙ tx := (calculus l E X).evaluationTensor n
  let epg := pullbackTensorDerivedEvaluation l E cf.g n
  let epi : pull l E cf.i ⋙ EX ≅ EZ ⋙ Pi :=
    pullbackTensorDerivedEvaluation l E cf.i n
  let epf := pullbackTensorDerivedEvaluation l E (oi ≫ pg) n
  let w := (z.compositors.pullComp cf.i cf.g).inv.app N ≫
    eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj N) cf.comm.symm)
  let v := TX.map (Prod.mkHom (𝟙 M) w)
  let q := ((finitePullComp l E cf.i cf.g n).symm ≪≫
    eqToIso (congrArg (finiteDerivedPullback l E n) cf.comm.symm)).hom.app (EY.obj N)
  have hcomp : EX.map w ≫ epf.hom.app N =
      epi.hom.app ((pull l E cf.g).obj N) ≫ Pi.map (epg.hom.app N) ≫ q := by
    exact paste_compositor_cast EX
      ((z.compositors.pullComp cf.i cf.g).inv.app N)
      (eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj N) cf.comm.symm))
      (epf.hom.app N) ((pullbackTensorDerivedEvaluation l E (cf.i ≫ cf.g) n).hom.app N)
      (epi.hom.app ((pull l E cf.g).obj N)) (Pi.map (epg.hom.app N))
      ((sfIntrinsicDerivedPullbackComp (Padic.coefficientExtensionRing l E (n + 1))
        cf.i cf.g).inv.app (EY.obj N))
      ((eqToIso (congrArg (finiteDerivedPullback l E n) cf.comm.symm)).hom.app (EY.obj N))
      q (pullback_evaluation_congr l E cf.comm.symm n N)
      (systemPullbackCompositorEvaluation l E o z.compositors cf.i cf.g n N) (by rfl)
  have htransport := tensor_right_transport EX TX tx ex M w (epf.hom.app N)
    (epi.hom.app ((pull l E cf.g).obj N) ≫ Pi.map (epg.hom.app N)) q
    (hcomp.trans (Category.assoc _ _ _).symm)
  have hproper := proper_projection_evaluation l E D hl o cf.g
    (cf.g ≫ tY) tY n
    ((Operations.shriek l E o cf.i).obj M) N (J.obj (EX.obj M))
    (((o.openEvaluation cf.i).evaluation n).app M)
  have hopen := open_projection_evaluation l E D hl o z.compositors z.openComparisons cf.i
    tX (cf.g ≫ tY) n
    M ((pull l E cf.g).obj N) ((finiteDerivedPullback l E n cf.g).obj (EY.obj N))
    (epg.app N)
  let Js := Operations.shriek l E o cf.i
  let Rs := Operations.push l E o cf.g
  let pp : (calculus l E Y).systemClosed.tensor.obj (Rs.obj (Js.obj M), N) ⟶
      Rs.obj ((calculus l E cf.Z).systemClosed.tensor.obj
        (Js.obj M, (pull l E cf.g).obj N)) :=
    ((properProjection l E o cf.g).app (Js.obj M)).app N
  let dd : (calculus l E cf.Z).systemClosed.tensor.obj
      (Js.obj M, (pull l E cf.g).obj N) ⟶
      Js.obj (TX.obj (M, (pull l E cf.i).obj ((pull l E cf.g).obj N))) :=
    (z.openComparisons.projection cf.i).hom.app (M, (pull l E cf.g).obj N)
  have hpaste := paste_support_word EX EZ EY Js Rs J R
    ((o.openEvaluation cf.i).evaluation n) ((o.evaluation cf.g).evaluation n)
    pp dd v
    (ex.hom.app (M, (pull l E (oi ≫ pg)).obj N) ≫
      tx.map (Prod.mkHom (𝟙 _) (epf.hom.app N)))
    (ex.hom.app (M, (pull l E cf.i).obj ((pull l E cf.g).obj N)) ≫
      tx.map (Prod.mkHom (𝟙 _)
        (epi.hom.app ((pull l E cf.g).obj N) ≫ Pi.map (epg.hom.app N))))
    (tx.map (Prod.mkHom (𝟙 _) q))
    _ _ _ _ _ hproper (hopen.trans (Category.assoc _ _ _).symm)
    htransport
  simp only [evaluateSupport_hom_app]
  dsimp only [projection, compactificationProjection, finiteProjection,
    sfAmbientCompactSupportCandidate, Functor.comp_map]
  exact hpaste

private theorem tensor_input_transport
    {A : Type*} [Category A] (t T : A × A ⥤ A) (e : t ≅ T)
    {W M N N' P Q : A} (a : W ⟶ t.obj (M, N))
    (k : M ⟶ P) (v : N ⟶ N') (w : N' ⟶ Q) :
    a ≫ e.hom.app (M, N) ≫ T.map (Prod.mkHom k (v ≫ w)) =
      a ≫ t.map (Prod.mkHom (𝟙 M) v) ≫ e.hom.app (M, N') ≫
        T.map (Prod.mkHom k w) := by
  have h := e.hom.naturality (Prod.mkHom (𝟙 M) v)
  rw [reassoc_of% h]
  simp only [← T.map_comp, prod_comp, Prod.mkHom, Category.id_comp]

private theorem paste_evaluated_projection
    {A B : Type*} [Category A] [Category B] (H : A ⥤ B)
    {A₀ A₁ A₂ : A} {P Q R B₀ B₁ B₂ B₃ B₄ : B}
    {p : P ⟶ Q} {s : Q ⟶ H.obj A₀} {a : A₀ ⟶ A₁} {h : A₁ ⟶ A₂}
    {q : H.obj A₂ ⟶ R} {x : P ⟶ B₀} {t : B₀ ⟶ B₁} {b : B₁ ⟶ H.obj A₁}
    {e : B₁ ⟶ B₂} {z : B₂ ⟶ B₃} {c : B₃ ⟶ R}
    {e₀ : B₀ ⟶ B₄} {t₀ : B₄ ⟶ B₂}
    (hv : p ≫ s ≫ H.map a = x ≫ t ≫ b)
    (hf : b ≫ H.map h ≫ q = e ≫ z ≫ c) (hy : t ≫ e = e₀ ≫ t₀) :
    p ≫ s ≫ H.map (a ≫ h) ≫ q = x ≫ e₀ ≫ t₀ ≫ z ≫ c := by
  simp only [H.map_comp, Category.assoc]
  rw [reassoc_of% hv, hf, reassoc_of% hy]

private theorem finish_evaluation
    {A B : Type*} [Category A] [Category B] (H : A ⥤ B) (T : B × B ⥤ B)
    {A₀ A₁ A₂ A₃ A₄ : A} {P Q R W M M' M'' M''' N N' : B}
    {p : P ⟶ Q} {s : Q ⟶ H.obj A₀} {q : H.obj A₄ ⟶ R}
    {a₁ : A₀ ⟶ A₁} {a₂ : A₁ ⟶ A₂} {a₃ : A₂ ⟶ A₃} {a₄ : A₃ ⟶ A₄}
    {input : A₀ ⟶ A₄} {x : P ⟶ W} {e : W ⟶ T.obj (M, N)}
    {v : M ⟶ M'} {y₁ : M' ⟶ M''} {y₂ : M'' ⟶ M'''} {z : N ⟶ N'}
    {c : T.obj (M''', N') ⟶ R}
    (hin : input = a₁ ≫ a₂ ≫ a₃ ≫ a₄)
    (hp : p ≫ s ≫ H.map ((a₁ ≫ a₂) ≫ a₃ ≫ a₄) ≫ q =
      x ≫ e ≫ T.map (Prod.mkHom v (𝟙 N)) ≫ T.map (Prod.mkHom (y₁ ≫ y₂) z) ≫ c) :
    p ≫ s ≫ H.map input ≫ q =
      ((x ≫ e) ≫ T.map (Prod.mkHom (v ≫ y₁ ≫ y₂) z)) ≫ c := by
  rw [hin]
  simpa only [Category.assoc, ← T.map_comp_assoc, ← T.map_comp, prod_comp,
    Prod.mkHom, Category.id_comp] using hp

end SystemEvaluationProof

attribute [local irreducible] CompactSupportFiniteProjection.tensor
  sfIntrinsicDerivedEquivalence compactificationProjection supportEvaluation
  SystemProjectionFormula.finiteProjection CompactSupportFiniteProjection.component

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- System projection evaluates to the finite projection in the explicit tensor,
support and pullback coordinates. No integral tensor, support adjunct, sourceMap or
targetMap occurs here: this concerns the proper/open system expression alone.

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions;
Stacks 07A4, 07A6 and 0E48, proper counit and open tensor factors.
(blueprint: lem-sf-integral-projection-system-evaluation).

Proof: compose the calculus's evaluationTensor with the canonical comparison of the
intrinsic finite tensor and the fixed-coefficient tensor transported through
sixFunctorFiniteRealization. Construct the latter on simultaneous K-flat models:
the ordinary constant-ring realization preserves balanced tensors, and its total
complex comparison descends through the K-flat localization. This defines the natural
family b on all system inputs. Expand compactificationProjection into the proper
projection mate, open projection and inverse pullback compositor. DirectEvaluation's
unit and counit equations carry the proper mate to the finite proper mate. The open
projection is the mate of the ordinary extension-by-zero tensor map; OpenEvaluation's
transpose equation carries it to the finite open map. The prescribed section formula
of Compositors carries the remaining pullback compositor to its finite counterpart.
Paste the proper and open squares, cancelling adjacent inverse comparisons by
naturality. The definition of the finite component conjugates precisely this finite
proper/open word by the stage's finiteSupport and finitePullback realizations.
These are the same factors in evaluatedSource and evaluatedTarget, so this is the
displayed equation. The construction uses the actual quotient at every m, including
m=0; zero complexes, identity opens and empty opens obey the same universal formulas. -/
theorem integralProjectionSystemEvaluation
    (o : Operations C.l E) (z : Realizations C.l E D o) :
    ∃ b : SystemTensorEvaluation (C := C) (E := E) m,
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (evaluation (C := C) (E := E) m Y).map
            (compactificationProjection C.l E o z.compositors z.openComparisons c
              ((calculus C.l E X.obj.left).reduction.obj K.obj)
              ((calculus C.l E Y.obj.left).reduction.obj L.obj)) ≫
          (evaluatedTarget d m b o f c K L).hom =
        (evaluatedSource d m b o f c K L).hom ≫
          (finiteInclusion (C := C) (E := E) m Y).map
            (CompactSupportFiniteProjection.component (stage d m) f c
              ((reduction d m X).obj K) ((torReduction d m Y).obj L)) := by
  obtain ⟨e, he⟩ := finiteIntrinsicProjectionRealization m (stage d m)
  let b : SystemTensorEvaluation (C := C) (E := E) m := fun X ↦
    (calculus C.l E X.obj.left).evaluationTensor m ≪≫
      Functor.isoWhiskerLeft
        ((evaluation (C := C) (E := E) m X).prod
          (evaluation (C := C) (E := E) m X)) (e X)
  refine ⟨b, ?_⟩
  intro X Y f c K L
  let M := (calculus C.l E X.obj.left).reduction.obj K.obj
  let N := (calculus C.l E Y.obj.left).reduction.obj L.obj
  let EX := evaluation (C := C) (E := E) m X
  let EY := evaluation (C := C) (E := E) m Y
  let H := sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c
  let PX := finiteDerivedPullback C.l E m f.hom.left
  let tx := finiteIntrinsicDerivedTensor C.l E X.obj.left m
  let ty := finiteIntrinsicDerivedTensor C.l E Y.obj.left m
  let TX := evaluatedTensor (C := C) (E := E) m X
  let TY := evaluatedTensor (C := C) (E := E) m Y
  let Q := (calculus C.l E X.obj.left).systemClosed.tensor.obj
    (M, (pull C.l E f.hom.left).obj N)
  let es := supportEvaluation C.l E o c m
  let ep := (pullbackTensorDerivedEvaluation C.l E f.hom.left m).hom.app N
  let k := (reductionEvaluation d m X K).hom
  let l := (reductionEvaluation d m Y L).hom
  let r := ((stage d m).finitePullback f).inv.app ((reduction d m Y).obj L)
  let q := ((stage d m).finiteSupport f c).inv.app
    (((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
      ((reduction d m X).obj K)).obj
        ((CompactSupportFiniteProjection.torPull (stage d m) f).obj
          ((torReduction d m Y).obj L)))
  have hv := SystemEvaluationProof.system_projection_evaluation C.l E D C.different
    o z f.hom.left X.obj.hom Y.obj.hom c m M N
  have hf := he f c ((reduction d m X).obj K) ((torReduction d m Y).obj L)
    (EX.obj M) (EY.obj N) (reductionEvaluation d m X K) (reductionEvaluation d m Y L)
  have hy := (e Y).hom.naturality
    (Prod.mkHom (es.hom.app M) (𝟙 (EY.obj N)))
  change ty.map (Prod.mkHom (es.hom.app M) (𝟙 _)) ≫ (e Y).hom.app _ =
    (e Y).hom.app _ ≫ TY.map (Prod.mkHom (es.hom.app M) (𝟙 _)) at hy
  have hinput :
      (b X).hom.app (M, (pull C.l E f.hom.left).obj N) ≫
        TX.map (Prod.mkHom k (ep ≫ PX.map l ≫ r)) =
      ((calculus C.l E X.obj.left).evaluationTensor m).hom.app
          (M, (pull C.l E f.hom.left).obj N) ≫
        tx.map (Prod.mkHom (𝟙 _) ep) ≫
        (e X).hom.app (EX.obj M, PX.obj (EY.obj N)) ≫
        TX.map (Prod.mkHom k (PX.map l ≫ r)) := by
    dsimp only [b, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.prod_obj]
    exact (Category.assoc _ _ _).trans
      (SystemEvaluationProof.tensor_input_transport tx TX (e X)
        (((calculus C.l E X.obj.left).evaluationTensor m).hom.app
          (M, (pull C.l E f.hom.left).obj N)) k ep (PX.map l ≫ r))
  have hp := SystemEvaluationProof.paste_evaluated_projection H hv hf hy
  dsimp +instances only [evaluatedTarget, evaluatedInput, evaluatedPull, evaluatedSource,
    evaluatedSupport, Iso.trans, Iso.symm, Iso.app, Functor.mapIso, Iso.prod]
  dsimp only [b, Iso.trans, Iso.app, Functor.isoWhiskerLeft, Functor.mapIso,
    Functor.whiskeringLeft, Functor.whiskerLeft, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.prod_obj]
  dsimp only [SystemProjectionFormula.projection, SystemProjectionFormula.evaluateSupport,
    SystemProjectionFormula.support, Functor.comp_obj] at hp
  exact SystemEvaluationProof.finish_evaluation H TY hinput hp

end WeilConjectures.IntegralProjectionReduction
