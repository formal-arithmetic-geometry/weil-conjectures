/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.Paper.WeilTensorProduct
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.CategoryTheory.BilinearCoefficientDescent
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.CategoryTheory.ScalarLocalization

/-! # Rational Weil descent of the completion-unit tensor comparison

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, penultimate sentence; the six-step conditional
rational/common-stage argument in the DAG
(blueprint: lem-wf-tensor-comparison-rational-weil-descent).

The records below organize hypotheses on the actual ordinary and completed tensors.
Their restrictions retain every ambient morphism. Raw extensions have the prescribed
pure-tensor action, including denominators. No integral invertibility of numerators occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.BilinearCoefficientDescent

attribute [local irreducible] wfPullbackCompletion
  proEtaleCanonicalTensorComparison ScalarLocalization.composition
  pbcCompletedScalarSections wfCompletionObj intrinsicCompletion intrinsicCompletionUnit

namespace WeilConjectures.WfTensorComparison

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (W₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated W₀.hom] [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The integral category in the node. Source: the conditional rational descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
abbrev Integral := PbcBoundedConstructibleComplete (D.geometricFiber W₀).left
  (pbcStageDatum.{u} c.l c.Qbar E)

/-- The raw rational category, without an idempotent envelope. Source: the descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
abbrev Rational := PbcRationalCategory (D.geometricFiber W₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Ordinary tensor on the ambient completed-coefficient derived category.
Source: the conditional descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
abbrev ambientOrdinary := wfOrdinaryDerivedTensor (D.geometricFiber W₀).left
  (pbcStageDatum.{u} c.l c.Qbar E)

/-- Completion with its actual Koszul fiber and actual unit. Source: the descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
abbrev completion := wfCompletion (D.geometricFiber W₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1
  (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)

/-- The ambient inclusion of complete objects. Source: the conditional descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
abbrev completeInclusion := ObjectProperty.ι
  (WfIsComplete (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
    (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E))

/-- The stipulated integral tensor closure hypotheses. Source: the conditional descent
argument (blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
structure Closure where
  ordinary : ∀ M N : Integral D c W₀ E,
    PbcIsBoundedConstructibleComplete (D.geometricFiber W₀).left
      (pbcStageDatum.{u} c.l c.Qbar E)
      ((ambientOrdinary D c W₀ E).obj (M.obj, N.obj))
  completed : ∀ M N : Integral D c W₀ E,
    PbcIsBoundedConstructibleComplete (D.geometricFiber W₀).left
      (pbcStageDatum.{u} c.l c.Qbar E)
      (((completion D c W₀ E).obj ((ambientOrdinary D c W₀ E).obj (M.obj, N.obj))).obj)

variable {D c W₀ E}

/-- Restriction of ordinary tensor, with unchanged ambient arrow action. Source: descent
argument (blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
def ordinary (d : Closure D c W₀ E) : Integral D c W₀ E × Integral D c W₀ E ⥤
    Integral D c W₀ E :=
  ObjectProperty.lift _
    (((ObjectProperty.ι _).prod (ObjectProperty.ι _)) ⋙ ambientOrdinary D c W₀ E)
    (fun MN ↦ d.ordinary MN.1 MN.2)

/-- Restriction of tensor followed by the published completion. Source: descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
def completed (d : Closure D c W₀ E) : Integral D c W₀ E × Integral D c W₀ E ⥤
    Integral D c W₀ E :=
  ObjectProperty.lift _
    (((ObjectProperty.ι _).prod (ObjectProperty.ι _)) ⋙ ambientOrdinary D c W₀ E ⋙
      completion D c W₀ E ⋙ completeInclusion D c W₀ E)
    (fun MN ↦ d.completed MN.1 MN.2)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Integral Frobenius is the dependency's coefficient transport. Source: descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
abbrev transport (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (W₀ : Over (Spec (CommRingCat.of D.k₀)))
    [IsSeparated W₀.hom] [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  pbcIsoIntegralPullback (D.geometricFrobenius W₀).hom
  (pbcStageDatum.{u} c.l c.Qbar E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- The prescribed ordinary tensor/pullback comparison, restricted fully faithfully.
Source: descent argument (blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
def ordinaryMu (d : Closure D c W₀ E) (M N : Integral D c W₀ E) :
    (transport D c W₀ E).obj ((ordinary d).obj (M, N)) ≅
      (ordinary d).obj ((transport D c W₀ E).obj M, (transport D c W₀ E).obj N) :=
  ObjectProperty.isoMk _
    ((proEtaleCanonicalTensorComparison (D.geometricFrobenius W₀).hom
      (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
      (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
      (asIso (completedCoefficientMap (D.geometricFrobenius W₀).hom
        (pbcStageDatum.{u} c.l c.Qbar E)))
      (wfTensorModel _ (pbcStageDatum.{u} c.l c.Qbar E))
      (wfTensorModel _ (pbcStageDatum.{u} c.l c.Qbar E))).app (M.obj, N.obj))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- The prescribed completed comparison: the published `wfIntegralTensorPullback`,
restricted to the constructible inputs. Source: descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
def completedMu (d : Closure D c W₀ E) (M N : Integral D c W₀ E) :
    (transport D c W₀ E).obj ((completed d).obj (M, N)) ≅
      (completed d).obj ((transport D c W₀ E).obj M, (transport D c W₀ E).obj N) :=
  ObjectProperty.isoMk _
    ((ObjectProperty.ι _).mapIso
      (wfIntegralTensorPullback (D.geometricFiber W₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (D.geometricFrobenius W₀)
        ((wfIntegralConstructibleInclusion _ (pbcStageDatum.{u} c.l c.Qbar E) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
          (wfUniformizer_generates D c E)).obj M)
        ((wfIntegralConstructibleInclusion _ (pbcStageDatum.{u} c.l c.Qbar E) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
          (wfUniformizer_generates D c E)).obj N)))

attribute [local irreducible] ordinaryMu completedMu

/-- Exactly the conditional integral hypotheses: actual unit, natural invertibility,
and its square with the prescribed comparisons. Source: descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
structure IntegralData where
  closure : Closure D c W₀ E
  chi : ordinary closure ≅ completed closure
  unit : ∀ M N : Integral D c W₀ E,
    (chi.hom.app (M, N)).hom =
      wfCompletionUnit (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) ((ambientOrdinary D c W₀ E).obj (M.obj, N.obj))
  compatible : ∀ M N : Integral D c W₀ E,
    (transport D c W₀ E).map (chi.hom.app (M, N)) ≫ (completedMu closure M N).hom =
      (ordinaryMu closure M N).hom ≫
        chi.hom.app ((transport D c W₀ E).obj M, (transport D c W₀ E).obj N)

/-- Prescribed raw extensions: unchanged objects and the all-scalars pure-tensor action.
Source: descent argument (blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
structure RationalData where
  integral : IntegralData (D := D) (c := c) (W₀ := W₀) (E := E)
  ordinary : Rational D c W₀ E × Rational D c W₀ E ⥤ Rational D c W₀ E
  completed : Rational D c W₀ E × Rational D c W₀ E ⥤ Rational D c W₀ E
  ordinary_raw : IsRawExtension (pbcStageUniformizer.{u} c.l c.Qbar E)
    (WfTensorComparison.ordinary integral.closure) ordinary
  completed_raw : IsRawExtension (pbcStageUniformizer.{u} c.l c.Qbar E)
    (WfTensorComparison.completed integral.closure) completed

/-- Localized unit components, transported only by the prescribed unchanged-object equations.
Source: descent argument (blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
def component (d : RationalData (D := D) (c := c) (W₀ := W₀) (E := E))
    (M N : Rational D c W₀ E) : d.ordinary.obj (M, N) ≅ d.completed.obj (M, N) :=
  eqToIso (d.ordinary_raw.2.1 (M, N)) ≪≫
    (pbcRationalization _ (pbcStageDatum.{u} c.l c.Qbar E)
      (pbcStageUniformizer.{u} c.l c.Qbar E)).mapIso (d.integral.chi.app (M.obj, N.obj)) ≪≫
        (eqToIso (d.completed_raw.2.1 (M, N))).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Rationalization of the prescribed integral pullback comparison, with the same objects.
Source: descent argument (blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
def rationalMu (U : Integral D c W₀ E × Integral D c W₀ E ⥤ Integral D c W₀ E)
    (V : Rational D c W₀ E × Rational D c W₀ E ⥤ Rational D c W₀ E)
    (hV : ∀ MN : Rational D c W₀ E × Rational D c W₀ E,
      V.obj MN = ⟨U.obj (MN.1.obj, MN.2.obj)⟩)
    (mu : ∀ M N : Integral D c W₀ E, (transport D c W₀ E).obj (U.obj (M, N)) ≅
      U.obj ((transport D c W₀ E).obj M, (transport D c W₀ E).obj N))
    (M N : Rational D c W₀ E) :
    (weilFrobeniusPullback D c W₀ E).obj (V.obj (M, N)) ≅
      V.obj ((weilFrobeniusPullback D c W₀ E).obj M,
        (weilFrobeniusPullback D c W₀ E).obj N) :=
  (weilFrobeniusPullback D c W₀ E).mapIso (eqToIso (hV (M, N))) ≪≫
    (pbcRationalization _ (pbcStageDatum.{u} c.l c.Qbar E)
      (pbcStageUniformizer.{u} c.l c.Qbar E)).mapIso (mu M.obj N.obj) ≪≫
        (eqToIso (hV ((weilFrobeniusPullback D c W₀ E).obj M,
          (weilFrobeniusPullback D c W₀ E).obj N))).symm

attribute [local irreducible] component rationalMu

/-- The ordinary rational tensor with its specified Weil structure. Source: descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
def ordinaryPair (d : RationalData (D := D) (c := c) (W₀ := W₀) (E := E))
    (K L : WeilD D c W₀ E) : WeilD D c W₀ E :=
  Endofunctor.IsoAlgebra.mk (d.ordinary.obj (K.carrier, L.carrier))
    (rationalMu (ordinary d.integral.closure) d.ordinary d.ordinary_raw.2.1
      (ordinaryMu d.integral.closure) K.carrier L.carrier ≪≫
        d.ordinary.mapIso (Iso.prod K.str L.str))

/-- The completed rational tensor with its specified Weil structure. Source: descent argument
(blueprint: lem-wf-tensor-comparison-rational-weil-descent). -/
def completedPair (d : RationalData (D := D) (c := c) (W₀ := W₀) (E := E))
    (K L : WeilD D c W₀ E) : WeilD D c W₀ E :=
  Endofunctor.IsoAlgebra.mk (d.completed.obj (K.carrier, L.carrier))
    (rationalMu (completed d.integral.closure) d.completed d.completed_raw.2.1
      (completedMu d.integral.closure) K.carrier L.carrier ≪≫
        d.completed.mapIso (Iso.prod K.str L.str))

attribute [local irreducible] ordinaryPair completedPair
  ordinary completed weilFrobeniusPullback weilScalarExtension weilScalarSystem

/-- Rational naturality and equivariance of the actual completion-unit comparison.
Source: latest fix-prop-projection-formula.proof.md, penultimate sentence;
DAG conditional descent argument, steps 1--5
(blueprint: lem-wf-tensor-comparison-rational-weil-descent).
Proof: (1) Apply raw rationalization to the two integral inverse equations.
(2) For integral u,v, divide the integral naturality square by varpi^(r+s).
Every rational arrow has such a numerator, by combining finitely many denominators;
no torsion cancellation or invertibility of the numerator is used.
(3) Rationalize the assumed integral Frobenius square. (4) Apply step 2 to the arbitrary
rational structure isomorphisms and compose with the ordinary pullback comparison.
Substitute step 3 to obtain the stated equivariance square. (5) Multiply that square
by the inverse component and its Frobenius image to obtain inverse equivariance.
Both composites are identities by step 1. -/
theorem rational_descent
    (d : RationalData (D := D) (c := c) (W₀ := W₀) (E := E)) :
    (∀ (M N M' N' : Rational D c W₀ E) (f : M ⟶ M') (g : N ⟶ N'),
      d.ordinary.map (Prod.mkHom f g) ≫ (component d M' N').hom =
        (component d M N).hom ≫ d.completed.map (Prod.mkHom f g)) ∧
    ∀ K L : WeilD D c W₀ E,
      (rationalMu (ordinary d.integral.closure) d.ordinary d.ordinary_raw.2.1
        (ordinaryMu d.integral.closure) K.carrier L.carrier).hom ≫
          d.ordinary.map (Prod.mkHom K.str.hom L.str.hom) ≫
            (component d K.carrier L.carrier).hom =
        (weilFrobeniusPullback D c W₀ E).map (component d K.carrier L.carrier).hom ≫
          (rationalMu (completed d.integral.closure) d.completed d.completed_raw.2.1
            (completedMu d.integral.closure) K.carrier L.carrier).hom ≫
              d.completed.map (Prod.mkHom K.str.hom L.str.hom) ∧
      ∃ e : ordinaryPair d K L ≅ completedPair d K L,
        HEq e.hom.hom.f (component d K.carrier L.carrier).hom ∧
        HEq e.inv.hom.f (component d K.carrier L.carrier).inv := by
  sorry

/-- At any common finite field the localized unit and inverse represent inverse Weil
morphisms. Source: latest fix-prop-projection-formula.proof.md, penultimate sentence;
DAG conditional descent argument, step 6
(blueprint: lem-wf-tensor-comparison-rational-weil-descent).
Proof: apply the two specified Weil transition functors to the input objects.
Apply rational_descent at the chosen common field, including the inverse component.
The stage inclusion sends both inverse equations to inverse equations in the common-stage
category. Its arrows are precisely the classes represented at that field, with the
normalized identity transition. Thus the assertion also includes L=E=F. No comparison
at another field is identified without its transition maps. -/
theorem common_stage_descent
    (d : ∀ J : Padic.FiniteCoefficientFields c.l c.Qbar,
      RationalData (D := D) (c := c) (W₀ := W₀) (E := J))
    (F L : Padic.FiniteCoefficientFields c.l c.Qbar) (hE : E ≤ L) (hF : F ≤ L)
    (K : WeilD D c W₀ E) (N : WeilD D c W₀ F) :
    ∃ e : ordinaryPair (d L) ((weilScalarExtension D c W₀ hE).obj K)
          ((weilScalarExtension D c W₀ hF).obj N) ≅
        completedPair (d L) ((weilScalarExtension D c W₀ hE).obj K)
          ((weilScalarExtension D c W₀ hF).obj N),
      HEq e.hom.hom.f (component (d L)
        ((weilScalarExtension D c W₀ hE).obj K).carrier
        ((weilScalarExtension D c W₀ hF).obj N).carrier).hom ∧
      HEq e.inv.hom.f (component (d L)
        ((weilScalarExtension D c W₀ hE).obj K).carrier
        ((weilScalarExtension D c W₀ hF).obj N).carrier).inv ∧
      ∃ eQ : ((weilScalarSystem D c W₀).ι L).obj
            (ordinaryPair (d L) ((weilScalarExtension D c W₀ hE).obj K)
              ((weilScalarExtension D c W₀ hF).obj N)) ≅
          ((weilScalarSystem D c W₀).ι L).obj
            (completedPair (d L) ((weilScalarExtension D c W₀ hE).obj K)
              ((weilScalarExtension D c W₀ hF).obj N)),
        eQ.hom = ((weilScalarSystem D c W₀).ι L).map e.hom ∧
        eQ.inv = ((weilScalarSystem D c W₀).ι L).map e.inv := by
  sorry

end WeilConjectures.WfTensorComparison
