/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.WeilTensorProduct
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.TwFrobeniusAction
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.SixFunctors.ConstructibleTensorCompletion
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcWeilCategory
import Sheaf.Paper.WeilCompletedTensorReflector

/-!
# Frobenius compatibility of ordinary and completed tensor

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md, step 13
(blueprint: lem-wf-tensor-completion-frobenius).

## Main statements

* `WfTensorCompletion.integral`: completeness, constructibility and unit naturality.
* `WfTensorCompletion.integral_equivariance`: the integral tensor Weil equation.
* `wfTensorCompletionFrobenius`: the normalized rational comparison and Weil isomorphism.
* `wfTensorCompletionCommonField`: its image at any common finite coefficient field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.all false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace WfTensorCompletion

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀)))
  [hsep : IsSeparated X₀.hom] [hft : LocallyOfFiniteType X₀.hom]
  [hqc : QuasiCompact X₀.hom] (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The specified completed-coefficient integral category on the geometric fibre.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev Integral := PbcBoundedConstructibleComplete (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E)

/-- The uniformizer is the single Koszul generator; this is the existing completion functor.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev completion := wfCompletion (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1
  (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)

/-- The existing completion unit, retaining its actual mapping-fibre normalization.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev unit := wfCompletionUnit (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1
  (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)

/-- The ordinary ambient derived tensor on the constructible inputs, with no completion.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev ordinaryAmbient : Integral D c X₀ E × Integral D c X₀ E ⥤
    PbcCompletedDerived (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E) :=
  ((ObjectProperty.ι _).prod (ObjectProperty.ι _)) ⋙
    wfOrdinaryDerivedTensor (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)

/-- The completed ambient tensor is ordinary tensor followed by the published reflector.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev completedAmbient := ordinaryAmbient D c X₀ E ⋙ completion D c X₀ E ⋙
  ObjectProperty.ι _

include hsep hft hqc in
/-- The canonical quotient/Koszul comparison is invertible and natural on integral inputs.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius).
Proof: use integral-stratified-perfect-characterization to identify both integral
conventions inside the same completed-coefficient derived category. Finite type over
k makes the fibre noetherian and finite-dimensional; separation gives qcqs and l≠p
makes l invertible. Constructible-tensor-completion gives completeness and an invertible
quotient-tower unit. The integer ring is a Noetherian DVR with finite residue field;
its positive quotients are finite and have the two-term free uniformizer resolution.
Constant-completion-equivalence therefore identifies the quotient and Koszul units.
Integral-operations-preserve-constructible gives bounded constructibility of the completed
tensor, hence also of the ordinary tensor. Finally the reflector's Hom bijection identifies
its morphism action and makes its unit natural in every pair of integral arrows. -/
theorem integral :
    (∀ MN : Integral D c X₀ E × Integral D c X₀ E,
      PbcIsBoundedConstructibleComplete (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) ((ordinaryAmbient D c X₀ E).obj MN) ∧
      PbcIsBoundedConstructibleComplete (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) ((completedAmbient D c X₀ E).obj MN) ∧
      IsIso (unit D c X₀ E ((ordinaryAmbient D c X₀ E).obj MN))) ∧
    ∀ (MN PQ : Integral D c X₀ E × Integral D c X₀ E) (f : MN ⟶ PQ),
      (ordinaryAmbient D c X₀ E).map f ≫
          unit D c X₀ E ((ordinaryAmbient D c X₀ E).obj PQ) =
        unit D c X₀ E ((ordinaryAmbient D c X₀ E).obj MN) ≫
          (completedAmbient D c X₀ E).map f := by
  sorry

/-- Restriction of ordinary tensor to the full integral constructible category.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def ordinary : Integral D c X₀ E × Integral D c X₀ E ⥤ Integral D c X₀ E :=
  ObjectProperty.lift _ (ordinaryAmbient D c X₀ E)
    (fun MN ↦ (integral D c X₀ E).1 MN |>.1)

/-- Restriction of completed tensor to the same full integral constructible category.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def completed : Integral D c X₀ E × Integral D c X₀ E ⥤ Integral D c X₀ E :=
  ObjectProperty.lift _ (completedAmbient D c X₀ E)
    (fun MN ↦ (integral D c X₀ E).1 MN |>.2.1)

/-- The actual completion unit lifted through the full constructible inclusion.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def chi : ordinary D c X₀ E ⟶ completed D c X₀ E where
  app MN := ObjectProperty.homMk (unit D c X₀ E ((ordinaryAmbient D c X₀ E).obj MN))
  naturality MN PQ f := ObjectProperty.hom_ext _ ((integral D c X₀ E).2 MN PQ f)

/-- The integral Frobenius is the existing exact coefficient transport.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev pullback := pbcIsoIntegralPullback (D.geometricFrobenius X₀).hom
  (pbcStageDatum.{u} c.l c.Qbar E)

/-- The ordinary pullback/tensor comparison restricted through the full inclusion.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def ordinaryMu (M N : Integral D c X₀ E) :
    (pullback D c X₀ E).obj ((ordinary D c X₀ E).obj (M, N)) ≅
      (ordinary D c X₀ E).obj ((pullback D c X₀ E).obj M, (pullback D c X₀ E).obj N) :=
  ObjectProperty.isoMk _
    ((proEtaleCanonicalTensorComparison (D.geometricFrobenius X₀).hom
      (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
      (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
      (asIso (completedCoefficientMap _ (pbcStageDatum.{u} c.l c.Qbar E)))
      (wfTensorModel _ (pbcStageDatum.{u} c.l c.Qbar E))
      (wfTensorModel _ (pbcStageDatum.{u} c.l c.Qbar E))).app (M.obj, N.obj))

/-- The existing completed comparison on the same inputs, restricted to constructibles.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def completedMu (M N : Integral D c X₀ E) :
    (pullback D c X₀ E).obj ((completed D c X₀ E).obj (M, N)) ≅
      (completed D c X₀ E).obj ((pullback D c X₀ E).obj M, (pullback D c X₀ E).obj N) :=
  ObjectProperty.isoMk _
    ((ObjectProperty.ι _).mapIso
      (wfIntegralTensorPullback (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (D.geometricFrobenius X₀)
        ((wfIntegralConstructibleInclusion _ (pbcStageDatum.{u} c.l c.Qbar E) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
          (wfUniformizer_generates D c E)).obj M)
        ((wfIntegralConstructibleInclusion _ (pbcStageDatum.{u} c.l c.Qbar E) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
          (wfUniformizer_generates D c E)).obj N)))

/-- Integral comparison with the two tensor Weil maps, and its inverse.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius).
Proof: write H for the exact Frobenius transport. Its finite constant comparisons
fix the uniformizer, so its Koszul comparisons preserve the degree-zero inclusions.
In the strict product/fibre model the unit is (u,0); the comparison applies the product
map to both summands and preserves zero. Consequently the completed tensor comparison
composed with H(chi) equals chi on the transported inputs composed with ordinaryMu.
Naturality of chi for the tensor of the two Weil maps now gives the displayed equation.
Both the unit and tensor structure maps are invertible, so the inverse also commutes. -/
theorem integral_equivariance (M N : Integral D c X₀ E)
    (phi : (pullback D c X₀ E).obj M ≅ M) (psi : (pullback D c X₀ E).obj N ≅ N) :
    IsIso ((chi D c X₀ E).app (M, N)) ∧
    (ordinaryMu D c X₀ E M N).hom ≫
        (ordinary D c X₀ E).map (Prod.mkHom phi.hom psi.hom) ≫
        (chi D c X₀ E).app (M, N) =
      (pullback D c X₀ E).map ((chi D c X₀ E).app (M, N)) ≫
        (completedMu D c X₀ E M N).hom ≫
        (completed D c X₀ E).map (Prod.mkHom phi.hom psi.hom) := by
  sorry

/-- The actual rational constructible coefficient stage; its objects remain integral objects.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev Rational := PbcRationalCategory (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- The actual integral-to-rational localization, tensoring each arrow with one.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev localization := pbcRationalization (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- A comparison package whose normalization below fixes all its maps and objects.
The tensor functors land in constructibles, so its fixed pairs are actual Weil objects.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
structure RationalComparison where
  ordinary : Rational D c X₀ E × Rational D c X₀ E ⥤ Rational D c X₀ E
  completed : Rational D c X₀ E × Rational D c X₀ E ⥤ Rational D c X₀ E
  chi : ordinary ≅ completed
  ordinaryMu : ordinary ⋙ weilFrobeniusPullback D c X₀ E ≅
    ((weilFrobeniusPullback D c X₀ E).prod (weilFrobeniusPullback D c X₀ E)) ⋙ ordinary
  completedMu : completed ⋙ weilFrobeniusPullback D c X₀ E ≅
    ((weilFrobeniusPullback D c X₀ E).prod (weilFrobeniusPullback D c X₀ E)) ⋙ completed

/-- Normalization on unchanged integral objects, pure tensors, units and pullback comparisons.
`HEq` retains the exact object equalities while prescribing the arrows, and does not
replace the maps by arbitrary isomorphisms. The localization equalities also fix all
denominators by functoriality.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def RationalComparison.Normalized (R : RationalComparison D c X₀ E) : Prop :=
  ((localization D c X₀ E).prod (localization D c X₀ E)) ⋙ R.ordinary =
      WfTensorCompletion.ordinary D c X₀ E ⋙ localization D c X₀ E ∧
  ((localization D c X₀ E).prod (localization D c X₀ E)) ⋙ R.completed =
      WfTensorCompletion.completed D c X₀ E ⋙ localization D c X₀ E ∧
  ∀ M N : Integral D c X₀ E,
    HEq (R.chi.hom.app (⟨M⟩, ⟨N⟩))
      ((localization D c X₀ E).map ((WfTensorCompletion.chi D c X₀ E).app (M, N))) ∧
    HEq (R.ordinaryMu.hom.app (⟨M⟩, ⟨N⟩))
      ((localization D c X₀ E).map (WfTensorCompletion.ordinaryMu D c X₀ E M N).hom) ∧
    HEq (R.completedMu.hom.app (⟨M⟩, ⟨N⟩))
      ((localization D c X₀ E).map (WfTensorCompletion.completedMu D c X₀ E M N).hom)

/-- The ordinary tensor Weil pair, using precisely the ordinary pullback comparison.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def RationalComparison.ordinaryPair (R : RationalComparison D c X₀ E)
    (K L : WeilD D c X₀ E) : WeilD D c X₀ E :=
  Endofunctor.IsoAlgebra.mk (R.ordinary.obj (K.carrier, L.carrier))
    (R.ordinaryMu.app (K.carrier, L.carrier) ≪≫ R.ordinary.mapIso (K.str.prod L.str))

/-- The completed tensor Weil pair, using the completed pullback comparison.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def RationalComparison.completedPair (R : RationalComparison D c X₀ E)
    (K L : WeilD D c X₀ E) : WeilD D c X₀ E :=
  Endofunctor.IsoAlgebra.mk (R.completed.obj (K.carrier, L.carrier))
    (R.completedMu.app (K.carrier, L.carrier) ≪≫ R.completed.mapIso (K.str.prod L.str))

end WfTensorCompletion
open WfTensorCompletion

/-- The normalized ordinary/completed tensor comparison is a natural Weil isomorphism.
Source: blueprint, projection-formula proof step 13
(blueprint: lem-wf-tensor-completion-frobenius).
Proof: first apply integral and integral_equivariance. The quotient-completion theorem and
constant-completion equivalence identify chi with the intrinsic unit, naturally in both
variables. Exact Frobenius coefficient transport fixes the uniformizer and the Koszul
inclusions; the strict (u,0) fibre model therefore gives the pullback/unit square.
Naturality for the tensor of Weil maps gives the tensor Weil equation. Inverting chi
also gives the inverse commuting equation. Raw rationalization keeps objects and sends
(f/pi^r,g/pi^s) to the tensor numerator divided by pi^(r+s). Bilinearity extends the
integral functors and comparisons uniquely, including naturality on every localized
arrow. Clear these denominators in the Weil equation; the integral numerator argument
only uses naturality and does not require those numerators to be isomorphisms. Thus chi
and its inverse give mutually inverse morphisms of actual constructible Weil pairs.
The displayed tensor Weil maps are written as composites of isomorphisms; their hom
parts are by definition mu followed by the tensor of the two Weil maps. -/
theorem wfTensorCompletionFrobenius (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃! R : RationalComparison D c X₀ E,
      R.Normalized D c X₀ E ∧
      ∀ K L : WeilD D c X₀ E,
        (R.ordinaryMu.app (K.carrier, L.carrier) ≪≫
            R.ordinary.mapIso (K.str.prod L.str)).hom ≫
            R.chi.hom.app (K.carrier, L.carrier) =
          ((weilFrobeniusPullback D c X₀ E).mapIso (R.chi.app (K.carrier, L.carrier)) ≪≫
            R.completedMu.app (K.carrier, L.carrier) ≪≫
            R.completed.mapIso (K.str.prod L.str)).hom ∧
        ∃ e : R.ordinaryPair D c X₀ E K L ≅ R.completedPair D c X₀ E K L,
          e.hom.hom.f = R.chi.hom.app (K.carrier, L.carrier) := by
  sorry

/-- The comparison remains the specified Weil isomorphism at any common finite field.
Source: blueprint, projection-formula proof step 13
(blueprint: lem-wf-tensor-completion-frobenius).
Proof: transport the two input Weil objects to the chosen common finite field G using
the recorded scalar-extension functors. Apply the normalized rational comparison at G.
Its equivariance and the inverse equation lift chi and chi inverse to Weil morphisms.
The common-stage inclusion is a functor and preserves isomorphisms; its image is the
class [G,chi]. The pair-category identity and composition laws make the two classes
inverse. This includes equal coefficient fields and every choice of a larger G. -/
theorem wfTensorCompletionCommonField (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (E F G : Padic.FiniteCoefficientFields c.l c.Qbar) (h : E ≤ G) (k : F ≤ G)
    (K : WeilD D c X₀ E) (L : WeilD D c X₀ F)
    (R : RationalComparison D c X₀ G) (_hR : R.Normalized D c X₀ G) :
    ∃ e : R.ordinaryPair D c X₀ G ((weilScalarExtension D c X₀ h).obj K)
          ((weilScalarExtension D c X₀ k).obj L) ≅
        R.completedPair D c X₀ G ((weilScalarExtension D c X₀ h).obj K)
          ((weilScalarExtension D c X₀ k).obj L),
      e.hom.hom.f = R.chi.hom.app
        (((weilScalarExtension D c X₀ h).obj K).carrier,
          ((weilScalarExtension D c X₀ k).obj L).carrier) ∧
      ∃ ebar : ((weilScalarSystem D c X₀).ι G).obj
          (R.ordinaryPair D c X₀ G ((weilScalarExtension D c X₀ h).obj K)
            ((weilScalarExtension D c X₀ k).obj L)) ≅
          ((weilScalarSystem D c X₀).ι G).obj
            (R.completedPair D c X₀ G ((weilScalarExtension D c X₀ h).obj K)
              ((weilScalarExtension D c X₀ k).obj L)),
        ebar = ((weilScalarSystem D c X₀).ι G).mapIso e := by
  sorry

end WeilConjectures
