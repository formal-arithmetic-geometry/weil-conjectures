/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.WeilTensorProduct
import Sheaf.Paper.WfConstructibleTensorKoszulUnit
import Sheaf.Paper.WfTensorPullbackCompletionUnitSquare
import all Sheaf.Paper.WeilTensorProduct

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
attribute [local irreducible] wfPullbackCompletion proEtaleCanonicalTensorComparison
  ScalarLocalization.composition pbcCompletedScalarSections wfCompletionObj
  intrinsicCompletion intrinsicCompletionUnit

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
  refine ⟨?_, ?_⟩
  · intro MN
    exact (wfConstructibleTensorKoszulUnit D c X₀ E).1 MN.1 MN.2
  · intro MN PQ f
    exact (wfConstructibleTensorKoszulUnit D c X₀ E).2 MN.1 PQ.1 MN.2 PQ.2 f.1 f.2

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
  have hi : IsIso ((chi D c X₀ E).app (M, N)) := by
    have : IsIso (unit D c X₀ E ((ordinaryAmbient D c X₀ E).obj (M, N))) :=
      ((integral D c X₀ E).1 (M, N)).2.2
    let i : (ordinary D c X₀ E).obj (M, N) ≅ (completed D c X₀ E).obj (M, N) :=
      ObjectProperty.isoMk _ (asIso (unit D c X₀ E
        ((ordinaryAmbient D c X₀ E).obj (M, N))))
    exact i.isIso_hom
  refine ⟨hi, ?_⟩
  have hs : (pullback D c X₀ E).map ((chi D c X₀ E).app (M, N)) ≫
      (completedMu D c X₀ E M N).hom =
      (ordinaryMu D c X₀ E M N).hom ≫
        (chi D c X₀ E).app ((pullback D c X₀ E).obj M,
          (pullback D c X₀ E).obj N) := by
    apply ObjectProperty.hom_ext
    exact (wfTensorPullbackCompletionUnitSquare D c X₀ E M N).1
  rw [← Category.assoc _ (completedMu D c X₀ E M N).hom, hs,
    Category.assoc]
  exact congrArg ((ordinaryMu D c X₀ E M N).hom ≫ ·)
    ((chi D c X₀ E).naturality (Prod.mkHom phi.hom psi.hom))

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

/-- Full normalized comparison property used to decompose the target proof.
It packages the target's existence conjunct without the outer uniqueness quantifier. -/
def WfTensorCompletion.FullProperty (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (R : WfTensorCompletion.RationalComparison D c X₀ E) : Prop :=
      R.Normalized D c X₀ E ∧
      ∀ K L : WeilD D c X₀ E,
        (R.ordinaryMu.app (K.carrier, L.carrier) ≪≫
            R.ordinary.mapIso (K.str.prod L.str)).hom ≫
            R.chi.hom.app (K.carrier, L.carrier) =
          ((weilFrobeniusPullback D c X₀ E).mapIso
              (R.chi.app (K.carrier, L.carrier)) ≪≫
            R.completedMu.app (K.carrier, L.carrier) ≪≫
            R.completed.mapIso (K.str.prod L.str)).hom ∧
        ∃ e : R.ordinaryPair D c X₀ E K L ≅ R.completedPair D c X₀ E K L,
          e.hom.hom.f = R.chi.hom.app (K.carrier, L.carrier)

/-- Existence part of the normalized rational comparison; uniqueness is omitted.
Source: blueprint proof step 13. The construction supplies the ordinary and completed
localized bifunctors, the completion-unit comparison, the two Frobenius comparisons,
and the induced Weil-pair isomorphisms.
(blueprint: lem-wf-tensor-completion-frobenius-existence).
Proof: restrict ordinary derived tensor and its intrinsic completion to integral
constructibles using wfConstructibleTensorKoszulUnit. Both bifunctors are linear in
each variable: derived tensor is bilinear and the completion reflector is linear by
its unit and the injective Hom comparison. Extend the two Hom maps by scalar extension
in both variables, sending (s tensor f, t tensor g) to st tensor T(f,g). The integral
identity and composition equations, together with commutativity of localized scalars,
prove the bifunctor laws on pure tensors; additivity proves them on every morphism.
Localize the invertible completion-unit components to obtain chi. Localize the ordinary
and completed pullback comparisons as well. Their integral naturality equations extend
to arbitrary localized arrows by the same pure-tensor calculation; these components
therefore define the three required natural isomorphisms. Their definitions give the
two localization equalities and the three component normalizations.
The integral pullback/unit square is wfTensorPullbackCompletionUnitSquare. Tensoring
that equality with one proves the rational square on every object, since objects are
unchanged. Naturality of rational chi, applied to the product of the two rational Weil
structure arrows, then gives the displayed Weil equation; no integral lift of either
structure isomorphism is needed. The equation makes chi a morphism of the two
IsoAlgebras. Compose it with its inverse and cancel chi to obtain the inverse's
commuting equation. Their underlying inverse identities lift through the faithful
IsoAlgebra forgetful functor, yielding the required Weil-pair isomorphism. -/
theorem wfTensorCompletionFrobenius_exists (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃ R : WfTensorCompletion.RationalComparison D c X₀ E,
      WfTensorCompletion.FullProperty D c X₀ E R := by
  sorry



/-- Integral precomposition determines a rational bifunctor in both variables. -/
private theorem tensor_precomp_injective
    {A : Type*} [CommRing A] {C : Type*} [Category C] [Preadditive C] [Linear A C]
    (p : A) {B : Type*} [Category B]
    (F G : ScalarLocalization A C p × ScalarLocalization A C p ⥤ B)
    (h : ((ScalarLocalization.localization A C p).prod
      (ScalarLocalization.localization A C p)) ⋙ F =
        ((ScalarLocalization.localization A C p).prod
          (ScalarLocalization.localization A C p)) ⋙ G) : F = G := by
  apply Functor.curry_obj_injective
  apply scalarLocalization_precomp_injective p
  apply Functor.flip_injective
  apply scalarLocalization_precomp_injective p
  apply Functor.flip_injective
  apply Functor.uncurry_obj_injective
  simpa only [Functor.uncurry_obj_curry_obj_flip_flip] using h

/-- Normalization fixes the bifunctors and all three isomorphisms componentwise. -/
private theorem normalized_unique (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (R S : RationalComparison D c X₀ E)
    (hR : R.Normalized D c X₀ E) (hS : S.Normalized D c X₀ E) : R = S := by
  have ho : R.ordinary = S.ordinary :=
    tensor_precomp_injective _ _ _ (hR.1.trans hS.1.symm)
  have hc : R.completed = S.completed :=
    tensor_precomp_injective _ _ _ (hR.2.1.trans hS.2.1.symm)
  cases R with
  | mk ro rc ri rm rn =>
    cases S with
    | mk so sc si sm sn =>
      dsimp only at ho hc
      subst so
      subst sc
      have hi : ri = si := by
        apply Iso.ext
        apply NatTrans.ext
        funext MN
        exact eq_of_heq ((hR.2.2 MN.1.obj MN.2.obj).1.trans
          (hS.2.2 MN.1.obj MN.2.obj).1.symm)
      have hm : rm = sm := by
        apply Iso.ext
        apply NatTrans.ext
        funext MN
        exact eq_of_heq ((hR.2.2 MN.1.obj MN.2.obj).2.1.trans
          (hS.2.2 MN.1.obj MN.2.obj).2.1.symm)
      have hn : rn = sn := by
        apply Iso.ext
        apply NatTrans.ext
        funext MN
        exact eq_of_heq ((hR.2.2 MN.1.obj MN.2.obj).2.2.trans
          (hS.2.2 MN.1.obj MN.2.obj).2.2.symm)
      subst si
      subst sm
      subst sn
      rfl

/-- Uniqueness part, supplied for two normalized comparison packages.
Source: localization precomposition and prescribed integral components. -/
theorem wfTensorCompletionFrobenius_unique (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (R S : WfTensorCompletion.RationalComparison D c X₀ E)
    (hR : WfTensorCompletion.FullProperty D c X₀ E R)
    (hS : WfTensorCompletion.FullProperty D c X₀ E S) : R = S := by
  exact normalized_unique D c X₀ E R S hR.1 hS.1



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
  obtain ⟨R, hR⟩ := wfTensorCompletionFrobenius_exists D c X₀ E
  -- The existence package already has exactly the target's normalized property.
  refine ⟨R, hR, ?_⟩
  intro S hS
  exact wfTensorCompletionFrobenius_unique D c X₀ E S R hS hR





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
  obtain ⟨S, hS⟩ := wfTensorCompletionFrobenius_exists D c X₀ G
  have heq := normalized_unique D c X₀ G R S _hR hS.1
  subst S
  obtain ⟨e, he⟩ := (hS.2 ((weilScalarExtension D c X₀ h).obj K)
    ((weilScalarExtension D c X₀ k).obj L)).2
  exact ⟨e, he, ((weilScalarSystem D c X₀).ι G).mapIso e, rfl⟩


end WeilConjectures
