/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.TraceFormulaSchemeGaloisComparison
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.TraceFormulaIteratedWeil
public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.ZetaWeil.FiniteTraceGlobalOperator
public import WeilConjectures.ZetaWeil.FiniteTraceFormulaConventions.FiniteTraceGlobalOperatorTriangulated
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation2
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SmoothPurity.TraceFixedScheme
public import WeilConjectures.AlgebraicGeometry.FixedScheme
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobeniusFiniteRadicial
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import Mathlib.Lean.Meta.CongrTheorems
public import WeilConjectures.AlgebraicGeometry.TraceOperations.GeometricOperationPackage
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.RelativeFrobeniusGeometricFiber
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius

/-! # Agreement with geometric Weil Frobenius

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-trace-formula/sec-frobenius-correspondences/
sk-lem-tf-frobenius-convention/_section.md and its proof.
(blueprint: sk-lem-tf-frobenius-convention).

All coefficients are the arbitrary finite commutative primary ring of
`FiniteTraceFormulaConventions`. Comparisons are the specified absolute-Frobenius
cancellation, restricted to the actual constructible finite-Tor full subcategory.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
open WeilConjectures.CondensedFrobeniusOperators
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteTraceFormulaConventions

/-- Both Frobenius pullbacks preserve Dctf, so their comparison restricts to it.
Source: sk-lem-tf-frobenius-convention, first assertion
(blueprint: sk-lem-tf-frobenius-convention).
Proof: semilinear pullback is the exact automorphism action of the recorded strict
Weil category, through the canonical left-derived/exact comparison. It preserves
bounded constructibility and the same finite Tor interval. Absolute Frobenius has
its relative-Frobenius trivialization on the small pro-etale site; cancel it using
schemeGaloisComparisonFunctor. Transport the two properties through this isomorphism
for scheme pullback. This includes zero objects and the empty scheme. -/
theorem convention_pullback_mem (T : FiniteTraceFormulaConventions.{u})
    (m : ℕ) (hm : 1 ≤ m)
    (K : ConstantModelConstructibleFiniteTor T.coefficients T.geometricScheme.left) :
    (constantModelBoundedConstructible T.coefficients T.geometricScheme.left ⊓
      fun M ↦ DerivedCategory.finiteTorAmplitude _ M)
        ((L T.coefficients (T.datum.schemeFrobeniusIterate T.X₀ m)).obj K.obj) ∧
    (constantModelBoundedConstructible T.coefficients T.geometricScheme.left ⊓
      fun M ↦ DerivedCategory.finiteTorAmplitude _ M)
        ((L T.coefficients ((geometricFrobeniusGeometry T.datum T.X₀).h.pow m).hom).obj
          K.obj) := by
  let P := constantModelBoundedConstructible T.coefficients T.geometricScheme.left ⊓
    fun M ↦ DerivedCategory.finiteTorAmplitude _ M
  have hb : (constantModelBoundedConstructible T.coefficients
      T.geometricScheme.left).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined T.coefficients
      T.geometricScheme.left).2.1
  have hG : P ((L T.coefficients
      ((geometricFrobeniusGeometry T.datum T.X₀).h.pow m).hom).obj K.obj) :=
    P.prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory T.coefficients
        ((geometricFrobeniusGeometry T.datum T.X₀).h.pow m).hom).app K.obj).symm
      (StrictWeilCondensed.action_mem T.coefficients
        ((geometricFrobeniusGeometry T.datum T.X₀).h.pow m) K)
  exact ⟨P.prop_of_iso
    ((schemeGaloisComparisonFunctor T.coefficients T.datum T.X₀ m hm).app K.obj).symm hG,
    hG⟩

/-- The actual scheme pullback, restricted by its preservation theorem.
Source: sk-lem-tf-frobenius-convention, domain Dctf
(blueprint: sk-lem-tf-frobenius-convention). -/
def conventionSchemePullback (T : FiniteTraceFormulaConventions.{u})
    (m : ℕ) (hm : 1 ≤ m) :
    ConstantModelConstructibleFiniteTor T.coefficients T.geometricScheme.left ⥤
      ConstantModelConstructibleFiniteTor T.coefficients T.geometricScheme.left :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ L T.coefficients (T.datum.schemeFrobeniusIterate T.X₀ m))
    (fun K ↦ (T.convention_pullback_mem m hm K).1)

/-- The actual semilinear pullback on the same full subcategory.
Source: sk-lem-tf-frobenius-convention, codomain Dctf
(blueprint: sk-lem-tf-frobenius-convention). -/
def conventionGeometricPullback (T : FiniteTraceFormulaConventions.{u})
    (m : ℕ) (hm : 1 ≤ m) :
    ConstantModelConstructibleFiniteTor T.coefficients T.geometricScheme.left ⥤
      ConstantModelConstructibleFiniteTor T.coefficients T.geometricScheme.left :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙
      L T.coefficients ((geometricFrobeniusGeometry T.datum T.X₀).h.pow m).hom)
    (fun K ↦ (T.convention_pullback_mem m hm K).2)

/-- Kappa_m is the restriction of the specified factorization/compositor/site comparison.
It is a natural isomorphism of endofunctors of Dctf, not a family of unrelated choices.
Source: sk-lem-tf-frobenius-convention, first display
(blueprint: sk-lem-tf-frobenius-convention). -/
def conventionComparison (T : FiniteTraceFormulaConventions.{u})
    (m : ℕ) (hm : 1 ≤ m) :
    T.conventionSchemePullback m hm ≅ T.conventionGeometricPullback m hm :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((schemeGaloisComparisonFunctor T.coefficients T.datum T.X₀ m hm).app K.obj))
    (fun f ↦ ObjectProperty.hom_ext _
      ((schemeGaloisComparisonFunctor T.coefficients T.datum T.X₀ m hm).hom.naturality
        f.hom))

/-- The natural comparisons respect the addition of positive exponents, with all
canonical pullback compositors displayed. This is iteration compatibility of kappa_m.
Source: sk-lem-tf-frobenius-convention, first paragraph of proof
(blueprint: sk-lem-tf-frobenius-convention).
Proof: factor Phi^m as absolute Frobenius followed by geometric Galois Frobenius.
Relative Frobenius trivializations multiply and are natural in the pulled-back module.
Expand the two factorizations at m and n; naturality moves the second trivialization
past the first Galois pullback. The pullback associativity law and multiplicativity
of the trivialization identify the result with cancellation at m+n. Restriction to
the full subcategory retains the identical components and equations. -/
theorem convention_comparison_iteration (T : FiniteTraceFormulaConventions.{u})
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let P := fun j ↦ T.datum.schemeFrobeniusIterate T.X₀ j
    let G := fun j ↦ ((geometricFrobeniusGeometry T.datum T.X₀).h.pow j).hom
    let κ := fun j hj ↦ (schemeGaloisComparisonFunctor T.coefficients T.datum T.X₀ j hj).hom
    ∃ hP : P m ≫ P n = P (m + n), ∃ hG : G m ≫ G n = G (m + n),
      κ (m + n) (by omega) =
        eqToHom (congrArg (L T.coefficients) hP.symm) ≫
        (leftDerivedUpperStarComp T.coefficients (P m) (P n)).hom ≫
        Functor.whiskerLeft (L T.coefficients (P n)) (κ m hm) ≫
        Functor.whiskerRight (κ n hn) (L T.coefficients (G m)) ≫
        (leftDerivedUpperStarComp T.coefficients (G m) (G n)).inv ≫
        eqToHom (congrArg (L T.coefficients) hG) := by
  exact schemeGaloisComparison_add T.coefficients T.datum T.X₀ m n hm hn

/-- Identify the model powers in sk-d-weil with the same scheme powers in the graph API.
Source: sk-lem-tf-frobenius-convention, opening context
(blueprint: sk-lem-tf-frobenius-convention).
Proof: at zero both powers are the identity. At successor, modelFrobenius_left identifies
the model endomorphism with relativeFrobenius. Substitute the induction hypothesis and
use the endomorphism power successor law. No identification with semilinear Frobenius
as scheme maps is made. -/
theorem convention_model_power (T : FiniteTraceFormulaConventions.{u}) (m : ℕ) :
    (TraceWeilComplex.frobeniusPower
      (TraceWeilComplex.modelFrobenius T.datum T.X₀) m).left =
        T.datum.schemeFrobeniusIterate T.X₀ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [TraceWeilComplex.frobeniusPower, Over.comp_left, ih,
      TraceWeilComplex.modelFrobenius_left]
    change (End.of (T.datum.relativeFrobenius T.X₀) ^ m) ≫
      T.datum.relativeFrobenius T.X₀ =
      End.of (T.datum.relativeFrobenius T.X₀) ^ (m + 1)
    exact (pow_succ' (End.of (T.datum.relativeFrobenius T.X₀)) m).symm

/-- The model Weil complex with psi = phi kappa_1. The identity-power unitor in
iteratedWeilMap at one is precisely the canonical identification with phi.
Source: sk-lem-tf-frobenius-convention, put psi = phi kappa_1
(blueprint: sk-lem-tf-frobenius-convention). -/
def conventionModelComplex (T : FiniteTraceFormulaConventions.{u}) (K : T.Weil) :
    TraceWeilComplex.WeilComplex T.coefficients T.geometricScheme :=
  TraceWeilComplex.FrobeniusCorrespondence.toWeilComplex T.datum
    (K := K.carrier)
    (eqToHom (congrArg (fun f ↦ (L T.coefficients f).obj K.carrier.obj)
        (by
          simpa only [TraceWeilComplex.frobeniusPower, Category.id_comp] using
            T.convention_model_power 1)) ≫
      (schemeGaloisComparisonFunctor T.coefficients T.datum T.X₀ 1 (by omega)).hom.app
        K.carrier.obj ≫
      (iteratedWeilMap T.coefficients T.datum T.X₀ K.carrier.obj
        (T.weilStructure K) 1).hom)

/-- Agreement of the coefficient iterates and compact-support operators, including
an arbitrary coefficient morphism without a Weil structure or invertibility assumption.
Source: sk-lem-tf-frobenius-convention, last two displays and final sentence
(blueprint: sk-lem-tf-frobenius-convention).
Proof: use conventionComparison, the absolute-Frobenius cancellation on Dctf, with
its iteration compatibility. Induct on m in the recursion of sk-d-weil. At one the
identity pullback unitor gives psi = phi kappa_1. In the successor step naturality
moves kappa past the previous Weil iterate; convention_comparison_iteration and the
iterated-Weil cocycle give psi_m = phi^[m] kappa_m. The model-power equalities only
translate the two recorded notations for Phi^m. For operators, identify sk-d-weil's
graph with the graph in graph_operator_arbitrary. The unique adjoint mate of kappa_m
identifies the pullback units, hence the compact-support pullback maps, including the
base-automorphism insertion. Composing with compact cohomology of phi^[m] gives
geometric Frobenius in degree m. Pasting units gives its cocycle law and induction
identifies it with the m-th power at one. The mate calculation uses no invertibility
of the last coefficient map, so it also proves the final clause for every v. -/
theorem frobenius_convention (T : FiniteTraceFormulaConventions.{u})
    (c : Compactification T.geometricScheme.hom) (m : ℕ) (hm : 1 ≤ m) :
    (∀ K : T.Weil,
      (T.conventionModelComplex K).iterate m =
        eqToHom (congrArg (fun f ↦ (L T.coefficients f).obj K.carrier.obj)
          (T.convention_model_power m)) ≫
        (schemeGaloisComparisonFunctor T.coefficients T.datum T.X₀ m hm).hom.app
          K.carrier.obj ≫
        (iteratedWeilMap T.coefficients T.datum T.X₀ K.carrier.obj
          (T.weilStructure K) m).hom ∧
      T.graphOperator K.carrier m
        (eqToHom (congrArg (fun f ↦ (L T.coefficients f).obj K.carrier.obj)
          (T.convention_model_power m).symm) ≫
          (T.conventionModelComplex K).iterate m) c =
        (T.globalFrobenius K c 1) ^ m) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor T.coefficients T.geometricScheme.left)
      (v : (L T.coefficients
        ((geometricFrobeniusGeometry T.datum T.X₀).h.pow m).hom).obj K.obj ⟶ K.obj),
      T.graphOperator K m
        ((schemeGaloisComparisonFunctor T.coefficients T.datum T.X₀ m hm).hom.app K.obj ≫ v)
        c = T.compactTransportMap K c m ≫ (T.operatorCompactSupport c).map v) := by
  sorry

end WeilConjectures.FiniteTraceFormulaConventions
