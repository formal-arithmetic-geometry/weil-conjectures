/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData
public import WeilConjectures.SixFunctors.CoefPairingExceptionalTests
import WeilConjectures.SixFunctors.CoefficientSystemFiniteTestEvaluation
import WeilConjectures.SixFunctors.IntegralDualizingFiniteCounitTest

/-! Evaluating the normalized system trace on a finite scalar test. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
/-- The finite-level Hom map obtained by evaluating the normalized system trace
is bijective. This is the finite duality/site-comparison step: it has no
inverse-limit assembly and no use of the global system Hom map.

Source: prop-coef-integral-dualizing, proof paragraph 2 (finite trace test);
prop-asd-internal-adjunction, exceptional-counit step; Stacks 07A6, 08J9, 0941.
(blueprint: lem-coef-system-finite-trace-evaluation-bijective).

Proof: the left adjoint of tower evaluation at n is the free representable tower,
so maps from the pulled-back test tensored with the cartesian reduction of K to
an arbitrary Q are, by scalar extension-restriction adjunction, the finite
tensor maps from the nth values to the nth evaluation of Q; no normalization of
Q is needed. The same calculation identifies the target Hom set with maps from
the nth evaluation of the compact support of that tensor to the evaluated base
unit. Use t.supportComparison, compactSupportSystemEvaluation and eQ n to
identify these values with the finite compact support of the finite input and
the finite dualizing object; the equation t.trace_evaluation identifies the
displayed map with postcomposition by integralDualizingFiniteSystemCounit
followed by the inverse of t.unitEvaluation n. The finite constructible origin
of the reduced input and its finite Tor interval from hK, with the finite
duality site comparison, transport this map to the ordinary etale exceptional
adjunction Hom equivalence for the compactification, which is bijective also
for the arbitrary tensor test. Transport back. -/
theorem integralDualizingSystem_finite_trace_evaluation_bijective
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (t : IntegralDualizingSystemTraceData D l E X S G Q eQ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : finiteTorConstructibleIntegral l E X K) (n : ℕ)
    (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
    Function.Bijective (fun g :
      S.systemClosed.tensor.obj
        ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
          ((coefPairingEvaluationLeft l E n).obj T), S.reduction.obj K) ⟶ coefTraceInput l E X Q ↦
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map
        (G.properModules.rightDerivedFunctor.map (G.openModules.mapDerivedCategory.map g)) ≫
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map t.trace ≫
        (t.unitEvaluation n).hom) := by
  let A := S.systemClosed.tensor.obj
    ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
      ((coefPairingEvaluationLeft l E n).obj T), S.reduction.obj K)
  let Ex := coefficientSequenceDerivedEvaluation l E X n
  let Ey := coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n
  let F := sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
    (Padic.coefficientExtensionRing l E (n + 1))
  let c : Ey.obj (G.properModules.rightDerivedFunctor.obj
      (G.openModules.mapDerivedCategory.obj A)) ≅ F.obj (Ex.obj A) :=
    Ey.mapIso (t.supportComparison.app A) ≪≫
      (compactSupportSystemEvaluation l E (finiteDualizingCompactification D X) n).app A
  let eQHom := Iso.homCongr (Iso.refl (Ex.obj A)) (eQ n)
  let eSupportHom := (Iso.homCongr c (Iso.refl
    ((finiteDualizingRealization l E (Spec (.of D.k)) n).obj
      (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))))).symm
  have heval := coefficientSystem_finite_test_evaluation_bijective
    D l E X S G (S.reduction.obj K) (coefTraceInput l E X Q)
      (S.reduction_normalized K) n T
  have hfinite := integralDualizingFiniteCounit_test_bijective
    D l hl E X S G K hK n T
  have hbij := eSupportHom.bijective.comp (hfinite.comp (eQHom.bijective.comp heval))
  convert hbij using 1
  funext g
  simp only [Function.comp_apply, eQHom, eSupportHom, Iso.homCongr,
    Equiv.symm, Equiv.coe_fn_mk, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id]
  change Ey.map (G.properModules.rightDerivedFunctor.map
      (G.openModules.mapDerivedCategory.map g)) ≫ Ey.map t.trace ≫
        (t.unitEvaluation n).hom =
    c.hom ≫ F.map (Ex.map g ≫ (eQ n).hom) ≫
      integralDualizingFiniteSystemCounit D l E X n
  rw [t.trace_evaluation n]
  have hs := congrArg Ey.map (t.supportComparison.hom.naturality g)
  dsimp only [Functor.comp_map] at hs
  rw [Ey.map_comp, Ey.map_comp] at hs
  have hn := (compactSupportSystemEvaluation l E
    (finiteDualizingCompactification D X) n).hom.naturality g
  dsimp only [Functor.comp_map] at hn
  dsimp only [c, Iso.trans_hom, Functor.mapIso_hom]
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ (Ey.map (t.supportComparison.hom.app _)), hs]
  simp only [Category.assoc]
  rw [← Category.assoc _ ((compactSupportSystemEvaluation l E
    (finiteDualizingCompactification D X) n).hom.app _), hn]
  simp only [Category.assoc]
  rfl

end WeilConjectures
