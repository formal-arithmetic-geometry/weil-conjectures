/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeDirectComparison

/-! # Native presentation of derived system direct image

## References

* Stacks Project, Tags 03D7, 07A7 and 0941.
* Zheng, Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard constantSheaf

/-- Native direct-image evaluation in the constant-ring module presentation. -/
def nativeProperConstantEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f ⋙
      coefficientSequenceDerivedEvaluation l E Y n ≅
    coefficientSequenceDerivedEvaluation l E X n ⋙
      proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) := by
  have := proEtaleConstantModuleDirectImage_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  exact ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f n ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
      (compactSupportDirectModel f (Padic.coefficientExtensionRing l E (n + 1))))

/-- The two derived models of sequence direct image have the same normalized evaluations.
This is purely a presentation comparison: no reduction or completed coefficients occur. -/
theorem nativeProperDerivedPresentation (o : IntegralSystemRealization.Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ e : IntegralSystemRealization.Operations.push l E o f ≅
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f,
      ∀ (N : coefficientSequenceDerived l E X) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Y n).map (e.hom.app N) ≫
            (nativeProperConstantEvaluation l E f n).hom.app N =
          ((o.evaluation f).evaluation n).hom.app N := by
  let d : IntegralSystemRealization.Direct l E f := o.direct f
  let ed : IntegralSystemRealization.DirectEvaluation l E d := o.evaluation f
  let e₀ := IntegralSystemRealization.integralNativeDirectIso l E f d
  refine ⟨e₀, ?_⟩
  intro N n
  exact IntegralSystemRealization.integralNativeDirectComparison l E f d ed N n

end WeilConjectures
