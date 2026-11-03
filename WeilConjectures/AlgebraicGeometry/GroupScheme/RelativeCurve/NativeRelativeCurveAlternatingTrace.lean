/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
import WeilConjectures.DeligneLaumon.Reduction.TraceReality

/-! # Reality of native affine-curve alternating traces

Source: latest blueprint, lem-zl-relative-envelope-factor-reality.
(blueprint: lem-zl-native-relative-curve-alternating-trace)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RelativeCurve

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {U₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [hYsep : IsSeparated Y₀.hom]
  (h₀ : U₀ ⟶ Y₀) [hSmooth : SmoothOfRelativeDimension 1 h₀.left]
  [hSep : IsSeparated h₀.left] [hQC : QuasiCompact h₀.left]
  (hAffine : ∀ y : Y₀.left, IsAffine (h₀.left.fiber y))
  (c₀ : Compactification h₀.left) (E : NativeL2.WeilModule D l U₀)
  (hLisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) E.carrier)
  (iota : PadicAlgCl l →+* ℂ)

include hl hYsep hSmooth hSep hQC hAffine hLisse

/-- Reality of the alternating trace in degrees one and two on the native local fibres.
Source: latest blueprint, lem-zl-relative-envelope-factor-reality.proof.md, second paragraph;
thm-trf-l-function-euler-product and lem-zl-euler-product-identity.
(blueprint: lem-zl-native-relative-curve-alternating-trace)

Proof: after compact-support base change, the two operators are the geometric
Frobenius on the affine curve fibre over the residue field. The Grothendieck trace
formula for every positive extension degree identifies the alternating trace with
the finite sum of local traces at rational points, with their residue degrees.
The coefficient sheaf is real, hence each local characteristic factor is real;
Newton identities imply reality of every power trace. Restriction to the fibre
replaces the original local Frobenius by its appropriate residue-degree power and
preserves that reality. The affine lisse degree-zero vanishing and curve range
leave exactly trace(H_c^2)-trace(H_c^1). Each summand and hence the total is fixed
by complex conjugation. The empty fibre gives the zero sum.
-/
theorem native_relative_curve_alternating_trace
    (hReal : NativeCondensedWeil.Real D l U₀ E iota)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    [FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (NativeCondensedModule.fibre l D (higherShriek D l h₀ c₀ E 1).carrier
        (NativeCondensedModule.localClosedPoint D Y₀ y ι hι))]
    [FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (NativeCondensedModule.fibre l D (higherShriek D l h₀ c₀ E 2).carrier
        (NativeCondensedModule.localClosedPoint D Y₀ y ι hι))]
    (m : ℕ) (hm : m ≠ 0) :
    (starRingEnd ℂ) (iota (ULift.down
      (LinearMap.trace (ULift.{u + 1} (PadicAlgCl l)) _
        ((NativeL2.closedOperator D l Y₀ (higherShriek D l h₀ c₀ E 2) y ι hι).hom ^ m) -
      LinearMap.trace (ULift.{u + 1} (PadicAlgCl l)) _
        ((NativeL2.closedOperator D l Y₀ (higherShriek D l h₀ c₀ E 1) y ι hι).hom ^ m)))) =
    iota (ULift.down
      (LinearMap.trace (ULift.{u + 1} (PadicAlgCl l)) _
        ((NativeL2.closedOperator D l Y₀ (higherShriek D l h₀ c₀ E 2) y ι hι).hom ^ m) -
      LinearMap.trace (ULift.{u + 1} (PadicAlgCl l)) _
        ((NativeL2.closedOperator D l Y₀ (higherShriek D l h₀ c₀ E 1) y ι hι).hom ^ m))) := by
  sorry

end WeilConjectures.RelativeCurve
