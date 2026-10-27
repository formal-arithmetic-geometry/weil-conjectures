/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

/-! # Integral scalar-mate steps for native compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)


include D hl

/-- Invertibility of the single completed-to-native compact-support scalar mate.
Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 5.3(1);
Stacks Tag 0GL1; steps 3 and 5--7 of the native finite comparison plan.
(blueprint: lem-sf-native-compact-support-scalar-mate-invertible).

Proof: open extension of K is complete and constructible, by the normalized open
reduction comparison and the common finite-level constructibility interval. The
stratified-perfect characterization makes it bounded below, and residue Tor gives
uniform Tor bounds. Integral compactification-system realization and completed
direct-image limits identify its recorded proper image with the actual one.
Factor the coefficient inclusion as completed integral to finite rational to native.
Localized direct-image comparison is invertible on this bounded-below object because
the proper map is qcqs. The bounded-push theorem for the finite field inclusion into
the algebraic closure makes the second proper comparison invertible. Identify the
native coefficient sheaf with the pulled-back locally finite coefficient ring by the
finite-field sheaf colimit. The normalized coefficient maps identify these comparisons
with the specified counit mates. Flat tensor associativity and pasted-mates counit
normalization identify their composite with the single proper scalar mate.
The open scalar mate is the K-flat tensor isomorphism b tensor j_!m sent to
j_!(b restricted tensor m). Its proper image is invertible. Paste this open comparison
with the proper scalar mate to obtain precisely PurCompactSupport.comparison.
Thus its component at K is invertible. The argument uses no absolute separatedness. -/
theorem native_compact_support_scalar_mate_invertible [G : NativeGeometry.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    IsIso ((PurCompactSupport.comparison a c).app K.obj) := by sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
