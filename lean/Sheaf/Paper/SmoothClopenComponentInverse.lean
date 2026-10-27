/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.FiniteClopenExceptionalRestriction
public import Sheaf.Paper.FiniteClopenDecompositionCore
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Pure-dimensional component inverses for the recorded exceptional systems

Source: blueprint smooth cohomological smoothness, first paragraph, and
section-invariant, Step 4 of finite-clopen inverse assembly.
(blueprint: lem-pur-smooth-clopen-component-inverse).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- A pure-dimensional smooth component has an inverse at integral and field
coefficients, for the actual component functors of any normalized comparison.
There is no gluing, common global system, or assertion about prescribed maps here.

Source: blueprint thm-pur-cohomological-smoothness, first paragraph; Step 4 of
lem-pur-varying-dimension-dualizing-inverse, integral and field coefficient clauses.
(blueprint: lem-pur-smooth-clopen-component-inverse).

Proof: Xi is Noetherian and the coefficient prime is invertible on its stalks,
because Xi is finite type over the fixed field. Compare R.base.integralI with the
normalized integral exceptional functor for c.precomp j.left by the unique
counit-preserving comparison of right adjoints: both are right adjoint to the
same specified integral compact-support functor. Its value on the unit is
therefore isomorphic to the normalized integral dualizing object. Use that
object's actual strict reduction system and canonical derived-limit realization,
not an arbitrary tower with the same limit. Its finite reductions are the finite
exceptional images of the reduced unit. At residue level smooth tensor duality
in pure relative dimension d identifies this image with the intrinsic comparison
image of an etale line shifted by 2d; the finite exceptional adjunction comparison
fixes that identification. Carry it back through the reduction of the integral
right-adjoint comparison. The construction works without a trivialization of the line.
Apply completeResidueLineInverse to this complete integral object with m = 2d.
It supplies its internal-Hom dual, both completed-tensor evaluation isomorphisms,
and uniform Tor intervals [-2d,-2d] and [2d,2d]. The original object and its dual
are constructible and complete, so the evaluations lift through the fully faithful
integral constructible inclusion. The tensor and unit are exactly the completed
operations used by clopenIntegralTensor and clopenIntegralUnit. This proves the
first assertion, including the finite-Tor membership of both objects.
Apply the rational localization functor to the same pair. Its tensor comparison
is defined on these integral representatives and preserves both evaluations.
The rationalObjectI coherence field identifies its first factor with the actual
rationalI image of the unit, giving the second assertion. Repeat the argument at
the finite coefficient field indexed by A, using R.stage A. The stage_eqI field
identifies its rational exceptional functor with R.actionI at A. Represent the
inverse and evaluations at that same stage and use the normalized tensor and
unit comparisons of common-stage operations; identity scalar extension is
included. This proves the third assertion for every A. All statements allow the
empty component: its categories are zero and the displayed maps are unique. -/
theorem smooth_clopen_component_inverse
    (Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (R : ClopenExceptionalAllCoefficients P X Y Xi g c j)
    (d : ℕ) [SmoothOfRelativeDimension d (j.left ≫ g)] :
    (let omega := R.base.integralI.obj (P.clopenIntegralUnit Y.left)
     finiteTorConstructibleIntegral P.coefficients.l P.extension Xi.left omega.obj ∧
       ∃ Q, finiteTorConstructibleIntegral P.coefficients.l P.extension Xi.left Q.obj ∧
         Nonempty ((P.clopenIntegralTensor Xi).obj (omega, Q) ≅
           P.clopenIntegralUnit Xi.left) ∧
         Nonempty ((P.clopenIntegralTensor Xi).obj (Q, omega) ≅
           P.clopenIntegralUnit Xi.left)) ∧
    (let omega := R.base.rationalI.obj (P.clopenRationalUnit Y.left)
     ∃ Q, Nonempty ((P.clopenRationalTensor Xi).obj (omega, Q) ≅
         P.clopenRationalUnit Xi.left) ∧
       Nonempty ((P.clopenRationalTensor Xi).obj (Q, omega) ≅
         P.clopenRationalUnit Xi.left)) ∧
    (∀ A : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar,
     let omega := R.actionI.functor.obj (P.clopenCommonStageUnit Y.left A)
     ∃ Q, Nonempty ((P.clopenCommonStageTensor Xi).obj (omega, Q) ≅
         P.clopenCommonStageUnit Xi.left A) ∧
       Nonempty ((P.clopenCommonStageTensor Xi).obj (Q, omega) ≅
         P.clopenCommonStageUnit Xi.left A)) := by sorry

end WeilConjectures.PurityFiniteSetting
