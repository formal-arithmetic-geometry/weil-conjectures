/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.PbcQbarCategory

/-!
# Trace functions of common-stage Weil complexes

Source: Weil blueprint, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md;
the local operators of def-weil-local-frobenius-trace
(blueprint: def-fd-trace-function).

The trace is the unique scalar whose value on every finite coefficient model is the
already defined alternating local Frobenius trace, included in the coefficient closure.
This retains arbitrary Weil complexes in the common-stage category, rather than requiring
their Weil structure to be defined at their underlying object's displayed stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The local alternating trace descends to a uniquely determined scalar in Qbar.
Source: blueprint def-fd-trace-function, together with its two definition dependencies
(blueprint: def-fd-trace-function).

Proof: represent the underlying object by its finite coefficient stage. The Weil
isomorphism and its inverse are common-stage morphisms, so both descend to a finite
overfield. Their two inverse identities hold at a further common finite stage. The
specified scalar comparisons with Frobenius pullback then give a finite-stage Weil
complex and an isomorphism from its inclusion to K. Compute the local operator using
the iterated Weil structure, the specified pullback-composition comparisons, and the
point transports of def-weil-local-frobenius-trace. These constructions commute with
finite scalar extension. Two finite-stage Weil models become isomorphic over a common
finite overfield. Their local operators are conjugate, so ordinary linear trace agrees
in each degree after scalar extension. Boundedness leaves finitely many nonzero degrees;
therefore the signed sum agrees too. This proves independence of model and existence.
One finite-stage model fixes the scalar, proving uniqueness. Negative degrees use
Int.negOnePow, and n is positive as in the finite-field-point convention. -/
theorem weilTraceFunction_existsUnique [IsSeparated X₀.hom]
    (K : sfCommonStageWeilComplex D l hl X₀ Qbar)
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn) :
    ∃! t : Qbar,
      ∀ (E : AlgebraicallyClosedCoefficients.Index l Qbar)
        (V : sfWeilComplex D l hl X₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E)),
        Nonempty (sfWeilStageObject D l hl X₀ Qbar E V ≅ K) →
          t = E.val.subtype
            (Shrink.algEquiv (Padic l) E.val
              (localExtensionTrace l
                (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E)
                D hl X₀ V n hn x)) := by
  sorry

/-- The function t_K(x) = Tr(F_x^(n) | K_xbar), namely the finite alternating sum
of ordinary traces on the cohomology stalks, computed at any finite coefficient model
and included in Qbar. The preceding uniqueness specification fixes its value exactly.
Source: blueprint sec-fourier-transform/sk-def-trace/def-fd-trace-function.md
(blueprint: def-fd-trace-function). -/
def weilTraceFunction [IsSeparated X₀.hom] (K : sfCommonStageWeilComplex D l hl X₀ Qbar)
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn) : Qbar :=
  (weilTraceFunction_existsUnique D l hl Qbar X₀ K n hn x).exists.choose

end WeilConjectures
