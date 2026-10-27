/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow
public import Sheaf.Paper.InternalAdjunctionPairingChange

/-! # Evaluation characterization of the ordinary finite Hom transpose
Source: blueprint thm-coef-finite-hom, evaluation paragraph
(blueprint: lem-coef-finite-hom-ordinary-transpose-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The ordinary evaluation comparison satisfies the reduced evaluation equation.
Source: blueprint thm-coef-finite-hom, proof paragraphs 1--2
(blueprint: lem-coef-finite-hom-ordinary-transpose-evaluation).

Proof: identify the normalized closed tensor and evaluation with the published
ordinary derived tensor and counit. Expand `evaluationComparison` as the
ordinary left-tensor adjunct of the tensor comparison followed by scalar
extension of the counit. Naturality of the braiding transports this left
adjunct to the right-tensor closed record used by `finiteHomEtaleClosed`; the
inverse tensor comparison then cancels the displayed tensorator. The resulting
composite is exactly the reduced evaluation map. This argument is valid for
arbitrary objects and identity quotients; no invertibility of the Hom map is
used. -/
theorem finiteHom_ordinary_transpose_evaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n)
    (K M : finiteHomEtale l E X n) :
    (finiteHomEtaleClosed l E X m).tensor.map
          (Prod.mkHom (Etale.CoefficientPairingChange.evaluationComparison
            (finiteHomQuotient l E h) X K M)
            (𝟙 ((finiteHomEtaleReduction l E X h).obj K))) ≫
        (finiteHomEtaleClosed l E X m).evaluation ((finiteHomEtaleReduction l E X h).obj K)
          ((finiteHomEtaleReduction l E X h).obj M) =
      (finiteHomEtaleTensor l E X h).inv.app
          ((finiteHomEtaleInternalHom l E X n).obj (Opposite.op K, M), K) ≫
        (finiteHomEtaleReduction l E X h).map ((finiteHomEtaleClosed l E X n).evaluation K M) := by
  sorry

end WeilConjectures
