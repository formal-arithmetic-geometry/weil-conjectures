/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
public import Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor

/-! # The contractible scalar realization adjunction

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

/-- Exact monoidal sections give the scalar realization adjunction with invertible unit.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2), Remark 3.2;
Stacks Project Tags 06YY and 06XN
(blueprint: lem-zl-contractible-realization-adjunction).

Proof: use the sectionwise/internal module equivalence to transport the exact,
cocontinuous evaluation in `heval` to actual internal module sections. Constant
realization followed by coefficient extension is left adjoint to these sections:
the adjunction sends a map to its value on constant generators, and its inverse
extends a linear map from sections by the coefficient action. This is the global
sections specialization of the ringed-topos module adjunction. The unit on a free
module is the identity after evaluating the coefficient ring. Coproduct preservation
and a free presentation extend its invertibility to every module, since sections
are exact and extension preserves cokernels. Derive this adjunction on flat-term
K-flat resolutions. Constant realization is exact, the fixed extension model has
its universal K-flat comparison, and exact sections compute their own right derived
functor. In each degree the preceding unit is invertible, so its localized chain
isomorphism is the derived unit. Uniqueness of derived adjunctions identifies this
with the unit for the fixed F and G. Derived tensor pullback supplies F's strong
symmetric monoidal structure. Transport the normalized monoidal sections data in
`heval` along the internal/sectionwise module equivalence and the unique localization
comparisons to obtain a monoidal structure on the fixed G. The localization sizes
need not agree: both comparisons commute with the common cochain localization, so
its universal property transports the tensor, unit, and coherence identities. -/
theorem contractible_realization_adjunction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U)
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ringSheaf J O)))]
    (heval : ContractibleDerivedSectionsTensor.{u + 1, u, 0} J (ringSheaf J O) (op U)) :
    ∃ adj : F J O U hU ⊣ G J O U,
      IsIso adj.unit ∧ strongSymmetric J O U hU ∧ Nonempty (G J O U).Monoidal := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
