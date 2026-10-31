/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModels
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModelCore
import WeilConjectures.SixFunctors.RationalTensorRealization.RationalRealizationTensorComparison

/-! # Normalized finite tensor comparison for native realization

Source: BS Definition 3.4.10 and Remark 6.8.15; Stacks 07A4 and 03EL.
(blueprint: lem-sf-adic-completed-tensor-finite-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

/-- Ordinary scalar extension has a balanced normalized tensor comparison at one
finite field, before rationalization and common-stage descent.
Source: BS Definition 3.4.10 and Remark 6.8.15; Stacks 07A4 and 03EL.
(blueprint: lem-sf-adic-completed-tensor-finite-model).

Proof:
1. Apply constructibleTensorCompletion to the coefficient field E and X. Package
its ordinary tensor, K-flat comparison, quotient augmentation and descended map
as ConstructibleTensorCompletionPresentation. The pure-section normalization,
zero shifted Roos coordinate, representative square and constructible
invertibility are exactly its four clauses.
2. Apply the ordinary cochain scalar tensor comparison to coefficientMap. On each
bidegree it sends s tensor (x tensor y) to (s tensor x) tensor (1 tensor y).
The inverse multiplies the two coefficient scalars. Balancing proves these maps
inverse; distributivity over direct sums gives the total-complex isomorphism.
The tensor differential shows that it is a chain map with the recorded signs.
3. Scalar extension carries K-flat complexes to K-flat complexes: tensor an
acyclic native-coefficient test complex with the extension, use the balanced
associator to identify this with the original complex tensored with the
restricted test complex, and use exactness of restriction of scalars. This proves
kflat for every integral good complex.
4. Descend the cochain comparison on the two good-complex localizations. Compose
with the supplied native K-flat model isomorphism, using the universal scalar
counits. Their naturality gives precisely tensorFiniteRepresentative.
Both sides invert quasi-isomorphisms in each variable, so two-variable
localization supplies a natural isomorphism on the entire derived categories.
The comparison retains the cochain pure-section equation of step 2.
5. Insert this comparison, the completion presentation and the K-flat proofs into
CompletedTensorFiniteModel. No common-stage functor, tensorator or constraint
coherence is constructed in this lemma. -/
theorem completed_tensor_finite_model
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (closed : CoefficientClosedStructure (ambientHom l X R))
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    Nonempty (CompletedTensorFiniteModel l X R closed models E) := by
  classical
  let F := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  obtain ⟨completion⟩ :=
    WeilConjectures.constructibleTensorCompletionPresentation l F X
  obtain ⟨core⟩ := completed_tensor_finite_model_core l X R closed models E completion
  exact ⟨{
    completion := completion
    balance := core.balance
    balance_sections := core.balance_sections
    kflat := core.kflat
    ordinary := core.ordinary
    representative := core.representative }⟩

end WeilConjectures.AdicQbarRealization
