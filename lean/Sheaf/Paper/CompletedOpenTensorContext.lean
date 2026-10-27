/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompletedOpenTensorRepresentativeData

/-! # Compatible completion presentations for open extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOpenTensor
open IntegralOpenReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U V : Scheme.{t}} (j : U ⟶ V) [IsOpenImmersion j]

/-- Compatible presentations of reduction, completion and the strict open comparison.
Source: Stacks Tags 0GL1, 0E8I, 0941 and 099B; step 1 of
lem-pur-completed-open-tensor-representatives.
(blueprint: lem-pur-completed-open-tensor-context).

Proof: use CompletionUnit.canonicalModels to choose coherent reduction/limit calculi
and ordinary and derived models on U and V, with independent universes. Compare their
integral closed structures with the canonical IntegralOnSlice.duality structures by
the total-tensor representative comparison and tensor-Hom transposition. Replace
the integral closed fields by the canonical structures and conjugate their tensor,
evaluation and currying comparisons by those isomorphisms. Keep the reduction functors
and their adjunctions. The coherence equations are transported by naturality and
cancellation of these isomorphisms, giving tensorV and tensorU as equalities.

Use the scalar-normalized slice coefficient isomorphisms and the ordinary quotient
reductions to construct one set of exact open operations and their semilinear model.
Its all-input comparison is the localization of the ordinary quotient-system chain
comparison. Restrict that same map to complete inputs for completeOpen.r. Construct
completeOpen.d by applying total limit to its inverse and then the inverse actual
reduction/limit unit. integralOpenExtensionComplete and normalized reconstruction
make that unit invertible;
the comparison's unit and realization equations follow from the adjunction triangles.

For completionV/U, apply normalizedCompletionRealization to compare the published
quotient/Roos completion with reduction
followed by total limit on flat-term K-flat representatives. Both are computed by
the same quotient tower. Their strict augmentations have the recorded
coefficientIntegralScalarUnitSection components, so the comparison identifies
completionUnit with the actual reduction/limit adjunction unit. Descent from the
good-complex localization gives
completionV/U and the required unitV/U equations on every derived input.

Restriction to an open is exact and has an exact extension-by-zero left adjoint,
so it preserves the products computing the Roos total limit. The scalar-normalized
slice coefficient isomorphisms identify its termwise quotient towers. Commuting
restriction with the two Roos coordinates gives restrictionCompletion, as in
OpenRoosRestriction.restrictionDescent. Equality
of the strict augmentations gives restrictionUnit after localization. Finally, the
slice insertion/collapse pair is the actual ordinary open adjunction unit and is
invertible for the subterminal open object. Its localization gives openUnit and
openUnitHom for the very same operations. Thus the Context fields are compatible
presentations of fixed maps, rather than independently chosen comparison witnesses.
Empty and identity opens use the same constructions. This step constructs no ordinary
tensor comparison and asserts none of its representative squares. -/
theorem completedOpenTensorContext [QuasiCompact j]
    (hlV : IsUnit (l : Γ(V, ⊤))) (hlU : IsUnit (l : Γ(U, ⊤))) :
    Nonempty (Context l E j) := by sorry

end WeilConjectures.CompletedOpenTensor
