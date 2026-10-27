## What changed

Marked `WeilConjectures.completedPullbackTensor_associativity_representatives`
STATEMENT-DISPUTED at its declaration. Its full signature, original docstring, imports,
and single named theorem hole are preserved. No target, definition, or dependency is changed.

The dispute concerns the canonical interpretation and the proposed proof, rather than
an established counterexample in the actual coefficient-sequence category. The node's
last step identifies the derived associators with the localized ordinary reassociation
maps. That identification is absent from the supplied data. It must be justified or
made part of a repaired choice before the planned proof is valid.

## Proved and sorry left

Closed: 0 of 1 holes. Added: 0 holes. Split off: 0.

The one remaining hole is
`WeilConjectures.completedPullbackTensor_associativity_representatives`, node
`lem-pur-completed-pullback-tensor-associativity-representatives`.
No proof is claimed. In particular, I did not move this obligation to a theorem under
a different name or assume the missing normalization as a new theorem.

## No longer needed

None. No import, module, node, or unit step is pruned. Both declared dependencies
remain relevant to a repaired proof.

## Where the brief, the DAG or earlier work was wrong

The second proof step assumes that the recorded K-flat models identify the two
specified derived associators with the ordinary total-complex associators. Inspecting
all relevant declarations shows that this has not been specified:

* `CoefficientClosedStructure` has `monoidal`, `adjunction`, and
  `evaluation_naturality`. Its adjunctions refer to right tensoring, not to the
  monoidal associator.
* `CoefficientTensorModels` has just `comparison` and `uncurry_model`.
  `CoefficientTensorUncurryModel` fixes the adjunction transpose and its pure-tensor
  evaluation formula. It has no associator equation.
* `CoefficientDerivedSystemTensors.systemClosed` and `.systemTensorModel` contain
  exactly those data. The subsequent calculus fields do not add the total-complex
  associator normalization. The reduction/finite internal-composition compatibility
  fields compare the chosen structures with one another; they do not identify their
  associators with ordinary reassociation, or compare different schemes' choices.
* `pullbackTensorCalculus` is the unrestricted first witness chosen from
  `coefficientDerivedSystemEvaluationCalculus`. Its definition retains neither a native
  monoidal identification nor `RingedDerivedTensorCoherence`.
* `pullbackTensorSystemComparison_existsUnique` fixes the four binary comparison
  squares, not associativity of the chosen monoidal structures.

There is an existing, precise API for the missing fact:
`CategoryTheory.RingedDerivedTensorCoherence.associator_model`, together with
`tensorIso_both`. `ringedDerived_closed_symmetric_monoidal` constructs some closed
structure and tensor model carrying that API. Its existential witnesses cannot be
substituted for `(pullbackTensorCalculus l E W).systemClosed` and `.systemTensorModel`:
no equality or compatibility between these choices is provided. The nearby
`ringed_forget_tensor_associator_representatives` explicitly assumes this coherence on
both sides, as well as hypotheses unsuitable for the present arbitrary K-flat inputs.

The inference from binary tensor/evaluation normalization to associator normalization
is false for general closed monoidal models. For example, in graded rational vector
spaces keep the usual tensor bifunctor, internal Hom, and tensor-Hom adjunction, and
transport the monoidal constraints through the identity functor with tensorator scalar
`theta(a,b) = -1` when `a` is odd and `b = 0`, and `1` otherwise, on homogeneous
degrees. This is an invertible natural tensorator. Transport gives valid monoidal
constraints; the associator changes by its coboundary, which is `-1` in degrees
`(1,0,1)`. The binary tensor bifunctor and adjunction remain unchanged. Thus the
uncurry normalization alone cannot be the asserted justification. This example is a
counterexample to that general inference, not a claimed realization of the full
coefficient-system calculus.

Precisely, writing `T` for the total tensor, `t` for the selected derived tensor,
and `r(A,B)` for `pullbackTensorSystemModel`, the missing local equation on each
scheme is

```
r(T(A,B),C) >> t.map(r(A,B),1) >> alpha(Q(A),Q(B),Q(C))
  = Q.map(ordinaryAssociator(A,B,C)) >> r(A,T(B,C)) >> t.map(1,r(B,C)).
```

The intermediate total tensors are K-flat by the already proved
`coefficientTotalTensor_isKFlat`, so their model maps exist. The issue is their
compatibility with `alpha`, not existence or K-flatness of those models. The
four binary pullback normalizations do not contain either side's `alpha`.

A repair should retain native representative constraint coherence when choosing the
system calculus, and verify all consumers of the repaired choice. It should then use
the four existing comparison normalization squares, ordinary cochain associativity,
and the two associator model equations to prove the assigned equation. Adding K-flat
or flat-term hypotheses, replacing the conclusion by canonical associators without
updating its consumers, or asserting coherence of an arbitrary chosen model would not
repair the current statement.

Current claim records name C2 as holder of
`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` and J4 as holder of
`Sheaf.Paper.CompletedPullbackTowerCore`. The worker brief permits edits to another
holder's module only as forced compiler adaptations of an interface change. This is
an upstream mathematical normalization repair, not such an adaptation. Consequently
neither held module was edited.

Searches used the required leanfinder, loogle, and grep modes of msearch.py, and direct
searches of Sheaf, WeilConjectures, and Mathlib. They located total-complex associators,
the explicit ringed coherence API, and monoidal-functor associativity laws; none
supplies the missing identification of the chosen calculus. Sources checked locally:
Stacks sites-cohomology.tex, lemma-pullback-tensor-product (07A4), and
lemma-tensor-product-K-flat (07A2). The unit record sk-def-purity-conv has no realized
statement or proof steps, and this delivery changes no unit route.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
