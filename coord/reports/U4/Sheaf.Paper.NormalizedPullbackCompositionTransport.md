## What changed

Prove `WeilConjectures.PullbackCompositionTransport.normalizedPullbackCompositionTransport`
from the ordinary composition/evaluation identity in the new module
`Sheaf.Paper.OrdinaryPullbackCompositionEvaluation` and existing derived-category
comparison APIs. Derived evaluation follows from the exact-derived square
composition theorem. All four transition clauses are naturality, with the
adjoint clauses transposed by the actual quotient adjunction. Strict-complex
representatives follow from localization factors and naturality of the given
Roos comparison. Both reduction clauses are counit naturality and cancellation;
completed naturality follows from naturality of the recursive beta maps.

Validation: the assigned module compiled in 37.0 seconds after explicit source
and target types were added to the two localization factors. The ordinary split
module also compiled independently. Delivery preflight supplies the final checks.

The original system pullback aliases are replaced by their definitionally equal
canonical names, and `ordinaryEvaluation` gives the primitive evaluation its
canonical functor type once, avoiding repeated expensive conversions.
`canonicalBetaTransformation` forms the whiskered realization followed by the
whiskered counit. Its component `canonicalBeta` is the original primitive beta
formula with its canonical system codomain, retaining the original
realization-parameter types.
The redundant identity complex-composition isomorphism is removed from
`strictComposition`; the existing identity-compositor theorem identifies its
hom with the identity, so the same termwise map is used.
The transport laws are also packaged as three unchanged predicates and their
conjunction, avoiding repeated structure-generation checks of the long equations.
The original representative fields are named as `RepresentativeForward` and
`RepresentativeBackward`, then folded in `RepresentativeLaws`. Their unfolded
formulas and hypotheses are identical; the conjunction replaces the original
two-field Prop structure and proved projections preserve its field names. Local reducibility annotations avoid
unfolding large constructions during elaboration. See
`coord/changes/U4-pullback-composition-canonical-definitions.md`. The comparison API is publicly imported because the public evaluation definition
now names it directly.
No module held
by another group and no adopted source-library module is changed.

## Proved and sorry left

Original module: one hole, in
`WeilConjectures.PullbackCompositionTransport.normalizedPullbackCompositionTransport`.
Its proof is replaced by a combination of strictly smaller facts. No literal
`sorry` remains in that module. The generic localization-factor, counit
conjugation, and conjugation-naturality lemmas are fully proved private lemmas.

One hole added, in
`WeilConjectures.PullbackCompositionTransport.ordinaryCompositionEvaluation`
(node `lem-pur-ordinary-pullback-composition-evaluation`). This is solely the
underived finite-evaluation compatibility of the adjunction-normalized
compositors, with no derived localization, Roos comparison, completed transport,
or reduction conclusion. Its docstring gives the sectionwise mate proof.

Thus this delivery is a decomposition: one upper hole closed, one strictly
smaller hole added; net zero holes closed. Existing imported theorem holes
are not changed.

## No longer needed

Removed private proof imports (three):

- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`.
- `Sheaf.Paper.NormalizedDVREffectivity`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.

The new proof does not separately use
`lem-pur-cochain-pullback-tensor-coherence`,
or
`lem-pur-normalized-operation-system-models`. The canonical whole-system
compositor already exists, and localization/naturality suffice for the remaining
clauses; no tensor/K-flat construction is needed here. Removed the obsolete
local tool-use approvals for `lem-coef-semilinear-derived-sections`,
`prop-weil-pbc-proetale-constant-exact`, and
`lem-pur-integral-operations-well-defined`; its import stays for finite-level
derived-category instances. The proof uses exactness instances
already packaged with primitive pullback, not these general theorem statements.

`lem-coef-semilinear-derived-sections` is no longer an explicit proof dependency
but remains a statement dependency/public import. The exactness and other foundational modules can still be transitively
needed by the unchanged canonical constructions. No entire module is withdrawn,
and no claim is made that the whole targets closure stops using these nodes.

## Where the brief, the DAG or earlier work was wrong

The original six-step plan asks for more representative and tensor calculations
than the Lean conclusion requires: its strict compositor is already the
termwise image of the canonical ordinary system compositor. Its Roos clauses
are consequences of localization factors and naturality of the realization.
The completed reduction clauses are purely formal consequences of the given
adjunction and beta isomorphisms. The specialized ordinary evaluated
composition identity is the remaining mathematical step and is explicitly
stated as a new node, rather than inferred from faithfulness of evaluations.

Edge cases: transition naturality includes identity quotient arrows; the
ordinary identity allows n=0, zero systems, arbitrary transitions, identity
scheme maps, and empty schemes. No normalization or coefficient invertibility
hypothesis is needed for the formal clauses. The original hypotheses and
conclusions are all retained. The unit route is unchanged.

## New nodes

`lem-pur-ordinary-pullback-composition-evaluation` records the ordinary
unit-normalized evaluation/composition square from original steps 1 and 3,
with its own module, source, proof in words, three search kinds, and unchanged
unit/chapter. The parent proof and proof dependencies are updated to the
argument actually used. The definition presentation change is recorded at
`coord/changes/U4-pullback-composition-canonical-definitions.md`.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
