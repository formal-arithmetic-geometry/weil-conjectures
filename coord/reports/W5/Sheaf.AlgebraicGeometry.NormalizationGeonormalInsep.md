## What changed

The statement of
`AlgebraicGeometry.exists_finite_purelyInseparable_geometricallyNormal_normalization`
is unchanged. Its proof now constructs the perfect closure, applies the perfect-closure
normality criterion, and identifies a descended finite model with the actual componentwise
normalization. It enumerates the reduced components by `Fin n`, checks their closed images
are distinct and exhaustive, reindexes their normalization coproduct, and transfers normal
stalks through the base-changed isomorphism for each extension field.

The following private helpers are proved in the assigned module:

- `reduced_closedImmersion_iso`: a reduced surjective closed immersion is the reduction of
  its target. The proof factors through the nilradical subscheme, cancels the closed
  immersion, proves surjectivity using injectivity of the reduction inclusion, and uses the
  reduced-target isomorphism criterion.
- `normal_stalks_of_iso`, `normal_stalks_of_openImmersion`, and
  `normal_stalks_of_self_baseChange`: transfer both domain and integral-closedness assertions
  through the appropriate stalk isomorphisms.
- `component_normalization_normal` and `reducedNormalization_normal`: use the source
  relative-normalization theorem over the function field and then the open coprojections.
- `reducedNormalization_finite`: component normalization is finite for finite type schemes
  over a field, and their finite coproduct is finite.
- `reducedNormalization_dense_preimage`: for each component, delete the other finitely many
  components, intersect that nonempty open with the given dense open, lift a point through
  its normalization, and use irreducibility and continuity of the coprojections.
- `finite_component_normalization_presentation`: construct the finite enumeration and the
  isomorphism of its normalization coproduct with the canonical component-indexed one,
  including its equation over the base.

Two new modules organize the argument: finite-model descent from a perfect closure,
and normalization over an open with normal reduction. The latter is now fully proved.
Each has one public named theorem, a complete source-based proof docstring and a matching
new node. Only the finite-model descent theorem remains an obligation. The original node's
proof and dependencies now describe the actual combination.
No existing public signature, definition, visibility, or public import was changed, and no
other group's held module was edited.

Validation: `lcompile.py --all` compiled all three delivery modules cleanly in import
order: finite-model statement 0.1 seconds, proved local normalization comparison 5.3 seconds,
and assigned module 6.8 seconds. There were no warnings. The required delivery dry run checks
the combined compilation, existing signatures, axioms and metadata.

## Proved and sorry left

Original holes: 1. The original theorem's `sorry` is replaced by a complete Lean proof from
one intermediate obligation, the proved local normalization theorem and existing
declarations. New holes: 1. This is a **decomposition**, not a proof with a net reduction
of holes: one upper hole closed and one strictly partial lower obligation added (net zero
among delivery declarations before import-closure pruning; the ledger measures closure
changes separately).

The assigned module and `ReducedNormalizationOverNormalReduction` both have zero explicit
`sorry`. The sole hole added is
`AlgebraicGeometry.exists_perfectClosure_finite_normal_model`, node
`lem-weil-pbc-perfect-closure-finite-normal-model`, in
`Sheaf.AlgebraicGeometry.PerfectClosureFiniteNormalModel`. What remains is the finite
intermediate-field inverse system, descent of the finite-presentation normalization model,
descent of finiteness and its dense closed-immersion open, and the Cartesian comparisons
needed to reflect surjectivity and density through purely inseparable homeomorphisms.
It asserts normality only after base change to the given perfect closure; the parent
derives normality at the finite stage and after every field extension.

The new theorem
`AlgebraicGeometry.Scheme.reducedNormalization_over_normal_reduction` is fully proved.
Its private helpers prove that components of locally Noetherian schemes with domain
stalks are open and disjoint; identify the nilradical reduction homeomorphism; show dense
opens meet every component; factor restricted components through the normal reduction
as open immersions; apply normalization over the normal locus; and compute the image
of the lifted restricted map. The public proof shows these images are distinct,
disjoint and covering, applies the coproduct isomorphism criterion, pulls back the
finite component coproduct, and verifies the resulting isomorphism's equation over U.
There is no auxiliary hole in that argument.

Existing project obligations, including normality over a perfect closure, the integrality
of reduced component schemes, and the broader reduced-normalization field-change API, are
used as stated. Their existing holes are not counted as holes added by this delivery.
Empty schemes, the empty component coproduct, components missing the chosen open, and
characteristic zero cause no additional assumptions in the proof or new statements.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Sheaf.RingTheory.IntegralClosureFiniteNormalProduct`
- `Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescent`
- `Sheaf.AlgebraicGeometry.NagataRelativeGluingValidStage`
- `Sheaf.AlgebraicGeometry.NagataFinitePresentationDescent`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `Sheaf.AlgebraicGeometry.DescendFinite`
- `Sheaf.AlgebraicGeometry.DescendClosedImmersion`
- `Sheaf.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`
- `Sheaf.AlgebraicGeometry.NagataRelativeGluingAxiomsEventually`
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange`
- `WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`

The four separate Nagata setup modules and their nodes
`def-nagata-relative-gluing-datum-descent`, `def-nagata-relative-gluing-valid-stage`,
`def-nagata-finite-presentation-descent`, and
`lemma-nagata-relative-gluing-axioms-eventually` are unnecessary on this item's route.
The already proved source declaration `Scheme.exists_isPullback_of_finitePresentation`
(attached to `lemma-nagata-finite-presentation-descends`) directly supplies the model.
`lem-weil-pbc-glue-schemes` is likewise not a separate dependency of this route. This does
not bypass a blueprint unit statement or unit proof step: it uses that step's existing
proved implementation.

The finite-normal-product theorem is not needed for the parent's normal-stalk construction;
the source `Scheme.Hom.isIntegrallyClosed_stalk_normalization` supplies it directly.
Its node and module remain transitively used by the existing broader reduced-normalization
field-change statement, so this is not a claim of global pruning of that branch.
The generic limit, finite/open/closed descent, reduced-normalization API and purely
inseparable homeomorphism inputs remain needed by the finite-model obligation; their
direct imports were moved there, not globally pruned. The proved local comparison does
not import the broader reduced-normalization field-change theorem: it uses the source
normalization-over-normal-locus theorem and explicit component arguments. The old Sheaf homeomorphism wrapper is
unnecessary; the source WeilConjectures implementation is the one used.

Removed the parent's obsolete direct `tool_uses` entries for the Nagata eventual-gluing
theorem, finite-presentation descent, the finite-normal-product theorem, and the purely
inseparable homeomorphism. The last three are either used within the new descent obligation
or remain transitively needed as described above; the parent's direct finite-normal
comparison approval is retained. No tool approval was added or reordered.

A direct import-graph comparison (project modules, following their public and proof
imports, with this sandbox as the overlay) removes the following 19 modules from this
item's import closure. Other targets may independently use them; no global deletion is
claimed. These are the complete project-module removals for this route:

| Module removed from this item's import closure | Associated node(s) |
| --- | --- |
| `Sheaf.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange` | No separate current Lean attachment |
| `Sheaf.AlgebraicGeometry.NagataAffineFpDescends` | `lemma-nagata-affine-fp-descends` |
| `Sheaf.AlgebraicGeometry.NagataAffineFpDescent` | `def-nagata-affine-fp-descent` |
| `Sheaf.AlgebraicGeometry.NagataFinitePresentationDescent` | `def-nagata-finite-presentation-descent` |
| `Sheaf.AlgebraicGeometry.NagataMorphismDescends` | `lemma-nagata-morphism-descends` |
| `Sheaf.AlgebraicGeometry.NagataMorphismDescent` | `def-nagata-morphism-descent` |
| `Sheaf.AlgebraicGeometry.NagataMorphismEqEventually` | `lemma-nagata-morphism-eq-eventually` |
| `Sheaf.AlgebraicGeometry.NagataMorphismEqualityStage` | `def-nagata-morphism-equality-stage` |
| `Sheaf.AlgebraicGeometry.NagataQCOpenDescent` | `def-nagata-qc-open-descent` |
| `Sheaf.AlgebraicGeometry.NagataQCOpenDescentSpec` | `lemma-nagata-qc-open-descends` |
| `Sheaf.AlgebraicGeometry.NagataQCOpenEqEventually` | `lemma-nagata-qc-open-eq-eventually` |
| `Sheaf.AlgebraicGeometry.NagataQCOpenEqualityStage` | `def-nagata-qc-open-equality-stage` |
| `Sheaf.AlgebraicGeometry.NagataRelativeGluingAxiomsEventually` | `lemma-nagata-relative-gluing-axioms-eventually` |
| `Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescends` | `lemma-nagata-relative-gluing-datum-descends` |
| `Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescent` | `def-nagata-relative-gluing-datum-descent` |
| `Sheaf.AlgebraicGeometry.NagataRelativeGluingValidStage` | `def-nagata-relative-gluing-valid-stage` |
| `Sheaf.AlgebraicGeometry.RelativeFiniteAffinePresentation` | `def-nagata-relative-finite-affine-presentation` |
| `Sheaf.Order.DirectedFiniteUpperBound` | `lemma-nagata-directed-finite-upper-bound`, `def-nagata-directed-finite-upper-bound` |
| `Sheaf.RingTheory.FilteredColimitFiniteData` | `lemma-nagata-filtered-colimit-finite-data` |

## Where the brief, the DAG or earlier work was wrong

The original plan expands the separate Nagata gluing data even though its stated
finite-presentation descent node already has a proved source theorem constructing the
model. The replacement route uses that theorem directly.

The reduced algebraic normalization field-change theorem assumes a reduced base. It does
not directly identify the canonical componentwise normalization of a nonreduced scheme
with normalization of its reduction. This compatibility, including its over-open equation,
is the interface of the second new node, now proved directly from the component
normalizations and finite coproducts. The parent now proves
rather than postpones the other part of that comparison, namely identifying a reduced
surjective closed immersion with the target's nilradical reduction.

No statement is disputed and no target meaning was changed. The source's ambient-open typo
was already corrected by the original node, and remains corrected here.

## New nodes

`lem-weil-pbc-perfect-closure-finite-normal-model` groups the descent part of Tag 0BXT through
the dense closed-immersion open. It introduces an arbitrary finite model with normal
perfect-closure base change, without identifying it as the finite-stage normalization and
without concluding normality over all extensions. The original theorem still needs the
normality criterion, local comparison, finite-normal global comparison, actual component
enumeration, and base-change stalk transport.

`lem-weil-pbc-reduced-normalization-over-normal-reduction` states and proves normalization
compatibility with restriction and reduction when the reduction of the chosen open is
normal. It has neither a finite-model construction nor a geometric-normality conclusion.
Its finite type, normality and empty cases were checked against the source and its
complete Lean proof includes the empty coproduct. Searches of
Mathlib, the source/project library and the imported blueprint found no declaration of this
exact compatibility statement.

There are no change records: all existing signatures and definitions are unchanged.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
