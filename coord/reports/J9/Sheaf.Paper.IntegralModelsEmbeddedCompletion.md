## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.integralModelsEmbeddedCompletion`
by a proof from the general flat ringed-ideal complete equivalence and its exact
restriction completeness iff. The proof supplies the section/small-site equivalences,
localizes the scalar restriction square, compares `smallDerivedObject` with the exact
derived functor, and transports the complete full subcategories and inclusion iso.
Small-site constructions and chosen kernel ideals are locally irreducible during
the assembly; explicit unfolding is confined to the representative comparison.
The main theorem has a local 400000-heartbeat budget for the categorical transport;
the server wall-time limit is unchanged.

A new module `Sheaf.Paper.IntegralModelsEmbeddedCoefficientKernels` isolates the
underived coefficient facts: finite type of the constant residue kernel, flatness,
the common residue quotient, and equality of the extended kernel with the completed
residue kernel. This is a strictly lower step with no derived objects or equivalences.
The new kernel module publicly imports only its coefficient definitions. Existing
public signatures and public imports are unchanged. No source-library file
is modified, and no arbitrary witness is used to define data.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.integralModelsEmbeddedCompletion`
(node `lem-sfb-embedded-integral-completion`) is reduced to the underived coefficient
lemma below. This is a decomposition: one upper hole closed, one lower hole added;
net hole reduction zero. The derived categorical assembly is complete. Both modules compiled through
`lcompile.py --all`; the final delivery reruns compilation and axiom probes.

One added hole remains:
`AlgebraicGeometry.ProEtale.integralModelsEmbeddedCoefficientKernels`
(node `lem-sfb-embedded-integral-coefficient-kernels`).
Its proof is exactly `by sorry`; its module and node contain the source and full
natural-language proof. There are no other holes in the delivery.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`
- `Sheaf.Paper.ConstantCompletionEquivalence`

The first two are used in the mathematical proof of the underived coefficient
lemma, and the second remains publicly imported by IntegralModelsStacks. The tower
comparison modules also remain in the existing import closure (including the
residue-comparison sibling and ConstantCompletionEquivalence). No claim is made
that these modules disappear from the targets' closure. Their original nodes
`det-prop-integral-criterion-constant-coefficients` and
`lem-weil-pbc-constant-completion-equivalence` are not direct proof dependencies of
the delivered derived assembly.

The assembly no longer needs
`lem-weil-pbc-flat-common-quotient-reduction-tower` or
`lem-weil-ringed-tower-pushforward-limit-comparison`: completeness preservation and
reflection follows directly from the general local scalar-restriction theorem.
Both nodes still realize steps of the fixed integral-models unit, so their direct
imports are retained as required by the unit-route rule; no withdrawal is requested. The node dependencies for the derived assembly now
record the general ringed-ideal theorem and the actual section scalar square.
The embedded/spectral comparison and integral-limit nodes remain dependencies of
the new underived lemma, not direct dependencies of the derived assembly. No module
is withdrawn or pruned from the library.

## Where the brief, the DAG or earlier work was wrong

The original proof plan used finite quotient towers and their derived inverse limits
to prove the arbitrary-complex completeness iff. The existing
`siteDerivedRestrictScalars_locallyDerivedComplete_iff` proves precisely the local
ideal-completeness statement directly, once the two kernel ideals are identified.
No mathematical statement was corrected and no unit route was changed. The general
flat ringed-ideal theorem is used as a tool from another unit, implementing precisely
the Stacks 099I step of this unit; its dependency needs the normal maintainer route
review. No tool approval was added by the worker.

Searches used LeanFinder, Loogle, LeanSearch and local ripgrep. Mathlib's indexed
results concern ordinary module completions, scheme flatness and constant sheaves;
none identifies the embedded coefficient maps. The useful general derived statements
already exist in `Sheaf.Paper.FlatRingedIdealCompleteEquivalence`.

## New nodes

`lem-sfb-embedded-integral-coefficient-kernels` states the underived flatness,
finite-type and first-kernel comparison on the actual coefficient-sized small site.
It is strictly simpler than the original theorem: it mentions only ring sheaves,
module flatness, and their ideals. The proof follows the first coefficient-comparison
step of the original node and Stacks 099L/099I. Edge cases include the empty scheme;
there is no boundedness, constructibility, or nonzero-object hypothesis. No change
record is required because existing definitions and public interfaces are unchanged.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
