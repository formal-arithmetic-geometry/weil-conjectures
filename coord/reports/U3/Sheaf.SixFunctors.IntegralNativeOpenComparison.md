## What changed

Filled `WeilConjectures.IntegralSystemRealization.integralNativeOpenComparison`, preserving
its statement and the construction of `integralNativeOpenIso`.

The proof identifies the ordinary direct evaluation square by its identity on sections,
then compares its pullback mates using a proved private categorical lemma. Exact
localization and the existing full cochain normalization give the derived pullback
square. The finite native open coordinate comparison preserves the localized unit.
A second application of the mate comparison proves the required open square from
`OpenEvaluation.transpose` and the definition of native `evalJ`.

Added two fully proved helper modules, with one public theorem each:

- `IntegralNativeOrdinaryPullEvaluation`: the ordinary pullback square, from normalized
  direct-image sections and adjunction units.
- `IntegralNativePullEvaluation`: the derived pullback square, by exact localization.

An unsplit version exceeded 60 seconds. Profiling isolated the concrete coefficient
presentation conversions. Local irreducibility of the large constructions, explicit
exactness structures, named-wrapper normalization, and explicit evaluation functors
avoid unnecessary unfolding, but the combined file still took 77 seconds. The proved
ordinary and derived steps were therefore put in separate modules. This adds no proof
obligations or holes.

All additional imports are proof-only. The ordinary helper imports
`IntegralDirectEvaluationMateInvertible` with `import all` to reuse its proved private
normalization helpers, and `CompactSupportOrdinaryDirectEvaluationSections` for the
section identity. The derived helper uses the same private cochain normalization and
the public derived-whiskering lemmas. The item imports the derived helper,
`ExactClopenNormalization` with `import all` for its proved `exact_adjunction_eq`, and
`ExactLocalizationInverseMate` for the exact-localization construction. The unit
transport formula is proved privately in the item from the localization unit formula.
The generic mate comparison is private and proved in both modules that use it.

Updated the item's proof, dependencies, and origin; added nodes for the two proved
helpers. No other existing module or node was changed.

Validation: all three modules compiled on the project server in import order with
`lcompile.py --all`. The only reported warnings were temporary profiling options and
a long line; those have been removed or fixed. The theorem signature and comparison
definition match the original source verbatim, and the overlaid DAG has no dependency
cycle. The final delivery command runs the clean compile and preflight checks.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralNativeOpenComparison`
(node `lem-sf-integral-native-open-comparison`): 1 of 1 original holes.

Also fully proved
`WeilConjectures.IntegralSystemRealization.integralNativeOrdinaryPullEvaluation` and
`WeilConjectures.IntegralSystemRealization.integralNativePullEvaluation`.
No `sorry` remains in any delivered module. No holes or split-off unproved statements
were added. This is a proof from existing declared dependencies, not a decomposition
into new obligations.

## No longer needed

No original imports were removed, and no modules or nodes are withdrawn.
The theorem `integralNativeDirectComparison` is not used: the proof uses the ordinary
direct-image isomorphism and its localized pullback comparison from that same module.
Thus `lem-sf-integral-native-direct-comparison` remains needed for those definitions;
it cannot be pruned as a node or module. Every original stated dependency remains used,
either in the item or in its two proved helpers.
The proof requires no properness, boundedness, reconstruction of a tower, or faithfulness
of finite derived evaluation.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The node's original normalized-mate argument works
for arbitrary derived systems, including the empty and identity opens and zero input.
Its previously informal exact-localization and finite-coordinate unit steps are now
explicit Lean proofs. The unit route is preserved. No existing public interface or
shared file was changed.

## New nodes

`lem-sf-integral-native-ordinary-pull-evaluation` records the proved ordinary comparison
of the specified inverse-image evaluation square. Its statement uses only public
comparisons, and its proof identifies the two normalized direct-image squares before
taking mates. It holds for all scheme morphisms, including identity maps and zero inputs.

`lem-sf-integral-native-pull-evaluation` records the proved exact localization of that
ordinary square, with the full prescribed cochain normalization. It applies to all
unbounded systems and is a genuine inverse-image step of the open-comparison argument.
Neither new node has a `sorry`. No change record is needed because no existing statement,
definition, or public import was changed.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
