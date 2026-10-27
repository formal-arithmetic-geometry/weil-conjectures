## What changed

Replaced the body of `WeilConjectures.compactSupportNativeSystemTransition` by the
pasting argument, with its statement, universes, hypotheses and original public
imports unchanged. The proof expands the specified compact-support evaluation into
its open and direct-image factors, applies the direct-image transition square to
`J.obj M`, moves the open evaluation through `sfDerivedImageRestriction` by
naturality, and applies direct image to the open transition square. Functoriality
and associativity identify the result with the definition of
`sfCompactSupportRestriction`.

Added two proof imports and two modules:

- `Sheaf.Paper.CompactSupportNativeOpenTransition` extracts the already specified
  open factor as `compactSupportNativeOpenEvaluation` and states its horizontal
  coefficient square.
- `Sheaf.Paper.CompactSupportNativeDirectTransition` extracts the already specified
  direct-image factor as `compactSupportNativeDirectEvaluation` and states its
  horizontal coefficient square.

Both evaluation definitions are the original factors, constructed from the same
native evaluations and model isomorphisms. Neither chooses new data. The proof
checks their composition against `compactSupportSystemEvaluation` itself. The new
statements separate original proof steps 1 and 2; the complete Lean argument in the
item performs original step 3. No existing module besides the item was changed.

## Proved and sorry left

This is a decomposition, not a completed geometric proof. The one original hole,
`WeilConjectures.compactSupportNativeSystemTransition`, is closed by a complete
pasting proof from two strictly simpler, single-operation statements. There are no
sorries left in the item module. Two holes are added:

- `WeilConjectures.compactSupportNativeOpenTransition`, node
  `lem-weil-compact-support-native-open-transition`.
- `WeilConjectures.compactSupportNativeDirectTransition`, node
  `lem-weil-compact-support-native-direct-transition`.

Thus the packet closes one hole and adds two (net -1); zero of the geometric
obligations are claimed as proved without these new statements. Each new theorem
has exactly `:= by sorry`, its own module and node, sources and a full proof plan.
Both evaluation definitions have complete bodies and no postponed data or proofs.

The edge cases were checked mathematically: n=0 means the positive ring A_1;
m=n uses identity quotient restriction; j=id and the empty open use the same open
unit normalization; g=id gives the direct-image unit normalization; zero systems
give zero maps. Noncartesian systems are included. No flatness, boundedness,
properness of g or preservation of K-injectives by evaluation/restriction was
introduced. Direct image requires its published resolution-normalized comparison,
not an assertion that quotient restriction preserves K-injectives.

Remote compilation passed for the direct module (34.2 s), open module (30.2 s),
and final item module (18.6 s), all under 60 s. The original theorem statement was
also compared byte-for-byte with the repository version. Delivery preflight performs
the declaration/axiom checks and records their results.

## No longer needed

No original import was removed and no module is claimed pruned. The two new imports
are private proof imports, and each is used by the pasting argument.

The item's former direct proof dependencies
`def-sp-varying-ring-operations`, `lem-weil-compact-support-coefficient-transition`,
`lem-trf-open-square-exchange`,
`lem-pur-system-pushforward-restriction-transition` and
`lem-weil-proetale-direct-image-restriction-of-scalars` are no longer individual
assembly steps. The first two remain needed for the definitions and the new
single-operation statements; the pushforward transition and direct-image
restriction calculations remain needed by the new direct-image statement. The
open-square exchange remains needed through the unchanged open-model definition
and its normalization; it is not globally pruned or withdrawn. The new open proof
plan additionally names the existing
`lem-sf-open-extension-scalar-restriction-coherence`, whose unit-normalized
uniqueness statement is closer to the required coefficient square than geometric
base change. The item's proof dependencies now record precisely the two
single-operation squares, the original evaluation construction and the specified
compact-support restriction comparison.

## Where the brief, the DAG or earlier work was wrong

No false statement or assigned-definition defect was found. The original DAG plan
has the right three parts. It left the identification of native evaluations with
the published coefficient comparisons inside its first two steps. These are
substantial identifications: `SystemPushforwardRestrictionTransition` is stated for
`SemilinearSections.Geometry` and its pulled-back coefficient systems, whereas the
item uses native varying constant-ring sequence modules and `evalPMate`.
`SequenceSiteOpenExtension` similarly constructs an open calculus on the localized
site, rather than asserting the equation for the particular `evalJ` and
`compactSupportOpenModel` in this item. Neither is a direct type-correct application
that proves the native square. The new lemmas retain the necessary identification
and normalization work, rather than changing the named comparisons or assuming
extra exactness of K-injective evaluation.

Sources read include Stacks `sites-modules.tex`, `lemma-extension-by-zero` (03DI),
and `sites-cohomology.tex`, `lemma-derived-pushforward-composition` (0D6E) and its
base-change discussion. The recorded historical representative-independence proof
is absent at its old path in the latest blueprint; this was not treated as a
withdrawal. The current unit record has no realized step bypassed by this split.
Project and Mathlib searches found no native single-operation transition theorem.
A source-only dependency check also found an existing DAG cycle through this item,
compact-support tower data, intrinsic compact support, derived direct image,
`lem-sf-integral-pullback-linear-adjunction`, system-operation exchange realization
and the compact-support reduction tower. The two new factors inherit that existing
component; no Lean import cycle is introduced and no unrelated metadata was edited.

## New nodes

`lem-weil-compact-support-native-open-transition` records the open-extension
coefficient square with arbitrary derived systems and the exact unit-normalized
open comparison. It has no proper/direct-image operation and requires no
compactification. Its proof plan is ordinary adjunction transposition, comparison
normalization, and exact localization. The extracted evaluation definition is
recorded in the same node's Lean declarations.

`lem-weil-compact-support-native-direct-transition` records the direct-image
coefficient square with arbitrary derived systems and the prescribed K-injective
normalization. It has no open extension or compactification. Its proof plan uses
the existing system restriction-transition theorem, native mate normalization and
comparison on restricted K-injective representatives. The extracted evaluation
definition is recorded in the same node's Lean declarations.

Both nodes carry the ancestor of the original item, actual LeanSearch, LeanFinder,
Loogle and grep queries, and explicit module/declaration attachments. Blueprint
searches for open evaluation, direct-image evaluation and compact-support
coefficient transitions found no matching imported blueprint node. No change record
is needed: no existing public signature, definition, attribute or import was changed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
