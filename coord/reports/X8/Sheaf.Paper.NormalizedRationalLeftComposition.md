## What changed

Filled `normalized_rational_left_composition` in
`Sheaf.Paper.NormalizedRationalLeftComposition` with a proof from the normalized integral
ring cocycle. The proof constructs the unchanged integral finite-Tor representative,
identifies scalar localization on objects and arrows, transports the three q components
and the two associator components, and applies rationalization to the integral equation.
All heterogeneous endpoint equalities are explicitly justified. The existing theorem
signature and public import are unchanged.

Added the scalar-only module `Sheaf.Paper.NormalizedScalarAssociatorLocalization`.
Its statement isolates identification of a supplied normalized completed scalar
associator with the intrinsic rational scalar associator. It quantifies over three
scalar functors on one scheme and contains no compact-support operations, q comparisons,
finite-field datum, or desired cocycle. Its remaining argument is the comparison between
the two ordinary/completed scalar implementations, followed by uniqueness of the
intrinsic associator and raw localization.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.normalized_rational_left_composition`
(node `lem-sf-normalized-rational-left-composition`). Its proof combines the existing
integral cocycle, the existing residue-Tor criterion, scalar localization, the given
rational normalization, and the new scalar-only identification.

Added one hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.normalized_scalar_associator_localization`
(node `lem-sf-normalized-scalar-associator-localization`). This is the whole proof of the
single public theorem in its new module. There are no other holes in the delivered
modules, and no data is chosen from an existence theorem with an unfinished proof.
This delivery is a decomposition: one upper hole closed, one strictly smaller scalar
identification added, net zero holes. The integral cocycle and the entire localization
transport are implemented in Lean.

## No longer needed

No original import was removed: the sole public data import is required by the signature.
The proof does not import `Sheaf.Paper.RationalLeftCoefficientLocalization`
(node `lem-sf-rational-left-coefficient-localization`). Its finite-sum arrow hypothesis
is stronger than the `localizedAction` supplied here, and it is stated on the intrinsic
integral category rather than the finite-Tor domain. The proof directly implements its
singleton-arrow transport argument on the supplied finite-Tor functors instead.

The finite-free completed scalar comparison remains needed below the new scalar-only
node; it is no longer a direct proof dependency of the item. The normalized ring cocycle,
residue-Tor criterion, and scalar-extension composition declarations remain needed.
No existing module is withdrawn, and no source-library declaration is removed.
This is dependency pruning within the proof, not a claim that the localization module
has become globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned localization application is not immediate: its existing declaration asks
for a finite-sum normalization which the construction data does not supply. Only its
singleton case is actually necessary. The construction's integral functors also have
the finite-Tor domain, whereas the localization theorem uses all intrinsic integral
constructible objects. The residue-Tor criterion supplies the unchanged representatives.

The supplied normalized scalar associators must be identified with the specific
`sfRationalScalarComp`, rather than merely with some coherent associator. This is the
strictly smaller scalar calculation isolated in the new node. No statement was weakened
and the unit route is unchanged. The quarantined source was preserved.

The first preflight found that citing the entire exceptional-adjunction existence
theorem as a statement dependency of the scalar-only node introduced a cycle through
its coherence proof. The new statement defines its scalar hypotheses explicitly and
now cites the foundational field, finite-Tor, scalar-extension, and raw-localization
definition nodes it actually needs, rather than that unrelated existence theorem.

## New nodes

`lem-sf-normalized-scalar-associator-localization` states the scalar-only comparison
above. Its source is the exceptional coefficient normalization paragraph and the
ordinary/completed scalar constructions used there. Its docstring and node give the
K-flat comparison, quotient-coordinate normalization, associator uniqueness, and forward
localization argument. Searches used Lean Finder, Loogle, and ripgrep of Mathlib and
both project roots. `CompletedLineTensor.canonical_restriction` identifies the fixed
completed and intrinsic associators; the supplied finite-Tor associator still needs the
ordinary-model comparison in the new node. No existing declaration states this entire
identification. The node has
the same chapter and unit as the item. Identity embeddings, repeated fields, and the
zero object require no excluded case: the proof only transports equalities forward
and never assumes rationalization faithful. No existing interface or definition changed,
so no change record or consumer adaptation is needed. The command-diff advisory comes
from section-local attributes, universes, and options for private proof helpers; these
do not change any existing public declaration or importer-visible attribute.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
