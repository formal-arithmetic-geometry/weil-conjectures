## What changed

Replaced the proof hole of
`AlgebraicGeometry.Scheme.sfbImmersion_sliceComparisons` with an explicit reduction
from ordinary module comparisons. Its signature and its two public imports are
unchanged.

The proof constructs the derived slice equivalence from an additive module
equivalence. It identifies the double localization representative in
`SfbCompletionNormalization.object` with the derived exact normalization functor,
uses invertibility of the completed inverse-image coefficient map to compute the
universal derived pullback on every complex, and composes the exact derived
functor comparisons. The second assertion follows by applying an ordinary natural
constant-module comparison termwise, localizing, restricting, and composing with
the first assertion. The same equivalence is used for both assertions.

Added `AdicImmersionModuleNormalization` and
`AdicImmersionConstantModuleComparison`. Their functors are concrete compositions
of the existing site transport, scalar restriction, scalar extension, and algebraic
inverse-image functors. Their additivity and exactness instances are proved.
No existing definition, statement, consumer, or source-library file is modified.

Validation: lcompile.py --all compiled the complete sandbox successfully: module
normalization in 11.0 s, constant-module comparison in 11.8 s, and the item module
in 17.7 s. After restoring the original public command fingerprint, the final
item module compiled again in 12.8 s without errors or warnings. The interface
comparison reports no public interface change, all three node statements match
their Lean statements, and the delivered dependency graph has no cycle through
these nodes. The earlier missing published object-file failure disappeared on
the next build snapshot.

## Proved and sorry left

Closed the single existing hole:
`AlgebraicGeometry.Scheme.sfbImmersion_sliceComparisons`
(node `lem-sfb-adic-immersion-slice-comparison`).

Added two holes, each the entire body of a public ordinary-module theorem:

- `AlgebraicGeometry.Scheme.sfbImmersion_moduleNormalization`
  (`lem-sfb-adic-immersion-module-normalization`).
- `AlgebraicGeometry.Scheme.sfbImmersion_constantModuleComparison`
  (`lem-sfb-adic-immersion-constant-module-comparison`).

This is a decomposition: one upper hole removed, two lower holes added, net
one additional hole. There are zero holes in the item module and exactly two
holes across this delivery. The upper theorem is proved from the two lower
statements and the existing declarations; this does not claim an axiom-free
proof of the mathematical comparison.

The private helper proving existence of the constant-complex isomorphism is a
proved proposition. It eliminates the ordinary comparison witness only inside
that proposition; no definition selects data from its unproved existence.

## No longer needed

No existing import, module, or node is globally pruned. The original public
imports remain. The direct proof dependencies now record the two ordinary
module statements and the exact normalization/localization results used by the
Lean proof. The old finite coefficient, site equivalence, and immersion-limit
arguments remain dependencies of the ordinary module statements rather than
being assumed as derived-category glue.

## Where the brief, the DAG or earlier work was wrong

The DAG's second and third steps treated the identification of the fixed
algebraic inverse image with the actual module inverse image, and its
compatibility with ordinary completed constants, as unstated glue. The listed
exactness and site-equivalence declarations do not themselves state those
natural module comparisons. These two steps are now explicit ordinary-module
obligations. The derived representative and composition arguments combining
them are written in Lean. No mathematical statement was disputed or weakened.

The module statements were checked on empty slices, the zero coefficient ring,
I=0, I=A, and arbitrary modules without projectivity or finiteness. The constant
comparison is before complexes; its termwise use therefore requires no
boundedness hypothesis. The blueprint unit route is unchanged.

## New nodes

`lem-sfb-adic-immersion-module-normalization` states the additive equivalence of
ordinary module sheaves on the two slices and its natural inverse-image
comparison. It contains no complex or derived category. It records the site
transport, finite-projection coefficient normalization, and module-action
identification needed before localization.

`lem-sfb-adic-immersion-constant-module-comparison` states the natural comparison
of ordinary completed constant-module functors on S. It has no slice, derived
object, or selected slice equivalence. Its proof is constant-sheaf transport
followed by the coefficient-map identity and scalar balancing. It is applied
termwise in the proved upper reduction.

The searches used LeanSearch, LeanFinder, Loogle, Mathlib source searches, project source
searches, and blueprint reference searches. They found the existing sheaf/module
equivalence and derived exact-functor APIs, but neither of these comparisons for
the fixed coefficient maps. Both nodes carry sources and complete proof plans.
The new nodes use the general native ringed-restriction equivalence
(`lem-pur-native-ringed-restriction-equivalence`), algebraic inverse-image transport
(`lem-sp-proetale-algebraic-inverse-image`), and its tensor comparison
(`lem-weil-pbc-algebraic-inverse-image-tensor-comparison`) as tools. These are
infrastructure for identifying the already specified functors; no statement of
the integral-models unit supplies those ordinary-module identifications. They
do not replace any step of that unit's route. Existing constant-ring and exact
restriction dependencies remain in use. No tool approval field was added.

The first preflight detected a circular statement dependency in the new constant
node: it cited the parent stratified-perfect theorem for its constant-model
definitions. The definitions are in `AdicStratifiedPerfectData`, so that citation
now names `def-sfb-adic-stratified-perfect-data`. The parent theorem is not used.
The additional proof instances are private and local, with their priorities
written on their declarations. The original public commands are preserved.
There is no change record because no existing statement or definition changed.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
