## What changed

Completed `AlgebraicGeometry.Scheme.ProEt.wContractible_sections_exact` in
`Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact`, preserving its statement,
all three universe parameters, and its independent coefficient-ring universe.
Abelian evaluation preserves finite limits sectionwise and carries epimorphisms to
surjections using the proved source `isWeaklyContractible_of_iso`. Forgetting module
structure preserves finite colimits by `moduleSheaves_colimits_forgetful`, so the
same surjectivity argument applies to module evaluation. Mathlib's kernels-plus-epis
criterion supplies preservation of homology, and additivity then gives finite colimits.
Added proof-only imports for the source weak-contractibility theorem, Mathlib's
abelian exactness criterion, concrete sheafification and its compatibility with
forgetting, and the abelian-group structure and epimorphism criteria.
The proof explicitly transports sheafification and its local-bijection criterion
from a small model in the full section universe.

Updated `det-pe-wc-sections-exact`'s proof, proof dependencies, and proof origin to
match the Lean argument. The geometric step remains the project's prescribed
w-contractible/projectivity argument; its already proved, universe-polymorphic
source implementation is used directly. No definitions or existing signatures changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.ProEt.wContractible_sections_exact`
(node `det-pe-wc-sections-exact`). Zero holes remain in the item; zero holes were added
and zero statements were split off. This is a proof, not a decomposition.

A fresh server compile accepts the retained completed module with no diagnostics (2.9 seconds).
A fresh explicit `#print axioms` check reports exactly `propext`, `Classical.choice`, and
`Quot.sound` (3.3 seconds). The diagnostic command is confined to a scratch file.
All Lean lines have at most 100 characters.

## No longer needed

The proof does not need `det-pe-wcb-projective`, whose declaration is in
`Sheaf.AlgebraicGeometry.ProEtale.Projective`: its second clause is restricted to set
sheaves in universe `t+1`, whereas the existing closed source theorem
`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_iso` handles arbitrary section
universes and takes local surjectivity directly. The latter is already recorded on
`lem-weil-pbc-source-affine-wcontractible-evaluation`; no duplicate node is introduced.

The proof also does not need `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`:
it never converts the underlying set-sheaf map back into an epimorphism, since the
source weak-contractibility theorem takes local surjectivity as its hypothesis.
Removed the current library's proof-only import
`Sheaf.AlgebraicGeometry.ProEtale.Projective`. The set-sheaf epi/local-surjectivity
module was not separately imported by the item. Both pruned dependencies may remain
needed elsewhere in the project. The other original proof dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The planned projectivity declaration has a narrower section universe than this item's
statement. This is an interface mismatch, not a false mathematical assertion. The
closed source weak-contractibility theorem already supplies the required geometric
step in all universes. Its disjoint-cover gluing proof includes the zero-ring/empty
spectrum case and needs no nontriviality hypothesis.

Typeclass inference for the larger section universe needs explicit small-model
transport; the source's special pro-etale sheafification instance alone is specialized
to the base universe. The ring-sheaf universe remains unrestricted throughout.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
