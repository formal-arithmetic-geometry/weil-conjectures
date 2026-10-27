## What changed

Proved `AlgebraicGeometry.Scheme.completedConstantModuleTensor` in its existing module,
with its statement, universes and public imports unchanged. Added proof imports of
`Sheaf.Paper.ProEtaleSheafificationTensorComparison`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence`, and
`Mathlib.CategoryTheory.Monoidal.CoherenceLemmas`.

The proof first builds the sectionwise identity comparison for the actual constant
presheaf functor used by `adicLisseConstantModules`, then composes the existing module
sheafification tensor isomorphism and scalar-extension tensor isomorphism. The object
and map specifications of `completedConstantExtension` supply the equality transports.
All helpers are private and fully proved.

The specified `completedKoszulOne` is invertible: the ordinary scalar adjunction,
module sheafification Hom equivalence and regular-module/sections equivalence identify
precomposition with this map as a bijection. Its section formula identifies that
bijection on every object. For the normalization, an automorphism of the tensor unit
acts naturally on every object by conjugating its right whiskering with the left
unitor. At the unit this action is the original automorphism, by unitor coherence.
Choosing the automorphism as the desired regular component followed by the inverse
of the initial regular component normalizes the comparison. Currying gives exactly
the existing statement. This uses no nonzero-ring or nonempty-site hypothesis.

Updated the item's DAG `proof`, `proof_deps` and `proof_origin` to record this argument.
No shared interface, source-library module or other item's node is changed.

Validation: the complete module compiles cleanly through `lcompile.py` in 21.1 seconds,
with exit code 0 and no warnings. The public theorem signature was compared verbatim
with the shared source; it is unchanged. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed the one existing hole, in
`AlgebraicGeometry.Scheme.completedConstantModuleTensor`
(`lem-weil-pbc-completed-constant-module-tensor`). No holes added or split off;
no `sorry` remains in the delivered module. The proof uses existing dependency
statements as supplied by the project.

## No longer needed

No imports removed and no nodes or modules withdrawn. All five previously declared
proof dependencies remain used. The route avoids a separate local pure-generator
normalization calculation: the stated conclusion only requires existence of the
comparison, and the regular-unit equation follows instead by natural unit action.
In addition the proof explicitly uses the ordinary adjunction from
`def-weil-pbc-adic-coefficient-datum` and the scalar-extension object/map specifications
from `lem-pur-derived-change-of-rings`; these are recorded in the updated proof edges.
There are no new public lemmas or new obligations below this item.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The original plan is valid but its
last generator computation is unnecessary for the existential statement: after the
regular-unit map is proved invertible, unit-action normalization suffices. The
proper-base-change unit's statement and realized proof steps are unaffected.

Searches used `msearch.py` grep for the existing completed tensor, constant and scalar
comparison declarations, LeanFinder for normalization of a natural tensor isomorphism
by an invertible unit map, and Loogle for monoidal-category/natural-isomorphism
interfaces. The first returned no Mathlib match; LeanFinder returned unit-of-tensor
and monoidal-functor unit results, not this normalized composite; Loogle reported an
unknown `CategoryTheory.NatIso` identifier. Local `rg` located the existing sheafification
and scalar-extension isomorphisms, the constant-presheaf proof in
`SiteTensorLocalModelComparison`, and the regular-unit adjunction proof in
`WeilCompletedRealizationRegular`. The latter helpers are private and their modules
contain unrelated site/derived transport; this item includes the necessary short
proved private glue directly. No unproved statement was duplicated.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
