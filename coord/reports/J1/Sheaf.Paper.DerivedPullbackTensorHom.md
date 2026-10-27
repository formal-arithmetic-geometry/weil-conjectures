## What changed

Replaced `WeilConjectures.rationalDerivedInternalHom_existsUnique` with a complete
algebraic proof from the ambient integral Hom bilinearity prerequisite in the new
proof-only import `Sheaf.Paper.IntegralDerivedHomBilinear`.

The private construction base changes the integral bilinear Hom action in both
variables, keeps exactly the prescribed integral objects, and sends scalar-first
pure tensors to the integral Hom map multiplied by the product of the scalars.
Four tensor inductions prove composition, including the reversed first-variable
composition. The integral identity formula proves identities. Double tensor
induction and functor extensionality prove uniqueness, including the heterogeneous
object transports. The construction works directly on the permitted full
subcategory; it does not assume mixed pairs are permitted.

Every existing public signature, definition body and public import is preserved.
The restriction calculation is a proved private helper. Local irreducibility
attributes keep the restricted Hom and category/linear instances folded only
during the final construction proof; no exported attribute is changed. Updated
the item's proof route and added the prerequisite's DAG node.
The packet was rebased onto the current source after T4's global-build rollback.
The private additive helper specialization and its `import all` consumer are
recorded in `coord/changes/J1-derived-Hom-private-additive-groups.md`.
The existing rational tensor-comparison proof now applies a proved private
generic lemma for composing bilinear localized functors with semilinear scalar
extension. This generalizes the same-ring `tensorIso_localize` argument already
in `RationalRestrictionComparisonCoherence`, keeping its composition calculation
independent of concrete derived-category Hom instances.
The stage-object proof now applies an explicit private object-equation lemma
instead of rewriting a functor under a large dependent type. Scoped unfolding
controls keep the full-subcategory and localization instances abstract while
elaborating the comparison definitions. Their original terms and explicit result
types are preserved, as are the priorities of all exported instances.
The bilinear map selected
from the new theorem is determined pointwise on every pair of arrows by its
conclusion, so no arbitrary object is chosen from a mere existence assertion.

## Proved and sorry left

This delivery is a decomposition: one upper hole closed and one lower hole added;
net zero holes closed. The current source module has five holes and this packet leaves four. At
session start the source contained four; the T4 landing was rolled back during
work after a failed global build. This packet was rebased onto that rollback and
does not restore its rational-tensor proof or comparison-definition changes.

Closed:

- `WeilConjectures.rationalDerivedInternalHom_existsUnique`.

Unchanged holes in the item, node `def-weil-derived-pullback-tensor-hom`:

- `WeilConjectures.rationalDerivedTensor_existsUnique`.
- `WeilConjectures.commonStageDerivedPullback_existsUnique`.
- `WeilConjectures.commonStageDerivedTensor_existsUnique`.
- `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.

Added:

- `WeilConjectures.integralDerivedHom_bilinear`, node
  `lem-sf-integral-derived-hom-bilinear`. This states only separate bilinearity of
  the existing ambient integral arrow action. It does not assert a rational
  functor, rational functoriality, uniqueness, constructible preservation, or
  common-stage descent. Its docstring supplies the Hom-complex calculation and
  descent through K-injective representatives.

The new statement was checked on zero arrows and zero objects: the Hom action is
zero in either zero arrow. Arbitrary torsion objects and unbounded complexes are
allowed; no scalar is cancelled and no flatness is assumed. Reversing the first
arrow gives the specified source and target, and composition reverses only that
arrow. Restriction to permitted endpoints uses full-subcategory Hom linear
isomorphisms, so no assertion on a mixed pair is required.

Validation: `lcompile.py` compiled the item cleanly in 57.4 s, with no warnings
or errors. The new prerequisite compiled cleanly in 33.2 s during the earlier
preflight. The unchanged `import all` consumer
`Sheaf.Paper.RationalRestrictionComparisonCoherence` compiled cleanly against the
revised item in 42.0 s. Its validation copy was then removed from the sandbox;
no consumer adaptation or withdrawal is included. The required delivery preflight
runs all packet checks again. All 51 original public declaration headers are textually unchanged,
all new Lean lines have at most 100 characters, the node proof dependency lists equal
the union of their step uses, and the new node has no dependency path back to its
parent. No profiling options remain in the delivery source.

## No longer needed

No existing import, node or module is pruned. The existing public imports and the pullback proof route remain. The rolled-back
T4 rational-tensor proof and its extra private imports/helpers are not restored. The stage-comparison
interface is still used by the unchanged normalized common-stage definitions.
The new proof-only import supplies the integral bilinearity premise which none
of the existing declared dependencies states. No declaration of the adopted
`WeilConjectures` source tree is removed or altered.

## Where the brief, the DAG or earlier work was wrong

The item's proof record described rational internal Hom as unfinished. The algebraic extension is now proved;
its missing ambient bilinearity prerequisite is stated separately rather than
leaving an anonymous hole inside the construction.

The current blueprint file under `literature/blueprint/latest/blueprint/`
`sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/`
`def-weil-derived-pullback-tensor-hom.md` defines all coefficient operations through
pulled-back condensed coefficients, whereas the assigned Lean module and its
recorded statements use integral completion, rationalization and common stages.
This pre-existing framework mismatch is also recorded by the node's
`blueprint_update`. This delivery proves the existing assigned rationalization
statement unchanged; it does not claim to implement the newer coefficient
framework or rewrite targets and their definitions.

## New nodes

`lem-sf-integral-derived-hom-bilinear`, at
`dag/nodes/sec-smooth-purity/lem-sf-integral-derived-hom-bilinear.json`, records
constant-scalar bilinearity of the existing ambient integral Hom action. Source:
Stacks Project `sites-cohomology.tex`, Section 08J7 and Lemma 0A95, with the
constant-scalar calculation written out. Its Lean declaration is
`WeilConjectures.integralDerivedHom_bilinear` in
`lean/Sheaf/Paper/IntegralDerivedHomBilinear.lean`. Mathlib searches and the search
for duplicate blueprint statements are recorded. The private-helper change record is
`coord/changes/J1-derived-Hom-private-additive-groups.md`.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
