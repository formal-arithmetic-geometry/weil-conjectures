## What changed

Proved `AlgebraicGeometry.exists_dense_open_isIso_component_modifications_of_pos`
with its signature unchanged in
`Sheaf.AlgebraicGeometry.DenseOpenComponentModificationsNonempty`.
The proof chooses the prescribed component dense opens, applies the geometric
component coproduct construction, restricts each modification isomorphism further
using `morphismRestrictRestrict`, and applies the proved coproduct transfer theorem.
The two added imports are proof-only imports.

Added `Sheaf.AlgebraicGeometry.SigmaDescRestrictIsIso`, with a complete proof of
`AlgebraicGeometry.isIso_sigmaDesc_comp_restrict` using Mathlib only. Its private
comparison inclusions have real definitions and its private comparison-isomorphism
lemma is proved. Universal finite coproducts of schemes identify the two restricted
sources with coproducts of component inverse images. A coproduct of isomorphisms,
followed by the given component coproduct isomorphism, gives the conclusion.

Added `Sheaf.AlgebraicGeometry.DenseOpenComponentCoproduct` for the remaining
geometric construction, independently of any modifications Y or ν. This is
strictly the component-separation part of the original argument, not a restatement
of the item: it constructs the component coproduct isomorphism and controls the
inverse images of prescribed dense opens. All transfer through the modifications
and all shrinking of their given isomorphisms are proved in Lean.

Compiled all three modules in import order with `lcompile.py --all`, without
warnings or errors. The new geometric statement was checked on n=0 (the cover
forces X empty), n=1 (a surjective closed immersion into a reduced scheme is an
isomorphism), intersecting components (their intersections are removed), and
arbitrary, possibly nonfinite modifications (no such assumptions are used).
The Stacks text for Tags 0BAJ and 0A3Q was read on the Stacks website because the
local literature source is absent. The new geometric docstring expands the
component construction in the existing parent node, not the stronger hypotheses
of the full birational theorem in 0BAJ.

## Proved and sorry left

Proved the item's only previous sorry:
`AlgebraicGeometry.exists_dense_open_isIso_component_modifications_of_pos`
(node `lem-weil-pbc-dense-open-component-modifications-nonempty`).
This proof still depends on the following single geometric sorry.

Proved from Mathlib only:
`AlgebraicGeometry.isIso_sigmaDesc_comp_restrict`
(node `lem-weil-pbc-sigma-desc-restrict-iso`), and its two private helpers.

The only sorry in the delivery is
`AlgebraicGeometry.exists_dense_open_component_coproduct`
(node `lem-weil-pbc-dense-open-component-coproduct`), in its own new module.
Its whole proof is `:= by sorry`, with a complete natural-language proof and source
in the docstring and matching DAG proof steps. No sorry remains in the item,
in private declarations, or in any definition.

## No longer needed

Removed DAG proof dependency:
`lem-weil-pbc-dense-open-component-modifications`, module
`Sheaf.AlgebraicGeometry.DenseOpenComponentModifications`.
It was not imported and must not be imported: this parent already imports the item.
It remains the item's caller, so this prunes the circular proof dependency rather
than removing the parent module from the targets' closure.

Removed the redundant public import `Mathlib.AlgebraicGeometry.Morphisms.IsIso`
from the new transfer module; it compiles using `Mathlib.AlgebraicGeometry.Limits`
alone. No existing imports were removed. The three public Mathlib imports are retained
for the item's unchanged statement. The proof uses only the two new modules as
project dependencies. No other node or module from the original component proof
is imported or needs proof for this delivery. The unit's realized statement and
steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The item's sole original proof dependency named its parent theorem. The parent
proves the nonempty case by applying this very theorem, so the proposed dependency
was circular and the module import would create a cycle. Replaced that dependency
with the independent geometric construction and the proved categorical transfer.

LeanSearch returned Internal Server Error for both searches; the search records
mark it unavailable without assigning a verdict. LeanFinder, Loogle, and local
source searches returned ingredients, and the categorical ingredients suffice for
a complete proof of the transfer theorem.

The generic component coproduct lemma does not require n>0; the item's existing
positive-family binder is kept unchanged. The proof registers its implied
`NeZero n` instance. No target signature, existing definition, or existing public
statement was changed.

During packaging, `/tmp` exhausted its inode capacity, despite available disk
space. Temporary shell files were redirected inside this sandbox; no shared files
were removed or tools modified.

## New nodes

`lem-weil-pbc-dense-open-component-coproduct`:
`lean/Sheaf/AlgebraicGeometry/DenseOpenComponentCoproduct.lean`, declaration
`AlgebraicGeometry.exists_dense_open_component_coproduct`. This is the remaining
geometric construction with prescribed component dense opens. Its source, proof,
searches, statement dependencies, Lean record, chapter and unit are recorded.

`lem-weil-pbc-sigma-desc-restrict-iso`:
`lean/Sheaf/AlgebraicGeometry/SigmaDescRestrictIsIso.lean`, declaration
`AlgebraicGeometry.isIso_sigmaDesc_comp_restrict`. This categorical transfer is
fully proved using Mathlib's universal finite coproducts and restriction APIs.
Its node records the two comparison-isomorphism constructions and their
coproduct identity. It introduces no geometric hypotheses or remaining sorry.

There are no change records: existing public interfaces are unchanged and the
new imports of the item are proof-only.

## Second reading by U1

1. PASS: compared every delivered module with the repository. The item is the
only existing module; its declaration signature and docstring are byte-for-byte
unchanged. The diff adds two proof-only imports and replaces its proof. Both
other modules are new. No existing definition or target was changed, and no
change record is needed. No open change record names these declarations.

2. PASS: compiled all three modules locally in import order without errors or
warnings. Scratch copies with `#print axioms` show only `propext`,
`Classical.choice`, and `Quot.sound` for the categorical transfer; the geometric
lemma and the item additionally use `sorryAx`, exactly from the single reported
geometric theorem. The delivery tool also probes all private helpers. There is
no hollow definition or forbidden declaration. The scratch copies were removed.

3. PASS: checked both new statements and their proof descriptions. For n=0 the
component cover forces the target empty; for n=1 the component immersion is a
surjective closed immersion into a reduced target. For intersecting components,
the finite union of other components is closed and misses the generic point of
the given component. A dense open in an integral component contains that generic
point. Thus the prescribed-open construction works without Noetherianity or
finite-type hypotheses. The transfer requires no reducedness, integrality, or
finiteness hypothesis on the modifications. Its proved pullback comparison is
valid for the empty coproduct as well. The remaining geometric lemma is strictly
the component separation and prescribed-open step: it does not mention Y or ν,
and the item genuinely proves restriction and transfer through the modifications.
The existing parent theorem cannot be used, since it calls the item.

Repeated LeanFinder, Loogle, and grep searches with different wording (recorded
in searches.jsonl), and searched both project roots directly. No matching
combined statement was found. Read Mathlib's irreducible-component-open and
surjective-closed-immersion APIs and the existing curve dense-irreducible-opens
proof; they supply ingredients, but the curve theorem requires a curve and does
not give the required component scheme isomorphism. Closing the remaining
geometric construction requires substantial new formalization, rather than a
few-minute application. Its complete sourced docstring and node are present.
Checked the component-separation paragraph of
[Stacks Tag 0BAJ](https://stacks.math.columbia.edu/tag/0BAJ) and the normalization
context of [Tag 0A3Q](https://stacks.math.columbia.edu/tag/0A3Q); the reduction does
not silently assume the extra hypotheses of the full birational lemma.

4. PASS after import pruning: the item uses precisely the geometric component
construction and the proved categorical transfer. Removed one redundant public
Mathlib import from the new transfer module. The original item's public imports
supply its unchanged signature; the new project imports are proof-only. The
report lists the sole old proof dependency, the circular parent dependency, as
no longer needed. The parent remains a caller, rather than a pruned module.
Read `dag/units/sk-thm-p1.json`: its realized statement and all four realized
steps remain in place; this is a reduction below the unit level.

5. PASS: read all three node records alongside the Lean declarations. The item's
two steps and dependencies match the chosen opens and restriction/transfer
proof. The transfer node records its universal-coproduct pullback comparison
and cancellation argument, with no project proof dependencies. The remaining
geometric node records the finite component separation, reduced closed
immersion, and prescribed-open gluing. New-node signatures, sources, searches,
creation fields, blueprint ancestry, chapter, and unit agree with the modules.

Second-reading change: removed only the redundant public import
`Mathlib.AlgebraicGeometry.Morphisms.IsIso` from
`Sheaf.AlgebraicGeometry.SigmaDescRestrictIsIso`; updated this report. No proof,
statement, definition, or node needed repair.
