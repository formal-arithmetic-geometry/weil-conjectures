## What changed

`AlgebraicGeometry.Scheme.Modules.affine_pushout_ring_section_presentation` now has
an explicit compiling reduction. The second inclusion is constructed as the ring
inverse-image adjunction unit followed by `t`. Its counit identity follows directly
from `hring.2.2` and `Adjunction.homEquiv_unit` applied to the inverse counit.

The proof obtains an affine section-ring pushout, compares it to
`CommRingCat.isPushout_tensorProduct` using `IsPushout.isoIsPushout`, and proves the
two inclusion formulas by the comparison's universal-property equations. Ring
multiplicativity gives the formula on pure tensors. Tensor induction constructs
an empty list, singleton list, or concatenated list as appropriate.

The new proof-only module `Sheaf.AlgebraicGeometry.AffinePushoutRingAffineSections`
states the remaining geometric comparison. It is independent of epsilon and both
counit assumptions. The existing theorem's signature, visibility, public imports,
and docstring are unchanged. No definition, instance or existing statement changes.
The existing DAG node records the written reduction; the new node records the
remaining affine comparison and its source argument. The conservative parser flag is documented in the layout change record below.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.Scheme.Modules.affine_pushout_ring_section_presentation`
(node `lem-weil-pbc-affine-pushout-ring-section-presentation`).
There is no sorry left in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.affine_pushout_ring_affine_sections`
(node `stage3-affine-pushout-ring-affine-sections`). Its whole proof is `by sorry`.
This delivery is a decomposition, not an axiom-free proof or a net hole reduction:
one upper hole is closed and one strictly geometric obligation is added. The
counit identity, ring universal-property comparison, pure-tensor multiplication,
and finite-list extraction are proved in Lean, rather than moved into that hole.

Both modules compile cleanly in import order using lcompile.py. The new comparison
has a full source argument in its docstring. Its canonical second map is constructed
explicitly; no arbitrary data is chosen from an unproved existence theorem. The
ring equivalence used in the target comes from a pushout universal property, which
uniquely determines it by its two inclusion equations.

Edge cases: for f=id the square has two identity upper maps and its pushout is the
original section ring; the comparison and finite-sum formula reduce accordingly.
For an empty affine open C is the zero ring and the pushout is the zero ring, so
surjectivity and the empty-list case remain valid. Zero rings are not excluded by
any hypothesis. No surjectivity of f, flatness, finite type or faithful ring map is
used. `dag/units/sk-thm-p1.json` was read: this helper is below its realized unit
nodes, and no unit statement or step is bypassed.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` from the item. Its node
`lem-weil-pbc-module-pullback-affine-sections` remains part of the remaining
geometric comparison's proposed proof; it is not claimed globally unreachable.

The original direct proof dependencies
`lem-weil-pbc-module-pullback-affine-sections` and
`lem-pc-module-pullback-adjunction` are no longer direct dependencies of the item.
The module affine comparison still uses the former; its canonical unit and the
pushout cancellation comparison still use the latter transitively. The target's
counit calculation uses the ring adjunction directly, without invoking the module
adjunction theorem. The existing public TensorPullbackAdjunction import is retained
to preserve the file's exposed interface. No existing DAG module is claimed
unreachable from the targets.

No additional intermediate surjectivity or finite-list lemma is needed: Mathlib's
ring tensor-product pushout and tensor induction prove those steps directly.

## Where the brief, the DAG or earlier work was wrong

The original DAG step refers to transporting through an object identification and
kappa, but the cited affine module section theorem does not itself identify the
regular module of an arbitrary ring-sheaf pushout with that pullback. Its signature
was read in full, along with TensorPullbackAdjunction, AffineModuleTensorBaseChange,
QuasiCoherenceScalarRestriction and QuasicoherentPushforwardQcqs. The missing ring
section comparison is now explicit; its proof plan specializes the existing
pushout scalar-extension cancellation comparison to the regular algebra module,
then applies quasi-coherent affine pullback sections. No module theorem with a
sorry was rejected merely for being unproved.

The source [Stacks Tag 01SB](https://stacks.math.columbia.edu/tag/01SB) was read. It
uses the algebra C tensor_D C in its affine reduction but omits the details; the
new lemma supplies precisely that ring comparison, rather than asserting that
arbitrary section functors preserve pushouts. The existing two-line ring node's
blueprint chain was followed to the first tensor-section node and then to
`thm-weil-pbc-finite-etale-lifting`; the new node uses that existing ancestry.

The first dry run exposed a leanindex.commands parser issue: the original theorem
keyword had one leading space and was parsed as continuation of the preceding e₀
notation, including its proof. Changing the proof was therefore flagged as a
visibility change. The keyword is now at column zero; all signatures and public
commands are semantically identical. The conservative flag and exact old/new
signature are documented in `coord/changes/affine-pushout-ring-presentation-layout.md`.
The two textual users were listed by downstream.py; the downstream caller is
unclaimed and needs no adaptation. No tool was modified.

## New nodes

`stage3-affine-pushout-ring-affine-sections`, in `dag/nodes/sec-proper-base-change/`,
corresponds to the single new module AffinePushoutRingAffineSections. It states the
specific commutative-ring pushout on sections, with the second map fixed by the
inverse-image unit. It has no epsilon or retraction conclusion and does not state
finite-sum generation. Its argument cites existing quasi-coherent pushforward,
pushout module base change and affine module-section comparisons, with the regular
module and multiplicative compatibility explained in the docstring.

Actual searches are recorded in searches.jsonl. LeanSearch returned Internal
Server Error and is marked unavailable. LeanFinder returned eight neighbouring
section theorems, none giving this geometric comparison. The Mathlib grep found
CommRingCat.isPushout_tensorProduct, which is used directly in the main proof;
its signature concerns rings and does not establish the geometric section-square
comparison. Repository and source-library rg searches found no existing theorem
stating the required ring comparison. Blueprint searches for tensor product and
pushout ring supplied no matching node to substitute for this new obligation.

Change record: `coord/changes/affine-pushout-ring-presentation-layout.md`.

## Second reading by D3

1. Compared both delivered modules with the repository versions. The existing theorem's
signature and visibility are unchanged; the only interface-visible textual adjustment is
placing the theorem keyword at column zero, documented in the change record. The new
module and node are additional declarations.

2. Compiled both modules with `lcompile.py --all`; both compile without errors or warnings.
The item module has no `sorry`; the split theorem is the only remaining `sorry`, and it is
named and documented. No forbidden declarations or hollow definitions occur. The proof's
axioms are inherited only from the allowed library mechanisms (the split theorem remains
open by design).

3. The split statement is the affine section-ring pushout comparison needed by the proof.
It is strictly narrower than the original finite-sum presentation, has no epsilon or
retraction assumptions, and fixes the second map canonically via the adjunction unit. Its
node, docstring source argument, and searches are present; no duplicate declaration was
found in the repository or Mathlib.

4. The proof follows the unit route: the affine section comparison is isolated in the new
geometric node, while the ring adjunction triangle, tensor-product pushout comparison,
pure-tensor multiplication, and induction are proved directly. The removed direct module
section import is no longer needed by the item; the new node records it as a transitive
proof dependency. The unit's realized route is retained.

5. The DAG proof steps and dependencies match the Lean proof: the new geometric node is
the sole non-elementary dependency, and the remaining steps use the direct ring and tensor
arguments. The unit and chapter fields agree with the item's node.

I changed only this report section during second reading; no Lean statements or proofs
required repair.
