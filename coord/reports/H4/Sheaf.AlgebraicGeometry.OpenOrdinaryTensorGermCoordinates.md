## What changed

Replaced the single hole in `AlgebraicGeometry.exists_openOrdinaryTensor_germ_coordinates`
with a proof using four new proof-only imports. The existing signature and public imports
are unchanged. The four compatible ring coordinates, the canonical semilinear input chain
isomorphism, and the induced tensor chain isomorphism are constructed and proved. The pinned
comparison equation is reduced to its pure-tensor calculation and extended by tensor induction.

New modules: `OpenOrdinaryTensorStalkRingCoordinates`, `OpenSemilinearInputComplexIso`,
`SemilinearTensorComplexIso`, and `OpenOrdinaryTensorPureGermCoordinates`, all under
`Sheaf.AlgebraicGeometry`. The original node's proof route is updated to these four nodes.
There are no adaptations of existing modules or changes to definitions. The input semilinearity
proof reuses the already-proved germ argument of `Modules.RestrictionStalkExtensionIso`;
its private helpers are reproduced locally because the existing public existential theorem
does not specify the canonical component required here.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_openOrdinaryTensor_germ_coordinates` (one original hole).
Added: `AlgebraicGeometry.exists_openOrdinaryTensor_pure_germ_coordinates`, node
`lem-pc-open-ordinary-tensor-pure-germ-coordinates` (one new hole).
This is a decomposition, with net zero holes closed, not a complete proof of the original
mathematical result. The sole remaining statement only computes the pinned maps on a pure
tensor with explicit canonical input coordinates; it asserts no existential ring or chain
isomorphisms and no arbitrary-tensor equation.

Fully proved new declarations:
`AlgebraicGeometry.exists_openOrdinaryTensor_stalk_ring_coordinates`,
`AlgebraicGeometry.exists_openSemilinearInputComplexIso`, and
`AlgebraicGeometry.exists_semilinearTensorComplexIso`. Their private helpers are fully proved.
Local compilation is clean: ring coordinates 14.6 s, input coordinates 29.6 s, generic
tensor transport 3.6 s, pure-generator statement 11.0 s, and the original theorem 28.5 s.

No other holes are added, no data are chosen from a new unproved existence statement, and
no `sorry` occurs in a definition.

Edge cases: an empty output open has no point z; zero rings and zero complexes are allowed;
no flatness or boundedness is used; the generator equation is stated for every integer degree.
The generic input construction handles point equality by equality induction. The tensor
construction includes inverse equivalences and differential naturality, not merely a map on
underlying sets.

## No longer needed

No existing imports, nodes, or modules are pruned. Second reading removed the redundant
public imports `Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`Mathlib.Algebra.Homology.Additive` from the new input-coordinate module: both are already
publicly available through `DerivedOpenRestrictionMaps`. No project module becomes unreachable. The original three definition nodes remain
used through the new modules' statements and proofs. The new helpers use only their required
imports; exploratory reads of tensor sections and unpinned restriction-extension isomorphisms
do not become proof dependencies. The unit `sk-thm-picard-semicon` is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The earlier node's elementary ring and semilinear
steps were substantial Lean constructions, now proved. Its non-elementary final step needs
an explicit pinned-adjunction generator computation; that is isolated without replacing the
original theorem by a renamed copy. No tool or process exception is requested.

## New nodes

`lem-pc-open-ordinary-tensor-stalk-ring-coordinates`: proved compatible four-ring stalk
coordinates with canonical input/output normalization, using open stalk maps and the tensor
map's two restriction equations.

`lem-pc-open-semilinear-input-complex-iso`: proved canonical additive input chain isomorphism,
its semilinearity, and its exact component formula.

`lem-pc-semilinear-tensor-complex-iso`: proved generic tensor transport for semilinear chain
isomorphisms over compatible ring equivalences, including its pure-tensor formula.

`lem-pc-open-ordinary-tensor-pure-germ-coordinates`: the only remaining hole, the pinned
comparison computation on a pure tensor. Its complete proof plan and sources are in its
docstring and node. No change record is needed because existing interfaces are unchanged.

## Second reading by H4

1. **Interface: pass.** Compared the sole existing delivered module with the repository
using `diff`, and compared its theorem signature as a byte string. Its hypotheses, all
four ring compatibility conclusions, semilinearity, pure-tensor formula and pinned
chain-square equation are identical. Existing public imports and definitions are
unchanged. The existing node changes only `proof`, `proof_deps`, and `proof_origin`;
there is no interface change or forced adaptation.

2. **Proof and trust: pass.** Compiled all five modules in import order with `lcompile.py`.
Read the ring proof's endpoint transports and both tensorMap restriction equations,
the input proof's common-open scalar/germ calculation, the generic tensor proof's
semilinear equivalences and differential naturality, and the original proof's tensor
induction. There is exactly one `sorry`, the reported pure-germ theorem; no forbidden
trust mechanism or hollow definition occurs. Scratch copies append `#print axioms`
for every public theorem and private helper. All three constructed helper theorems
and all four private helpers use only `propext`, `Classical.choice`, and `Quot.sound`.
Only the original theorem and the open pure-germ theorem additionally use `sorryAx`.
The scratch input module also compiles after removing both redundant imports.
The preflight also probes the delivered set. Existing choices of tensorMap, pinned adjunctions and tensorStalkIso have
specifications determining their maps; the new ring, input and tensor witnesses come
from proved constructions, not an unproved arbitrary existence statement.

3. **Split statements: pass.** Read the new modules and their four nodes against
Stacks Tags 0098 (pullback stalks) and 0096 (canonical adjunction), the specified
`exists_tensorPullback_stalk_iso` generator formula, the pinned adjunction unit,
`tensorPullbackCompositionIso`, and the Mathlib restriction germ formulas. The only
open new theorem computes the final comparison on pure tensors with explicit
canonical input coordinates and a normalized output ring equivalence. It does not
restate the original existence of four compatible ring equivalences and two chain
isomorphisms: these are independently proved, and the original proof really extends
its generator equation by tensor induction. Its docstring explains the unit/mate
calculation, the section-germ reduction and scalar extension. For a top open the
formula is the same-germ identity; an empty output open supplies no point; zero
modules and rings satisfy the zero formula; all integer degrees are included, with
no flatness, boundedness or nonzero hypothesis. Independently searched with LeanFinder
`open immersion pullback tensor stalk comparison naturality restriction unit` and
Loogle `"tensorProduct", "stalk"`, then `rg` for tensor/germ and restriction/stalk
phrases in Sheaf and WeilConjectures. Results give constituents, not the pinned square.
`RestrictionStalkExtensionIso` has private scalar helpers but its public existential
extension iso lacks the canonical component formula required here. No short complete
proof of the pinned mate computation was found; the named hole remains.

4. **Route and pruning: pass after import repair.** The proof proceeds from the
original theorem down through ring coordinates, canonical input coordinates, generic
tensor transport, then the generator computation. Each of its four new proof imports
is used. The old dependencies `def-pc-derived-open-restriction-maps`,
`def-pc-open-pinned-single-tensor-restriction-iso`, and
`def-pc-single-complex-base-change-stalk-condition` remain used transitively; none is
no longer needed. Removed the two redundant Mathlib public imports in the new input
module after checking their public-import closure through `DerivedOpenRestrictionMaps`.
The unit `sk-thm-picard-semicon` and its `realized` record are unchanged; this is below
its perfect-complex/base-change route, with no bypass of a unit statement or step.

5. **DAG: pass.** Checked all five node files. The original node's four steps and
`proof_deps` match the four helper applications and final tensor induction. Each new
node has its source, proof plan, dependency union, searches, creation/blueprint data,
chapter/unit, and exact Lean declaration record. The ring node adds input/output
normalizations actually used by the original proof. The input node specifies the
component formula actually substituted; the tensor node includes differential
naturality and inverse maps, rather than just an additive map. The remaining pure
node matches the single named hole and the report's decomposition accounting.

Changes by this reader: restored the exact original whitespace before `:=` in the
existing theorem signature; removed two redundant Mathlib imports from the new input
module; added this independent review. No statement, definition or proof route changed.
