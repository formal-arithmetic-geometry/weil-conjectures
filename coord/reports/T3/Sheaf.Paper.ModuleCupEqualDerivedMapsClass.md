## What changed

Replaced the stale evaluator split with a fixed natural derived pairing. The assigned
module now obtains the existing derived-class comparison, derived homology tensor
pairing, and naive/derived cup diagram, applies a single-resolution homology formula
twice, and uses injectivity and the supplied equalities of derived maps and input
classes. Its original theorem signature and docstring are unchanged.

The new module `Sheaf.Paper.ModuleCupSinglePairingHomology` states the precise
single-resolution normalization formula, with a complete source-based proof sketch.
It uses the same supplied comparison and tensor interfaces for both resolutions.
No other existing Lean module is adapted or given a changed interface.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.moduleCup_equal_derived_maps_class`
(node `lem-sc-module-cup-equal-derived-maps-class`) from the single-pairing formula.

One new obligation is
`AlgebraicGeometry.Scheme.Modules.moduleCup_single_pairing_homology`
(node `lem-sc-module-cup-single-pairing-homology`). This is a decomposition: one
upper hole closed and one strictly smaller cycle-normalization obligation added.
The assigned module has no remaining sorry. The existing existence theorems for
the comparison and homology tensor interfaces are used as delivered in the library.
No sorry is introduced into an existing dependency module.

## No longer needed

Removed the undelivered `cupEval`, `moduleCup_derived_evaluation_formula`, and false
`moduleCup_evaluation_independent` declarations from the stale sandbox. The two
undelivered node copies `new-module-cup-derived-evaluation-formula` and
`new-module-cup-evaluation-independent` are archived in scratchpad and are not
part of this delivery; no published DAG node is deleted.

The assigned module's direct proof import of
`Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` is replaced by
`Sheaf.Paper.ModuleCupSinglePairingHomology`. Naive/derived compatibility remains
needed through the new module, so its node and module are not globally pruned.
Removed the redundant direct import of
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
from `ModuleCupSinglePairingHomology`: the required declarations are already
publicly imported through `DerivedTensorStructure`. This removes a redundant
edge only; that module remains transitively needed.
The old direct proof dependencies `lem-sc-module-cup-resolution-realization`,
`def-sc-module-cup-resolution-data`, and `def-sc-ringed-space-module-cohomology`
are no longer invoked by the assigned theorem's proof. Their declarations remain
needed in signatures or through the single-pairing formula; none of these modules
is globally pruned.
Second reading also removed the redundant public import
`Sheaf.Paper.ModuleCupRealizationComplexData` from the new module: it is already
publicly supplied by `ModuleCupDerivedClassComparison`, and still needed there.

## Where the brief, the DAG or earlier work was wrong

Earlier sandbox work used two stale evaluator statements, including an assertion
that arbitrary bilinear evaluations agree. Those statements remain archived outside
the delivery. That assertion is false: zero and nonzero bilinear evaluations need
not agree. The repaired argument uses one fixed μ and one fixed tensor pairing
instead; the repository version of the assigned theorem still has a sorry.

The return's failed axiom probes and importer failures share the duplicate generated
local symmetric-instance name in `ModuleCupKInjectiveTarget` and
`GlobalTensorPullbackMonoidalNormalization`. The current repository already repairs
this in `ModuleCupKInjectiveTarget` by explicitly naming its local instances, as
recorded in `coord/changes/module-cup-source-lax.md`. This delivery does not restore
any of the stale conflicting anonymous instances.

For all returned failures attributed to changes in `ModuleCupDerivedClassComparison`,
`ModuleCupDerivedHomologyTensor`, `ModuleCupHomologyRepresentability`, and
`ModuleCupShiftedUnitTensor`, this delivery retains those existing library modules
unchanged. Their already delivered public interfaces suffice. The newly added
single-pairing module and the assigned module are checked together in import order;
no consumer of an altered existing interface needs adaptation.

The previous tool refusal about closing no target sorry does not describe this
sandbox: its assigned theorem contains a sorry in the repository snapshot, and this
repair supplies a complete proof of that theorem. No target signature is changed.

The source read is Stacks Tag 0FKU, the global construction and the diagram following
Lemma 20.31.3. The new formula is exactly evaluation of that diagram on a single
pair of cycles, with the already existing class-comparison and tensor-cycle APIs.
The degree-zero, zero-cycle, and zero-module cases use the same equations. The
unit record `sk-prop-av-cube` has no realized step to bypass; the cube route remains.

## New nodes

`lem-sc-module-cup-single-pairing-homology` records the single-resolution formula,
its source, explicit cycle and diagram proof steps, genuine logged searches, and
its verbatim Lean statement in its own module. The assigned node's proof and
proof dependencies now follow the fixed-pairing comparison argument.

No existing definition, statement, visibility, or public import is changed.
`coord/changes/module-cup-class-congruence-proof-transparency.md` records the local
irreducibility attribute conservatively classified as an interface command by the
checker. No forced adaptation is needed.

Repair verification: the two delivered modules compile in dependency order against
the current library, including the explicitly named K-injective target instances.
The redundant derived-monoidal import was removed in this repair. The previous
second-reading section was removed because this revised delivery needs a fresh
independent reading. The worker has not pushed or delivered this repair.

## Second reading by T3

1. Compared the assigned module with the repository by diff. Every existing
signature, docstring, definition and instance body is byte for byte unchanged.
Only the proof, its private import and local elaboration controls differ; the
local irreducibility attribute has its change record. No other existing module
is delivered. Verdict: pass.

2. Compiled both modules in import order through lcompile.py. The only delivered
sorry is the named single-pairing theorem. There is no axiom, unsafe, opaque,
implemented_by, extern, hollow definition or arbitrary witness definition.
The assigned theorem uses existence results only inside a proof. Explicit #print axioms scratch copies of both theorems report only propext,
Classical.choice, Quot.sound and sorryAx; the latter is expected from the named
open split and imported obligations. Verdict: pass.

3. Read C.on_cycles, P.on_cycles and P.natural, Realizes, derivedMap and the
naive/derived compatibility diagram together with Stacks Tag 0FKU. The proposed
formula follows by transporting the tensor cycle along Q(ν) and Q(global t),
then using comparison naturality and μ naturality for the augmentation inverses.
The output lift is uniquely identified by the monic cycle inclusion and the
invertible extension identification. This includes p=q=0; zero inputs give zero
by bilinearity and linearity, and zero modules give zero classes. No resolution
flatness is needed. The split is a strictly smaller single-resolution diagram
evaluation, not a renamed two-resolution equality. Independent leanfinder,
loogle and grep searches (logged in searches.jsonl), plus rg across the cup
modules, found no exact existing formula. Its source and proof docstring and
node are present. Verdict: pass; one hole closed and one added, a decomposition.

4. The upper proof is the direct injectivity-and-rewrite reduction using fixed
C, P and μ. No shorter existing cup formula was found. Both existing public
imports are preserved where required; the new module's redundant realization
import was removed. The No longer needed section now enumerates all old
proof_deps removed from the direct proof, without claiming transitive pruning.
Read sk-prop-av-cube.realized: its statement and step arrays are empty, and this
below-unit reduction keeps the general cube route. Verdict: pass.

5. Compared both node statements and verbatim Lean records with the Lean.
The existing node changes only proof, proof_deps and proof_origin. Their uses
match the fixed-pairing reduction; the new node has source, proof steps, searches,
creation provenance, blueprint ancestry, chapter/unit and Lean record. No
statement is changed. Verdict: pass.

Changes by this reader: removed the redundant public realization-complex import
from the new module, corrected its author group to T3, completed the direct
proof-dependency pruning inventory, and added this independent review. The
mathematical proof and split statement were retained.
