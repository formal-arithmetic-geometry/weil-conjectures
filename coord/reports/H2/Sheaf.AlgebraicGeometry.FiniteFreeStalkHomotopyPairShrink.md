## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_shrink_homotopy_pair_of_stalk`
without changing its signature, public imports, or definitions. Its proof first
shrinks for the P pair, then shrinks for the single-complex pair inside that open,
and restricts the first homotopy again. The two remaining shrinking assertions
live in new, separately importable modules `FiniteFreeStalkHomotopyPShrink` and
`FiniteFreeStalkHomotopyQShrink`, imported only for the proof.

Proved the private helpers `homotopy_of_natIso` and
`restrict_homotopy_P_to_subopen`. The latter applies Mathlib's
`Functor.mapHomotopy` and transports through the natural comparison between
restriction in two stages and direct restriction. No restriction hole remains.
The original target docstring is retained. The new modules have full source and
proof docstrings, and their nodes have self-contained statements and proof steps.

All three delivered modules compile together in import order using lcompile.
No existing signatures, definitions, or visibility were changed. No forced
adaptations were needed. Files touched are these three Lean files, the parent
node and two new nodes, and this report; no scratch Lean files were created.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_shrink_homotopy_pair_of_stalk`
(node `lem-pc-finite-free-stalk-homotopy-pair-shrink`). This is a decomposition,
not a proof of all transitive dependencies: it closes one hole and adds two.

Exactly two new named holes remain, each in its own new module:
- `AlgebraicGeometry.Scheme.Modules.exists_shrink_homotopy_P_of_stalk`, in
  `Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopyPShrink`, node
  `lem-pc-finite-free-stalk-homotopy-p-only`.
- `AlgebraicGeometry.Scheme.Modules.exists_shrink_homotopy_Q_inside_of_stalk`, in
  `Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopyQShrink`, node
  `lem-pc-finite-free-stalk-homotopy-q-inside`.

Both are strictly parts of the pair argument. The P theorem has no Q parameters;
the Q theorem has no P or boundedness parameters. Rank zero, d=0, and any integer
single degree were checked against the proof arguments. No arbitrary witness
is chosen into a definition. The target module itself contains no sorry.

## No longer needed

Removed the proof-only import `Sheaf.Topology.PresheafModuleStalkFunctor` from the
target module. The parent no longer directly uses nodes `def-weil-pbc-free-module`,
`def-weil-pbc-module-stalk`, and
`lem-weil-pbc-open-immersion-module-pullback-restriction` as proof dependencies;
they remain prerequisites of the new shrinking arguments and are not claimed
as globally pruned. The public imports used by the target statements are retained.

The earlier sandbox's proposed node
`lem-pc-finite-free-stalk-homotopy-restrict` and its unproved restriction statement
are unnecessary: the restriction step is now proved locally. No other module
is claimed to leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox kept all three split holes inside the target module, had
non-self-contained node statements and abbreviated proof docstrings, and carried
an earlier second-reading section. This attempt places the two genuine holes
in new modules, fills the restriction hole, expands their documentation, and
leaves the second reading to the next worker.

The original DAG dependencies describe bases, stalks and restriction, but do
not themselves state homotopy spreading. The new nodes isolate the two finite
matrix arguments that are not yet formalized. The Q case is simpler than the
original general homotopy description: its differentials vanish, so only
shrinking equality of one finite matrix is needed. The blueprint unit route is
preserved; the unit record has no realized substep naming an alternative node.

## New nodes

`lem-pc-finite-free-stalk-homotopy-p-only` states spreading for the bounded P
complex, using only its own fixed map pair. Its module is
`Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopyPShrink`. It follows the parent
source's finite coefficient extension and germ equality argument.

`lem-pc-finite-free-stalk-homotopy-q-inside` states spreading for the single Q
complex inside any prescribed open containing y. Its module is
`Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopyQShrink`. It follows the same source,
using zero differentials to reduce to finite matrix equality. The new nodes
record LeanFinder, Loogle and grep searches; no matching existing spreading
statement was found. LeanSearch was attempted and returned Internal Server Error;
this unavailability is recorded without a mathematical verdict. No statement-change record is needed.

## Second reading by H2

1. I compared each delivered module with the repository version. The existing target theorem has byte-for-byte identical declaration signature and unchanged definitions; the two additional modules are new split-off statements. Verdict: no accidental interface change.

2. I compiled all three modules with `lcompile.py --all`; compilation succeeds with no errors. The target module has no `sorry`; the only remaining sorries are the two named split-off theorems, each documented and represented by a DAG node. No forbidden axioms, unsafe declarations, or hollow definitions were added.

3. I checked both split-off statements against the finite matrix argument and their edge cases (rank zero, degree zero, and arbitrary integer single degree). They are true, strictly simpler than the parent, and are not duplicate library declarations. Verdict: statements and nodes are appropriate.

4. I reviewed the proof route and imports. The parent uses the two split-off shrinking results and proves restriction transport locally through `mapHomotopy` and natural-isomorphism comparison. The removed stalk-functor import and the corresponding parent-only dependencies are no longer needed; the unit route remains represented by the parent node and its two decomposition nodes.

5. I checked the DAG records against the Lean declarations: statements, proof steps, proof dependencies, origins, module paths, and declarations agree. The new nodes carry source documentation and Mathlib/search records. Verdict: DAG and Lean are consistent.

Changed during second reading: added this review section only; no proof or interface repair was necessary.
