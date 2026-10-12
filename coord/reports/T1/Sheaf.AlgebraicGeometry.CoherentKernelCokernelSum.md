## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum` with a complete Lean proof of its
unchanged statement. The kernel clause uses the existing
`coherent_finiteType_submodule_kernel`. The cokernel and extension clauses combine
finite type from `finiteType_image_extension` with two new statements asserting only
finite type of relation kernels. All three short-exact cases are combined using
Mathlib's kernel/cokernel universal-property isomorphisms.

Private helpers prove finite type transport under isomorphism, finite type of finite
free sheaves from actual basis generating data, coherence under isomorphism, and
coherence of zero. Finite sums are proved by induction, with a fully constructed
splitting for the tail-biproduct to full-biproduct to first-summand sequence. The empty
sum is handled by its universal property. No definitions or existing signatures change.

Added proof-only imports of `CoherentCokernelRelations` and
`CoherentExtensionRelations`; removed the unused proof imports listed below. The
three public imports are retained because the public statement uses their notions.
The original declaration docstring is preserved; the updated DAG records the exact
implemented reduction. Added two new modules and their matching DAG nodes.

Read the Stacks source at `/home/ubuntu/c1-stacks-review/modules.tex`, lines 1640–1767,
Lemma 01BY, label `lemma-coherent-abelian`, including both snake-lemma diagrams. The
repository's literature copy is absent on this machine, but this local copy contains
the cited statement and proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.RingedSpace.coherent_kernel_cokernel_sum`
(node `lem-weil-pbc-coherent-modules-kernel-cokernel-sum`). Its module contains no sorry.
This is a decomposition of one hole into two strictly smaller relation-kernel holes,
not a sorry-free proof of the mathematical result. It also depends on the existing
holed `coherent_finiteType_submodule_kernel` and `finiteType_image_extension`; these
are not new holes in this delivery.

Added exactly two holes, each in its own module:

- `AlgebraicGeometry.RingedSpace.coherent_cokernel_relations`, node
  `lem-weil-pbc-coherent-cokernel-relations`, module
  `Sheaf.AlgebraicGeometry.CoherentCokernelRelations`.
- `AlgebraicGeometry.RingedSpace.coherent_extension_relations`, node
  `lem-weil-pbc-coherent-extension-relations`, module
  `Sheaf.AlgebraicGeometry.CoherentExtensionRelations`.

The new statements assert only the relation condition; neither supplies finite type
of the cokernel/middle term, and neither restates the original conjunction. Their
complete source proofs are in their docstrings and nodes. Every private helper is
proved. There is no sorry in a definition or anonymous proof.

All three modules compile cleanly with the prescribed `lcompile.py --all` (exit 0,
no warnings). The first worker's earlier dry run encountered a missing `refuse_missing` import
in the delivery tool. The second reader's rerun passed that point, compiled and
probed the declarations, then stopped solely because the required second-reading
section was not yet written. No tool was edited or bypassed.

## No longer needed

Removed direct imports from the item's module:

- `Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover`, node
  `lem-weil-pbc-coherent-module-local-on-open-cover`: its scheme-only theorem is not
  used. The new relation arguments need locality on general ringed spaces, supplied
  by the open-local definitions in their proof plans, rather than this scheme lemma.
- `Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`, node
  `lem-weil-pbc-ringed-space-module-exactness-local-lifting`: the item's combining
  proof does not use it directly. It remains needed below the two new relation
  nodes, so this is removal of a direct import, not pruning the node from their closure.

Removed from the parent node's direct proof dependencies:
`lem-weil-pbc-module-restriction-open-immersion-colimits`,
`lem-weil-pbc-ringed-space-module-exactness-local-lifting`,
`lem-weil-pbc-abelian-exact-iff-epi-kernel-lift`,
`lem-weil-pbc-snake-lemma-abelian`,
`lem-weil-pbc-coherent-module-local-on-open-cover`, and `def-sp-abelian`.
The snake lemma, local lifting and epi-kernel-lift remain dependencies of the new
relation nodes. Scheme restriction and scheme-only locality are unused throughout
this reduction. Mathlib supplies the abelian infrastructure directly; no new
abelian-category theorem is imported or proved. Other unrelated consumers of these
nodes are outside this item's scope, so no whole-project pruning claim is made.

## Where the brief, the DAG or earlier work was wrong

The original plan cites `coherent_module_local_on_open_cover` while stating the result
for every ringed space. The cited Lean theorem only concerns schemes and cannot be
applied to arbitrary `X : RingedSpace`. The relation-kernel statements now retain
the correct generality and explain restriction/locality through the definitions.
The same caveat applies to the scheme-only recorded restriction functor.

Mathlib and the source library contain finite type/quasi-coherent notions and abelian
category tools, but the searches found no existing coherent relation-kernel theorem.
LeanSearch returned HTTP 500 and is recorded as unavailable, not as a negative search.
Loogle, Lean Finder, grep, and whole-blueprint searches were performed and recorded.

The new cokernel relation statement uses only finite type of the source: in the
Stacks diagram the source is used to make its image finite type, and the combined
finite-free relation kernel is controlled by coherence of the target. Edge cases
checked mathematically: source zero gives relations in an isomorphic coherent target;
target zero gives a finite free kernel; rank zero gives a zero kernel. The extension
relation statement has the same zero-rank case; either zero end term identifies the
middle term with the other coherent end term. Empty opens cause no exception.
The implemented finite-sum induction explicitly includes rank zero.

This item is not in `sk-thm-p1.realized`; the unit's statement and steps are unchanged,
and the proof follows the same coherent-module argument beneath the unit level.

## New nodes

`lem-weil-pbc-coherent-cokernel-relations` isolates the finite relation kernel conclusion
of the cokernel diagram in Stacks 01BY (3), with a finite type source and coherent
target. It is stated in `lean/Sheaf/AlgebraicGeometry/CoherentCokernelRelations.lean`.

`lem-weil-pbc-coherent-extension-relations` isolates the relation-kernel conclusion
of Stacks 01BY (4) for a short exact sequence with coherent end terms. It is stated in
`lean/Sheaf/AlgebraicGeometry/CoherentExtensionRelations.lean`.

Both nodes inherit the item's chapter, unit and nearest blueprint ancestor, carry
actual Mathlib search records, and have complete proofs in words. The visibility
change record below documents the command-level addition of private-helper universe
names; no existing definition, statement or public import changes.

## Earlier second reading (a previous round; superseded)

Pending independent second reading; all three delivered modules compile cleanly.

## Forced adaptations

None.

Change record: `coord/changes/coherent-kernel-cokernel-sum-visibility.md`.

## Second reading by T1

1. **Existing signatures and data: pass.** Compared the complete delivered module
   with the repository using `diff -u`. The existing declaration
   `AlgebraicGeometry.RingedSpace.coherent_kernel_cokernel_sum`, including every
   hypothesis, conjunction and universe annotation, is byte for byte unchanged
   up to its proof delimiter. Its existing docstring is preserved. The only
   additions are four private proved helpers, two proof-only imports and the
   proof. Two unused proof-only imports are removed. Public imports, open commands,
   the local biproduct attribute and all definitions are unchanged. The added
   universe names `v w` are documented in the corrected change record.
2. **Proof and axioms: pass as a decomposition.** Independently compiled all three
   modules through `lcompile.py --all`, cleanly. Inspected every helper, the kernel
   and cokernel reductions, both universal-property isomorphisms, and the explicit
   biproduct splitting. The `Fin 0` case uses the empty universal property; the
   successor identity is checked on index zero and every successor projection.
   Scratch copies with `#print axioms` verified that `finiteType_of_iso`,
   `finiteType_free` and `coherent_iso` use only `propext`, `Classical.choice`,
   `Quot.sound`. `coherent_zero`, the main theorem and the two relation theorems
   additionally use `sorryAx`, from the listed open dependencies. No other axiom
   appeared. There are exactly two new `sorry`s, each the entire body of its
   named relation theorem, and none in data or private helpers. The free generating
   tuple and transported generators are actual constructions; existential generator
   data are taken only from the proved Mathlib finite-type interface, not from an
   unproved mere existence assertion.
3. **Split statements and source: pass.** Read Modules, Lemma 01BY,
   `lemma-coherent-abelian`, lines 1640–1767 of the local Stacks source, including
   both diagrams. The cokernel statement requires only finite type of the source:
   the proof uses it solely for finite type of its image, and coherence of the
   target supplies the combined relation kernel. The extension statement takes a
   genuine short exact sequence and coherent end terms; its relation kernel is
   the kernel of a map from the quotient's finite-type relation kernel to the
   coherent first term. Neither supplies the separate finite-type conclusion and
   neither restates the parent theorem. Both docstrings give the full argument,
   and both have matching nodes. Checked rank zero, either zero end term, zero
   source/target, and the empty open. These yield zero or finite free relation
   kernels or the original coherent relation condition, with no missing hypothesis.
   Independently searched with Lean Finder for "Finite generation of relation
   sheaves of quotients and extensions on arbitrary ringed spaces", Loogle for
   `"IsFiniteType"`, and `rg` on the source library, upstream library and Mathlib
   module-sheaf files. The hits concern finite presentations and generating data,
   not either required relation-kernel conclusion. Upstream `Scheme.Modules.isCoherent`
   is a different predicate (quasi-coherent and finitely presented); it does not
   give this result on arbitrary ringed spaces. The existing restricted
   locally-Noetherian result is also not a route to this general statement.
4. **Shortest route, imports and pruning: pass.** The private finite-type helpers
   use Mathlib generating data directly. The main kernel proof uses the already
   stated finite-type submodule/kernel theorem; finite type of cokernels and
   extensions comes from the already stated image/extension theorem. Mathlib's
   `fIsKernel`, `gIsCokernel` and limit/colimit uniqueness handle the two remaining
   short-exact cases. The two unresolved relation arguments require substantial
   restriction/local-generation constructions and cannot be closed by one of
   the searched lemmas. Every public import supplies a notion in a public
   signature; every proof-only import is used. Compared old and new parent
   `proof_deps`: all six removed direct dependencies are listed in `No longer
   needed`; local lifting and snake arguments remain below the new nodes, so
   those are not claimed as whole-project pruning. Read `dag/units/sk-thm-p1.json`:
   this node realizes neither the unit statement nor one of its steps; its
   `realized` route is untouched. This delivery closes one upper hole and adds
   two strictly smaller ones, a decomposition with hole delta minus one.
5. **DAG agreement: pass.** Compared the parent JSON: only `proof`, `proof_deps`
   and `proof_origin` differ. Its five steps track the actual helpers, kernel
   reduction, cokernel reduction, short exact reductions and finite-sum induction.
   The cited kernel/cokernel nodes are Mathlib leaves for the universal properties
   actually used. Each new node has the correct general-ringed-space statement,
   verbatim Lean signature, source, complete argument, union of step dependencies,
   search records, creation metadata, module, chapter and unit. The new extension
   argument uses only the finite-type kernel conclusion of 01BY (2), not the parent
   theorem. The original docstring's scheme-only restriction/locality citations
   remain as historical proof-plan text; their inapplicability is explicitly
   reported above and they are not used by the implemented proof.

Second-reading changes: corrected the stale visibility record to describe the
actual `universe u` to `universe u v w` command change, added blueprint identifiers
to the two new module docstrings, replaced the obsolete tool-blockage claim with
the rerun result, and wrote this independent reading. No Lean proof, definition
or theorem signature required repair. Temporary axiom-probe source files were removed.
