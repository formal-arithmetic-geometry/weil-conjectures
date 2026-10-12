## What changed

Replaced the sorry in `AlgebraicGeometry.coherent_module_local_on_open_cover` by a
reduction that pairs finite type with the kernel condition in each direction. Its
original signature, visibility, public imports, and docstrings are preserved.
Added three proof-only imports and three new theorem modules:
`CoherentModuleFiniteTypeLocalCore`, `CoherentKernelConditionRestriction`, and
`CoherentKernelConditionDescent`. Each supplies a strictly smaller part of the argument.
No definition, instance, target, or existing declaration statement changes.

## Proved and sorry left

Closed the upper hole `AlgebraicGeometry.coherent_module_local_on_open_cover`
(node `lem-weil-pbc-coherent-module-local-on-open-cover`) by reduction to three
named intermediate theorems. The item's module contains no sorry.

Added and left these three holes, each the whole proof of its public theorem:

- `AlgebraicGeometry.coherent_module_finite_type_local_core`
  (`lem-weil-pbc-coherent-module-finite-type-local-core`): finite type of restricted
  coherent modules and finite type of a module with coherent restrictions.
- `AlgebraicGeometry.coherent_kernel_condition_restriction`
  (`lem-weil-pbc-coherent-kernel-condition-restriction`): only the kernel condition
  restricts, without requiring finite type of the target module.
- `AlgebraicGeometry.coherent_kernel_condition_descent`
  (`lem-weil-pbc-coherent-kernel-condition-descent`): a single kernel is finite type
  from the kernel conditions on the covering opens.

This is a decomposition, not a complete proof: one original hole closed, three
new holes added, hence a delivery-local net of -2. No claim is made about the
whole-library ledger or pruning count, which the maintainer computes. Scratch
`#print axioms` checks allow the three standard axioms and `sorryAx`; the parent
still depends on `sorryAx` through precisely these three open theorems.

## No longer needed

No repository import is removed, and no module is claimed pruned. All original
public imports remain because the statement uses coherence, scheme modules and
open restrictions. The three added imports are proof-only and all are used.

The parent's old proof dependencies `def-pc-scheme`,
`def-weil-sheaf-of-modules-category`, and
`lem-weil-pbc-module-restriction-open-immersion-colimits` are no longer direct
proof dependencies: its proof now uses the coherence definition and the three
intermediate results. They remain statement dependencies and dependencies of
those intermediate results; they are not globally obsolete. The old dependency
`pqf-def-coherent` is retained.

The first worker's earlier private helpers were absent from the repository
baseline, so their removal is not repository pruning. The second reader removed
`coord/changes/coherent-module-local-proof-scope.md` from the sandbox because it
described discarded helper scopes and no longer described the delivered code.

## Where the brief, the DAG or earlier work was wrong

The incoming repair stripped the target's documentation and reformatted its
signature, left a whitespace warning, omitted the kernel holes from the report,
and incorrectly described the finite-type core as an existing imported module.
The core is a new module of this delivery, and its new node lacked required
metadata, search records, and a recorded Lean signature. Its docstring did not
spell out both directions completely. The change record described a previous
private-helper implementation that no longer existed. These faults are repaired.
The earlier report's claim that all private-helper repetition is mechanically
rejected was not verified and is not relied on here.

Fresh Lean Finder and Loogle searches found finite-generator definitions and
constructors, not the required locality conjunction. LeanSearch was unavailable
(Internal Server Error), recorded without a mathematical verdict. Scoped `rg`
found private finite-type helpers in `QuasicoherentFiniteTypeAffine`, which cannot
be called through ordinary imports. `ModulePullbackFiniteType` proves general
pullback preservation but does not establish the cover-descent conjunct; no
short complete replacement was found. Kernel searches likewise found no
matching restriction/descent statements in Mathlib or the library.

## New nodes

`lem-weil-pbc-coherent-module-finite-type-local-core` is the finite-type portion
of the original five-step argument, without either kernel-condition conclusion.
Its source, two proof steps, searches, chapter/unit, blueprint ancestry, creation
metadata, and verbatim Lean statement are recorded. Its docstring proves both
clauses by finite generators on open neighbourhoods.

`lem-weil-pbc-coherent-kernel-condition-restriction` isolates the transfer of a
rank-n free-source map through nested open restrictions. It neither assumes
finite type of F nor concludes coherence. Its docstring and node describe the
open-site equivalence and transfer of finite local generators of the kernel.

`lem-weil-pbc-coherent-kernel-condition-descent` isolates finite type of one kernel
on an open W from the conditions on the intersections W intersect U_i. It does
not assert either finite type or coherence of F. Its docstring and node describe
restriction of that map, the sectionwise kernel comparison and local generators.
No change record is required for these new declarations and proof-only imports;
there is no change to an existing interface.

## Second reading by V1

1. Compared the delivered target with the repository version. Restored its
   original documentation and declaration formatting. The existing theorem
   signature is byte-for-byte identical, all original public imports and
   visibility are preserved, and the three other modules are genuinely new.
   Verdict: no accidental existing interface change.
2. Compiled all four modules through `lcompile.py` in import order and checked
   each declaration with `#print axioms` in a scratch copy. The only holes are
   the three whole named theorem proofs listed above; there are no definitions
   or forbidden declarations in this delivery. The resulting reduction is still
   conditional on those holes. Verdict: valid Lean decomposition, not an
   axiom-free proof of the target.
3. Read the three statements, their docstrings, the coherence definition and the
   original proof plan. Checked empty opens, empty index types, singleton covers,
   rank zero, and non-surjective maps. Empty covers force the space empty;
   rank-zero kernels are zero; no finiteness or Noetherian hypotheses are needed.
   Each statement is true and strictly smaller than the parent; none restates
   coherence locality. Independently repeated searches with different phrases
   and scoped library `rg`. Verdict: legitimate intermediate statements; no
   accessible exact duplicate found.
4. Checked the proof from the target downward: it projects the kernel condition,
   applies the appropriate restriction/descent theorem, and pairs it with finite
   type. All proof-only imports are used; original signature imports remain.
   `## No longer needed` lists every former direct dependency dropped from the
   parent. Read `dag/units/sk-thm-p1.json` and its `realized` bindings: this item is
   below the unit's bound steps, and no bound node, unit route or chapter changes.
   Verdict: the decomposition preserves the original mathematical route.
5. Read all four node records against their Lean statements. Repaired the core's
   incomplete record and ancestry, and replaced the parent's stale claims about
   proved helper constructions by the actual reduction. Its `proof_deps` is the
   union of the proof steps' uses; the new nodes have complete statement and
   source metadata and match their declarations. Verdict: DAG and Lean agree.

Second reading changed: restored the target signature/documentation, removed
unnecessary `classical` and fixed the whitespace warning, expanded the core's
natural-language proof, completed its node and searches, corrected the parent's
proof/dependencies, removed the obsolete change record, and rewrote the report
with all holes and honest decomposition accounting. No kernel theorem or
mathematical statement was changed.
