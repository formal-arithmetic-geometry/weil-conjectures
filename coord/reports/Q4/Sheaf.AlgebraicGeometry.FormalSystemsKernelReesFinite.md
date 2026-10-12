## What changed

The item's existing declaration and two public imports are unchanged. Its proof now
establishes coproduct quasi-coherence directly: the coherent formal levels are
quasi-coherent, successor kernel pieces are quasi-coherent, and their coproduct is
quasi-coherent. The upstream coproduct theorem expects an index in the scheme's
universe, so apply it to `ULift ℕ` and transport with `Sigma.reindex`.

The new module `Sheaf.AlgebraicGeometry.FormalSystemsKernelReesFiniteExistence`
states only the remaining existential graded-construction conjunct. It is a strict
part of the original argument and no longer repeats the original conjunction.
The proof-only import of this module stays plain `import`.

## Proved and sorry left

Closed in the item's module: `AlgebraicGeometry.formalSystems_kernel_rees_finite`.
Its quasi-coherence conjunct is proved from existing declarations; the full result
still depends on the open graded-construction theorem below.

Added hole: `AlgebraicGeometry.formalSystems_kernel_rees_finite_exists`, node
`lem-weil-pbc-formal-systems-kernel-rees-finite-existence`, in the new module.
This is the only direct `sorry` in the delivered Lean files. It has a source and
complete natural-language proof docstring. One original hole is closed and one
strictly smaller hole is added: this is a decomposition, net zero holes closed,
not a complete proof of the graded construction.

Removed the first worker's redundant hole
`AlgebraicGeometry.formalKernelPiece_sigma_quasicoherent` and its proposed node:
that clause is now proved inline, without adding a duplicate of the upstream
kernel/coproduct lemmas. Also removed the quasi-coherence clause from the new
existence hole, which had repeated the entire item unchanged.

## No longer needed

Removed these direct imports from the item's module:

- `Sheaf.AlgebraicGeometry.Coherent` (already available through the public types);
- `Sheaf.AlgebraicGeometry.CoherentFormalModule` (already available through the pieces);
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`;
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`;
- `Sheaf.RingTheory.CompletedModuleAssociatedGradedGenerators`.

All old `proof_deps` absent from the new parent proof are listed here:
`def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-coherent-formal-modules-affine`,
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-completed-module-associated-graded-generators`, and `pqf-def-coherent`.
The first six remain in the natural-language proof plan of the new construction
hole; they are not needed to elaborate the parent's actual Lean proof. The old
`pqf-def-coherent` locality step is absorbed by the definition of local generation.
No claim is made that these modules are globally unreachable from other targets;
the maintainer's import-closure ledger determines global pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's existence theorem had exactly the item's full statement, so its
application did not constitute a reduction. Its separate quasi-coherence hole was
redundant even within that proof. Both new nodes had empty notion dependencies,
unexecuted search claims, and one-line proof sketches; the quasi-coherence comment
was not a declaration docstring and detached the item's original docstring from
its declaration. The parent's DAG proof was not updated. These faults are repaired.

LeanSearch currently returns Internal Server Error; the failed attempt is recorded
honestly in `searches.jsonl`. LeanFinder, Loogle and Mathlib grep succeeded.
Independent source inspection used Stacks [087Z](https://stacks.math.columbia.edu/tag/087Z)
and [087W](https://stacks.math.columbia.edu/tag/087W), because the listed TeX source
is not present on this machine. The expanded local lift and degree-zero arguments
in the docstring supply the steps implicit in that short affine source proof.

## New nodes

`lem-weil-pbc-formal-systems-kernel-rees-finite-existence`: the strict remaining
conjunct, with a self-contained mathematical statement, its exact Lean signature,
source, three-step proof and dependency union, real search results and provenance.
It introduces no data definition and chooses no arbitrary witness into library data.
The earlier proposed coproduct node is removed. No change record is needed: no
existing statement, definition, or public import changes.

## Second reading by Q4

1. Compared the two delivered modules with the repository. The item exists and its
   signature is byte-for-byte identical through the return type. The helper module
   is new. No existing definitions or public imports change; there are no adapted
   modules. Verdict: pass after removing the exact restatement.
2. Compiled both modules locally in import order with no errors or warnings.
   Reviewed every declaration and searched for forbidden constructs: only one
   named theorem has `sorry`, and no definition is added. Scratch `#print axioms`
   checks cover the item, the remaining hole and the standalone quasi-coherence
   argument; permitted standard axioms and the documented construction hole are
   the only trust dependencies. Verdict: pass, with the remaining hole explicit.
3. The remaining statement is exactly the graded-construction conjunct. Its source
   proof supplies the local operations and degree-zero generators. Checked degree
   zero, m=0, n=0, the empty scheme, zero formal module, zero ideal (positive
   graded pieces vanish), and unit ideal (annihilation forces every level to zero).
   No global section lifting is assumed; quotient lifts and coefficients are local.
   LeanFinder/Loogle/Mathlib grep and direct alternate-word searches of the library
   found no matching graded sheaf construction. `IdealPowersReesGradedData` concerns
   powers times one coherent module over a pulled-back base ideal and proper scheme,
   not these quotient/kernel sheaves and formal transitions. Verdict: pass.
4. Replaced the quasi-coherence split with existing upstream lemmas and pruned the
   unused imports. Listed every old parent proof dependency no longer used there.
   Read `dag/units/sk-thm-p1.json`: this auxiliary node is not a realized unit key
   or step; no realized field or unit route changes, and the construction hole keeps
   the original affine completion/generator route. Verdict: pass.
5. Updated the parent's actual proof and dependency union; rebuilt the new node's
   statement, verbatim Lean record, source, proof steps, searches, creation metadata,
   and blueprint origin. No stray coproduct node remains. Verdict: pass.

Second reading changed the invalid restatement into a strict remaining conjunct,
proved quasi-coherence directly, removed the redundant hole/node, restored the
original declaration's docstring attachment, pruned five imports, and repaired
both DAG records and the report. The full graded theorem remains a decomposition.
