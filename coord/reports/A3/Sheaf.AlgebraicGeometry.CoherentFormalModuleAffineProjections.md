## What changed

The target `coherentFormalModule_affine_projections` keeps its signature and docstring
byte for byte. Its proof now evaluates F on V, applies the existing completed-scalar
limit and algebraic finite-limit theorems, and transports their projection properties
through the specified linear isomorphism. All new proof imports are plain `import`. The new bridge imports no limit machinery
beyond that already available from the formal-module definition.

The first worker's `CoherentFormalModuleAffineProjectionData` and its node were removed:
they merely repackaged the target using a family required to equal its projections.
The replacement `CoherentFormalModuleAffineOpenSectionsAdic` states only finite-level
finiteness, annihilation and successor transition properties. It is strictly a part of
the argument; it asserts no limit projection properties. No definitions were added or
changed, and no existing declaration's signature or visibility changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.coherentFormalModule_affine_projections` (1 of 1 holes
in the assigned module). It depends on existing open statements and the following new one.

Hole added: `AlgebraicGeometry.coherentFormalModule_affine_open_sections_adic`, node
`lem-weil-pbc-formal-module-affine-open-sections-adic`, is exactly `:= by sorry`.
This is a decomposition, not a completed proof of the import closure: one hole closed
and one strictly simpler hole added, net zero directly changed holes. Existing upstream
open theorems were not changed. The first worker's projection-data hole is absent from
the final delivery and is not counted as an upstream hole closed.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine` and
`Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects` from the target.
The old proof dependency `lem-weil-pbc-coherent-formal-modules-affine` is no longer
needed anywhere in this item's proof: the equivalence, completeness and reconstruction
assembly is bypassed in favor of the existing algebraic limit calculation.
`lem-weil-pbc-coherent-formal-modules-restriction-objects` is no longer a direct dependency
but remains below the new finite-level bridge, which imports its module. No claim is made
that either module is unreachable from all other targets. The discarded new projection-data
module and node are also absent. All imports needed by public signatures remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The initial split-off projection-data statement was equivalent to the target universally
quantified over n: choosing the canonical projections proves it from the target, and
rewriting the comparison equations proves the target from it. Its description as a
strictly stronger intermediate theorem did not make it progress. It was replaced by
finite-level hypotheses and a real reduction to the existing algebraic adic-tower lemmas.

The shortest applicable existing route uses `adicTower_completedScalarLimit` and
`adicTower_finiteLimit` directly, without assembling the whole affine category equivalence.
The finite-level bridge is the restriction/sections transport of the existing Spec A
sections theorem, rather than a new version of the whole projection theorem.

## New nodes

`lem-weil-pbc-formal-module-affine-open-sections-adic` is stated in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleAffineOpenSectionsAdic.lean`.
Its source, complete proof in words, finite-level signature and LeanSearch (unavailable), LeanFinder, Loogle and source-grep search
records are in the node and docstring. No change record is needed: only proofs and
proof imports of existing declarations changed, and the removed first-worker helper
was never part of the repository.

## Second reading by A3

1. Compared the target module against the read-only repository with `diff -u` and checked
its theorem signature and docstring exactly: unchanged. Only proof imports and its proof
body changed. No other existing Lean module is delivered; no definition or public import
changed. No open change record named these modules.
2. Both delivered modules compile locally through `lcompile.py --all`, without errors or
warnings. There is one named theorem sorry, exactly the bridge listed above. No axiom,
unsafe, opaque, extern, implemented_by, definition sorry, or custom trust bypass occurs.
The axiom probes show only propext, Classical.choice, Quot.sound and sorryAx, consistent
with the explicit bridge and existing open algebraic finite-limit theorem. The proof
chooses a completed module only from a limit comparison and its coordinatewise scalar
equations: these determine it up to the required linear isomorphism; no arbitrary
existence witness is used in a definition.
3. The original helper failed the strict-part requirement and was removed. The replacement
is true: restriction followed by the affine finite-level theorem gives exactly its
statement. Checked level n=0 (positive level 1), zero system, zero ideal, unit ideal and
empty affine open: finite generation, annihilation and transition kernels have the
expected meanings; for unit ideal and empty open all levels vanish. LeanSearch was unavailable (Internal Server Error); LeanFinder and Loogle
returned no exact match, and source rg found only the Spec A bridge and algebraic limit
ingredients already used in the route. Closing the finite-level bridge requires the
restriction/affine-scheme comparison, which is left as one documented smaller hole.
4. The actual proof uses the existing algebraic theorems and Mathlib's kernel/comap
and ideal-multiple transport lemmas. Its proof imports are needed and plain imports.
Every old proof dependency is accounted for above. Read `dag/units/sk-thm-p1.json`:
this node realizes no unit-level statement or step, and the unit's realized route is
unchanged. The lower-level affine equivalence assembly can therefore be pruned here.
5. The existing node now records the finite-level bridge, completed-scalar limit and
finite-limit dependencies, followed by the elementary kernel transport. Its statement
and all fields outside proof/proof_deps/proof_origin are unchanged. The new node's Lean
signature is copied verbatim, its proof dependencies equal the union of its proof steps,
and its chapter, unit, source, searches, creation and blueprint records are present.

Changes made by this reading: removed the equivalent projection-data helper and its node;
added the strictly smaller finite-level affine-open bridge; wrote the actual algebraic
limit reduction and kernel transport; corrected the dependency records and report.

Dry-run metadata correction: extracted the new signature from the actual declaration
start (the earlier extraction accidentally began at the word theorem in its docstring),
and recorded the attempted but unavailable LeanSearch query. Sources 087W and 087X
were checked directly on the Stacks website; their finite-level reduction and restriction
statements match the bridge proof in words.
