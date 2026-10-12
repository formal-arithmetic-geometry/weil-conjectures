## What changed

Repaired `AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_nonvanishing_pullback` by
moving the three helper proofs (`stalk_map_smul`, `nonvanishingLocus_iso`, and `tensorPow_iso`)
inside the target proof as local terms. `AmpleIso` already contains these statements; they are
private, so they cannot be imported by name. The target now uses the same argument without
introducing duplicate top-level declarations, satisfying import-pruning while preserving the
original theorem signature and proof route.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_nonvanishing_pullback`.
Added 0 holes. No `sorry` remains in the delivery. This closes the local hole, not the whole
axiom closure: `#print axioms` still reports `sorryAx` through the already imported
`AlgebraicGeometry.Scheme.Modules.nonvanishing_tensorPullback`.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`;
its module remains a transitive dependency of `NonvanishingTensorPullback`, so no whole-module
pruning is claimed. Replaced it with proof-only imports of
`Sheaf.AlgebraicGeometry.NonvanishingTensorPullback` and
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.

The old direct DAG proof dependencies no longer used directly are
`lem-weil-pbc-invertible-pullback-tensor`, `lem-weil-pbc-tensor-over-quotient-ring`, and
`def-weil-pbc-ample-invertible-module`. The first two remain below the nonvanishing lemma;
the last remains a statement dependency, supplied by the retained public `Ample` import.
No module is claimed to leave the targets' closure. The local helper terms replace duplicate
top-level helper declarations; no additional module or DAG node is needed.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery copied private helper declarations from `AmpleIso` as new top-level
statements. Import-pruning correctly rejected these as duplicates of statements already in the
library. Keeping the helper proofs local avoids redeclaration while retaining their use.


## Second reading by A3

1. **Visible statements unchanged: pass.** Compared the sole delivered module and its existing
   DAG node with the repository versions. The existing theorem signature is byte-for-byte
   unchanged. No definition, public import, or new declaration is added or changed; the node
   changes only `proof`, `proof_deps`, and `proof_origin`. No change record is required.
2. **Proof and axioms: pass for a local-hole closure.** Compiled the actual delivered file
   cleanly using `lcompile.py` (3.6 seconds), and compiled a scratch copy of that current file
   with `#print axioms`. Its axioms are `propext`, `Classical.choice`, `Quot.sound`, and
   inherited `sorryAx`. Separate checks show that the chosen canonical adjunction and the
   upstream tensor-power comparison have only the three standard axioms; `sorryAx` already
   occurs in the imported `nonvanishing_tensorPullback`. No forbidden mechanism, holed
   definition, or new hole is present. The chosen adjunction is proved, and its unit is fixed
   sectionwise by its statement; the tensor-power isomorphism is obtained from a proved theorem.
   The witness section is explicitly the image of the canonical unit section under a composite
   isomorphism, rather than data taken from an unproved existence statement.
3. **Split statements: pass, none added.** The three local helper proofs are complete and are
   genuine parts of the argument: linearity of stalk maps, invariance of nonvanishing under
   isomorphisms, and induction on tensor powers. They introduce no library statements or nodes.
   Checked the zero-exponent base case, zero sections, identity morphisms, and empty schemes:
   the same construction works, and the required positive-exponent case follows without an
   extra hypothesis. Existing private helpers in `AmpleIso` cannot be used by their names.
4. **Shortest route, imports, and units: pass after report correction.** Searched the local
   library and Mathlib for alternative stalk linearity and tensor-power isomorphism lemmas;
   recorded independent Loogle and grep searches through `msearch.py`. No usable shorter
   theorem for this precise predicate was found. The proof uses the existing upstream
   `nonempty_pullback_tensorPow_iso` and existing `nonvanishing_tensorPullback`, leaving the
   local elementary transports. Public `Ample` and `TensorPullback` supply the statement's
   definitions; the two new imports are proof-only. The removed direct import and all three
   removed old direct DAG dependencies are now listed above, with their retained transitive
   or statement uses distinguished. No whole-module pruning is claimed. Read
   `dag/units/sk-thm-p1.json`, including its `realized` field: this auxiliary node is below
   those unit steps, and no unit-level statement, step, or route is bypassed or changed.
5. **DAG agreement: pass.** The revised first step records adjunction uniqueness, the proved
   upstream tensor-power comparison, and transport of the unit section; the second records
   stalk-isomorphism invariance and the imported pointwise nonvanishing criterion. The union
   of their `uses` equals `proof_deps`, and `proof_origin` describes this actual reduction.
   The node's statement and Lean declaration record remain unchanged; no new-node fields
   are needed.

Second-reading changes: corrected `## No longer needed`, clarified the inherited `sorryAx`
in `## Proved and sorry left`, and replaced the stale scratch axiom review with a copy of the
actual current proof. The Lean proof and DAG edits were already correct and were retained.
