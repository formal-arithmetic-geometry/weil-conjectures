## What changed

In `lean/Sheaf/CategoryTheory/MapExtendHomology.lean`, replaced the fully qualified
application `HomologicalComplex.mapExtendIso K ComplexShape.embeddingUpNat E`
with the equivalent method-form application `K.mapExtendIso ComplexShape.embeddingUpNat E`.
Both resolve to the canonical upstream construction. All declaration signatures,
imports, visibility, and the homology comparison construction are unchanged.
Change record: `coord/changes/map-extend-homology-method-form.md`.
This is a repair-queue delivery, not new proof progress. The duplicate removal
requested by the repair queue was already landed before this delivery.

## Proved and sorry left

`mapExtendHomologyIso` is a direct construction and
`mapExtendHomology_nonempty_iso` packages it; both were already complete at the
repository baseline. Holes closed: none. Holes added: none. Sorries left: none.
There are no split-off statements and the net hole reduction is zero.

## No longer needed

None in this delivery: no imports, modules, or proof dependencies are pruned.
The node already has empty `proof_deps`. The earlier removal of
`mapExtendTermIso`, `mapExtendTermIso_comm`, and `mapExtendComplexIso` is prior
landed work, not pruning attributable to this delivery.

## Where the brief, the DAG or earlier work was wrong

The repair queue still requests duplicate removal, but the repository baseline
already uses the upstream isomorphism and contains no duplicate declarations.
The first worker's change is only equivalent notation, not a mathematical repair
or a newly closed proof. Its proposed `coord/changes/map-extend-homology.md`
would overwrite a landed historical record and did not contain verbatim old/new
signatures; the second reader removed it from the sandbox delivery. Preflight classifies exposed definition-body edits as interface changes, so a
separate method-form record contains verbatim old/new definitions and all users.

## Second reading by T1

1. Compared the complete delivered module with the repository using `diff -u`.
   The sole change is the method-form application described above. Existing
   declaration signatures are byte for byte unchanged; no definitions change
   meaning and no target statements change. PASS.
2. Compiled the module locally with `lcompile.py`, without errors or warnings.
   The module has no sorry, axiom, unsafe, opaque, implemented_by, or extern.
   A scratch copy with `#print axioms` for both declarations and both upstream
   isomorphisms confirms only propext, Classical.choice, and Quot.sound. The
   definition constructs an isomorphism directly; it chooses no arbitrary
   witness from an unproved existence statement. PASS.
3. No new declarations or split-off statements exist. Read the upstream
   `mapExtendIso` construction and Mathlib `extendHomologyIso`: their composition
   applies for every natural q, including q = 0, and requires no exactness of E.
   There is no restatement under another name. PASS.
4. The two-step canonical comparison is already the shortest existing route.
   Both public imports are needed in the exposed definition body; ExtendMap
   is not merely a proof import. No old proof dependency is omitted from the
   report. The item is below unit level and does not replace a unit step;
   `dag/units/sk-thm-p1.json` and its realized route remain unchanged. PASS.
5. Read `lem-weil-pbc-map-extend-homology.json`: its proof is exactly mapping
   upstream mapExtendIso by homology, composing extendHomologyIso, and packaging
   the result. Empty proof_deps and the recorded proof_origin still agree with
   Lean. No new node or node edit is needed. PASS.

Second-reading changes: corrected progress/pruning claims, removed the proposed
historical change-record overwrite, and documented checks. Added the method-form change record required by preflight. No further Lean edit
was needed.
