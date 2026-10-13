## What changed

Proved `CategoryTheory.essentiallyConstantInd_hom_colimit_bijective` in
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit` with its original
signature, universes, visibility, and selected cocone unchanged. Added the proof-only import
`Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered`. All three original public imports
remain needed by the statement and its canonical map; no importer-visible changes were made.

Mathlib's same-stage injectivity criterion reduces injectivity to representatives at one stage.
For that stage the essential-constancy factorization immediately transports equal images to
equal representatives. Surjectivity uses the section already present in the witness. Both parts
are fully proved from Mathlib and the real definition; no Sheaf theorem with sorry is used.
Updated the existing node's proof and proof_origin to record this shorter route; proof_deps still
contains only `def-pc-essentially-constant-ind-diagram`.

Searches through leanfinder, loogle and grep found the Mathlib criterion, rather than an exact
existing proof of the item. Read its source and the essential-constancy definition. Read Stacks
Tags [05PU](https://stacks.math.columbia.edu/tag/05PU),
[05PY](https://stacks.math.columbia.edu/tag/05PY), and
[0FND](https://stacks.math.columbia.edu/tag/0FND) online because the literature source copies
are absent on this machine. The unit record `sk-thm-picard-duality` has no realized statement or
step identifying this node; the proof changes only the node's internal argument, retaining the
same Hom computation required by the pre-derived adjunction.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.essentiallyConstantInd_hom_colimit_bijective`
(node `lem-pc-essentially-constant-ind-hom-colimit`). Proved 1 of 1 sorries; none left in the
item and none added anywhere. This is a proof, not a decomposition. The module compiled with
`lcompile.py` without errors or warnings.

## No longer needed

No imports, nodes, or modules are pruned: the only planned dependency is the essential-constancy
definition, which remains needed. The explicit common-stage and coequalization work in original
proof steps 3 and 4 is no longer needed in this module: Mathlib's same-stage injectivity
criterion supplies the general filtered-colimit reduction. No new modules or nodes were added.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or interface error found. The original proof plan is valid but longer
than necessary. Its final naturality discussion is not a separate conclusion of the Lean
statement, which asks only for bijectivity of the specified canonical map. No unit step is
bypassed. The existing declaration docstring is retained verbatim; the updated node records the
implemented shorter proof.

Lean simplification of associativity inside the predicate of `Classical.choose` can change the
selected cocone expression. The injectivity proof therefore uses explicit associativity and
`congrArg` to preserve that exact selected cocone.

## Second reading by S3

1. Compared the delivered module and node with the repository using `diff`. Verdict: pass.
   The sole Lean changes are the proof body and a plain proof-only Mathlib import. The existing
   declaration signature, universes, visibility, docstring, and selected cocone are byte-for-byte
   unchanged. No definitions or target statements change, and no change record is needed.
2. Compiled the delivered module independently with `lcompile.py`, without errors or warnings.
   Scanned its Lean source: no sorry, axiom, unsafe, opaque, implemented_by, extern, or kernel
   bypass. A scratch copy with `#print axioms` compiled and reported exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Verdict: fully proved, with no hollow data construction.
3. There are no new or split-off statements, modules, or holes. Read the actual essential-
   constancy definition and both Mathlib criteria used. Verdict: pass. The section gives a
   representative for every morphism, including empty Hom sets vacuously; the witness supplies
   a stage, so an empty indexing category cannot satisfy the hypothesis. Same-stage equality
   transports along the factorization arrow exactly as required.
4. Read the proof from its conclusion downward and searched the repository for Hom-colimit
   and essential-constancy results. Read Mathlib's same-stage injectivity and surjectivity
   proofs; the implemented direct reduction is already short. The three public imports support
   the unchanged statement; the added filtered-colimit import is proof-only. The old sole
   proof dependency remains used, so the pruning list is complete. Read the unit's `realized`
   record: it assigns this node to no statement or step, and the same Hom computation remains
   available to the pre-derived adjunction. Verdict: no unit route bypassed.
5. Compared the node changes with every step of the Lean proof. Verdict: pass. Only `proof`
   and `proof_origin` change; `proof_deps` remains the exact union of the recorded node uses,
   namely the essential-constancy definition. The statement and Lean record remain unchanged.

Second reading changed only this report: no proof or node repairs were necessary. Independently
confirmed one hole closed, zero holes added, and no modules pruned.
