## What changed

`cechComparison_inverseImage_unit` now reduces by degree induction to degree-zero
normalization and cover-relative effacement. Its existing signature and public
imports are byte for byte unchanged. Three proof-only imports were added:
`CechInverseImageDegreeZero`, `CechCoverRelativeEffacement`, and
`CechComparisonInverseImageSuccessor`.

The new successor module proves `cechComparison_inverseImage_succ_step`: the unit
cochain maps form a morphism of short exact complexes; connecting-map naturality,
the two comparison connecting laws, and exact-functor Ext associativity finish the
induction step. Its `unitCechMap` abbreviation is private, is an explicit existing
cochain construction, and occurs only in proofs. No existing definition changes.
The new degree-zero and relative-effacement modules state the two remaining holes.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.Modules.cechComparison_inverseImage_unit`
(node `lem-pc-cech-comparison-inverse-image-unit`). Its proof still depends on the
following two new named holes:

- `AlgebraicGeometry.Scheme.Modules.exists_cechCoverRelativeEffacement`
  (node `lem-pc-cech-cover-relative-effacement`).
- `AlgebraicGeometry.Scheme.Modules.cechInverseImage_degree_zero`
  (node `lem-pc-cech-inverse-image-degree-zero`).

The second reader also closed the proposed successor hole:
`AlgebraicGeometry.Scheme.Modules.cechComparison_inverseImage_succ_step`
(node `lem-pc-cech-comparison-inverse-image-unit-succ-step`). It adds no hole.

Against the repository baseline this is one upper hole closed and two holes added,
a net of -1 holes closed, hence a decomposition rather than a complete proof of the
item. There are no sorries in the item's module or in the successor module, and no
sorries in definitions. Imported upstream holes are unchanged. The maintainer's
pinned sorry ledger remains the authority for whole-closure counts.

## No longer needed

Every old proof dependency absent from the new direct proof dependency list is:

- `lem-sc-injective-cech-augmentation-quasi-iso`: the augmented-resolution route
  is replaced by cover-relative induction.
- `def-pc-cech-inverse-image-cochain-map`: still needed by the unchanged signature
  and used inside the successor and degree-zero lemmas, rather than a direct step
  of the target's induction.
- `def-pc-flat-cohomology-comparison`: likewise remains a statement dependency and
  is used in the new lemmas; it is no longer a direct induction step.

No existing public import was removed, and no whole module is asserted to be
pruned from the target closure. The successor's private naturality and Ext-boundary
helpers are now proved and used; the earlier report's claim that they were no
longer needed was incorrect.

## Where the brief, the DAG or earlier work was wrong

The earlier report omitted the two new holes from the delivery's hole accounting
and called the upper reduction a proof without distinguishing decomposition. It
also described `unitCechMap` as an existing private declaration, although the
repository baseline contains no such helper. Its visibility change record had no
verbatim existing definition and was unnecessary; it has been removed.

The proposed successor theorem was in the item's module, contrary to the rule that
a new statement has its own module. It has been moved to its own module and
proved. Its original node prose incorrectly assumed surjective connecting maps on
both covers, whereas the Lean signature only assumes quotient-section
surjectivity. The prose now matches the Lean statement. The target node failed to
name the successor theorem used by its proof; its proof steps and dependencies
now describe the actual induction.

The earlier timeout does not justify postponing the successor calculation: with
explicit component extensionality, unit naturality and the existing homology/Ext
lemmas it compiles within the single-file limit. A bounded attempt to close the
degree-zero lemma found unfinished adjunction transport work; no experimental
proof or hole from scratchpad is delivered.

## New nodes

`lem-pc-cech-cover-relative-effacement` states a locally split effacement sequence
usable on the two covers. Its docstring constructs the middle sheaf as a product
of open direct images and proves positive Čech acyclicity by insertion homotopies.
The object is eliminated only inside a theorem proof, never selected as definition
data from an unproved existence theorem.

`lem-pc-cech-inverse-image-degree-zero` states only degree-zero normalization. Its
docstring reduces to the class of a global section and the constant-sheaf
adjunction defining `constIso`.

`lem-pc-cech-comparison-inverse-image-unit-succ-step` is the now-proved
connecting-map calculation in its own module. Its public signature uses the
explicit cochain map; no private declaration occurs in that signature. There are
no change records and no forced adaptations.

## Second reading by Q3

1. Compared every delivered module to the repository baseline. Only the item is
   an existing module. Its theorem signature, normalization objects, and two
   public imports are byte-identical; its original docstring has been restored.
   The other three modules and their statements are new. No target statement or
   existing definition changes. Verdict: pass after removing the unnecessary
   public helper and the inapplicable visibility change record.
2. Compiled all four modules through `lcompile.py --all`, in import order, without
   errors or warnings. Scanned every delivered Lean file: only the two named
   theorem holes above remain; no forbidden declaration or hollow definition.
   Explicit scratch `#print axioms` reports only `propext`, `Classical.choice`,
   and `Quot.sound` for the successor; the target and both remaining holes also
   report `sorryAx`, as expected. deliver3.py's full declaration probe and dry-run
   preflight passed. Verdict: pass, with the documented lower holes.
3. Read all new signatures, proof docstrings and nodes. Effacement uses the product
   of open direct images: projection locally retracts the embedding, and inserting
   the distinguished index contracts each factor. This survives inverse image
   locally on the V-members. Degree zero uses the global-section normalization
   and the specified constant-sheaf isomorphism. The successor uses any qualifying
   short exact sequence and proves equality only on a boundary class, assuming
   equality on its preimage; it is strictly a part of the argument and now proved.
   Tested empty index sets (the covering scheme and its inverse image are empty),
   zero classes, identity inverse image, and q=0 in the successor. Searched the
   library with restriction, boundary, exact-functor, and effacement terminology,
   and used independent leanfinder, loogle and grep searches through msearch.py.
   Existing homology naturality and Ext lemmas were used; no existing theorem
   matches either remaining hole. Sources 01FD and 01EQ were checked directly;
   the effacement expansion is the assigned node's own argument, not a verbatim
   lemma of those tags. Verdict: pass.
4. Read from the top: normalization plus degree induction is a real reduction,
   not an application of a renamed target. Proved its missing connecting-map
   calculation by the existing homology naturality and Ext composition lemmas.
   Retained the original statement imports; additional imports are proof-only.
   Listed every removed old direct proof dependency above. Read
   `dag/units/sk-thm-picard-rr.json`: its `realized.statement` and sole
   `realized.steps` entry are empty, so no realized unit node is bypassed or
   removed. The change stays below the unit level. Verdict: pass.
5. Checked every node's Lean statement verbatim against its module; checked that
   each `proof_deps` equals the union of the proof steps' `uses`. Corrected the
   successor's prose and module record, and the parent's route and dependencies.
   New nodes retain the required source, creation, blueprint, chapter/unit,
   search and Lean records. Verdict: pass after repair.

Second-reading changes: proved the successor hole; moved it to a dedicated module;
made its cochain abbreviation private and removed the false visibility record;
restored the original target docstring; repaired the DAG route and successor
statement prose; replaced misleading hole accounting and pruning claims.
