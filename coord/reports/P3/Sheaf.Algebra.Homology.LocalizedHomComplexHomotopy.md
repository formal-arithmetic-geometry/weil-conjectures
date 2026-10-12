## What changed

Replaced the sorry in `CategoryTheory.localizedHomComplex_homotopy` by a composition
of the cocycle comparison and quotient comparison. The existing theorem signature
and its docstring are byte for byte unchanged. This is a decomposition, not a
completed proof of the mathematical result.

The two new statements are in their own modules:
`Sheaf.Algebra.Homology.LocalizedHomComplexCycles` and
`Sheaf.Algebra.Homology.LocalizedHomComplexHomology`. Both are imported only for
the proof, using plain imports. The homology reduction requires the canonical
component formula for its input equivalence. Each open theorem has a source,
complete natural-language proof, blueprint tag, and matching DAG node.

Removed the unused public imports of
`Mathlib.Algebra.Category.Grp.FilteredColimits` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`; the explicit import-change record
is `coord/changes/localizedHomComplex_homotopy-imports.md`.

## Proved and sorry left

Hole closed: `CategoryTheory.localizedHomComplex_homotopy`.

Holes added and still open:

- `CategoryTheory.localizedHomComplex_cycles_aux`, node
  `lem-pur-localized-hom-complex-cycles-aux`.
- `CategoryTheory.localizedHomComplex_homology_aux`, node
  `lem-pur-localized-hom-complex-homology-aux`.

One upper hole is closed using two strictly smaller, source-backed intermediate
statements. This is a decomposition: zero of the one original mathematical
results is fully proved; holes closed minus holes added is -1 before considering
any independent changes elsewhere in the target closure. No sorry occurs in a
definition, no data construction was added, and neither open theorem merely
renames the full original conjunction.

## No longer needed

Removed imports: `Mathlib.Algebra.Category.Grp.FilteredColimits` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`. No project module
is claimed pruned from the targets' import closure.

Old proof dependency `def-pur-hom-complex` is no longer a direct proof dependency
of the original node: the two auxiliary nodes replace it there. It remains a
proof dependency of both auxiliaries and a statement dependency of the original
node. `Sheaf.Algebra.Homology.HomComplex` stays publicly imported and is not pruned.
No other old proof dependency existed. The unit
`dag/units/sk-def-sf-operations.json` has empty realized statement and steps;
no realized route was bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-81cc4, B9: replaced the entire blueprint value in both
auxiliary nodes with the specified ancestry from
`def-weil-derived-pullback-tensor-hom`, through
`lem-pur-localized-hom-complex-homotopy` and
`lem-pur-rhom-into-kinjective-local`. The cycles node records the canonical
product-projection comparison; the homology node records descent through
boundaries and null-homotopies. Both have `same_as: []`, since the reviewer
found no equivalent blueprint statement. No Lean declaration changed.

The first worker's homology auxiliary was false for an arbitrary equivalence of
sets. For a one-point site over F₂, take L concentrated in degree zero and I with
I⁻¹ = F₂, I⁰ = F₂², and differential x ↦ (x,0). The chain maps form F₂² and the
boundaries are {(0,0),(1,0)}. Permute the canonical cocycle equivalence by swapping
(1,0) with (0,1), fixing (0,0). Two equal homology classes would then have distinct
images in the homotopy category. The original theorem already requires a
canonical component formula; the repaired auxiliary now requires that formula
as well, and the original proof supplies it from the first auxiliary.

The first delivery also lacked auxiliary proof docstrings, self-contained node
statements, verbatim Lean signatures, Mathlib search records, and the update of
the original node's proof dependencies. These are repaired.

The source was read at [Stacks, Hom complexes](https://stacks.math.columbia.edu/tag/0A8X)
and [Equation 0A8Y](https://stacks.math.columbia.edu/tag/0A8Y). The sign in degree -1
is plus, so boundaries are null-homotopies. Tests in words include zero complexes
(singleton cycles, maps and classes), complexes with zero differentials (no
nonzero boundaries or nontrivial homotopies), and unbounded complexes (products
allow arbitrary families, with no finite-support restriction).

## New nodes

`lem-pur-localized-hom-complex-cycles-aux` is the product/kernel step of the
original argument, without the homology or homotopy quotient conclusion.

`lem-pur-localized-hom-complex-homology-aux` is the boundary/quotient step,
conditional on the canonical cocycle equivalence and its component formula.

Both nodes record LeanSearch (unavailable: Internal Server Error), LeanFinder,
Loogle, and source grep. Mathlib's `Cocycle.equivHom`, `Cochain.equivHomotopy`,
`CohomologyClass.homAddEquiv`, and `leftHomologyData'` handle the categorical
Hom-group complex; they do not supply the comparison from evaluated sheaf
products on the slice site. The upstream/project search found no duplicate
localized comparison. Closing either remaining step requires this substantial
comparison, rather than a missing one-line application.

Change record: `coord/changes/localizedHomComplex_homotopy-imports.md`.

## Earlier second reading (a previous round; superseded)

1. Compared each delivered module with the repository. The only existing
   declaration is `CategoryTheory.localizedHomComplex_homotopy`; its signature
   and docstring are byte for byte unchanged. No definition changed. The explicit
   public-import removals have their change record. Verdict: pass after repairs.
2. Compiled the three modules in import order with `lcompile.py`; the only
   textual sorries are the two public named auxiliary theorems. No forbidden
   declarations or attributes and no sorry in a definition. A scratch copy
   checked `#print axioms` for all three declarations: each lists only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The unchanged direct
   importer `RhomIntoKInjectiveLocal` also compiled against the delivered overlay.
   The delivery tool additionally probes every delivered declaration. Verdict: pass with the two reported
   open proof dependencies, so this is a decomposition.
3. Read both auxiliary statements top down, checked the source and edge cases,
   and searched Mathlib and the project independently. Repaired the false
   arbitrary-equivalence homology statement by requiring the canonical
   component formula. Added complete proof docstrings and node search records.
   Each auxiliary is strictly a part of the original argument. Verdict: pass
   after repairs; both reductions remain open.
4. Read the imported Hom-complex construction and its product/differential
   specification. No direct existing lemma eliminates the sectionwise
   comparison. Removed the filtered-colimits and sheaf-Abelian imports; the new imports are plain
   proof imports. The original node's two proof steps are preserved as the two
   reductions. Checked the unit's empty realized route and listed every old
   proof dependency displaced. Verdict: pass.
5. Checked the node statements, sources, proof steps, dependency unions,
   proof origins, creation records, blueprint ancestry and Lean records.
   The original node now follows the exact composition used by the Lean proof.
   Auxiliary Lean signatures are copied verbatim and declaration names fully
   qualified. Verdict: pass after repairs.

Second reading changed: corrected the homology auxiliary's missing canonical
component premise and passed it in the main proof; moved both new statements
into separate modules; added their proof docstrings; repaired the new node
metadata and the original proof plan; removed the filtered-colimits and sheaf-Abelian imports with
an explicit change record; corrected the accounting to decomposition.

## Second reading by P3

1. Compared the item module with the repository using diff and independently
   compared its theorem signature byte for byte. The signature and existing
   docstring are unchanged; only the proof and the reported imports differ.
   The other two modules are new. No definition was changed. The public-import
   removals have the explicit change record. Verdict: pass.
2. Compiled all three modules in dependency order with lcompile.py. A scratch
   copy printed axioms for all three declarations: only propext,
   Classical.choice, Quot.sound and sorryAx occur. The two reported named
   auxiliaries are the only remaining textual sorries; there is no definition
   added and no forbidden declaration form. The unchanged direct importer
   RhomIntoKInjectiveLocal compiled against the overlay. Verdict: pass as a
   decomposition, not a completed mathematical proof.
3. Read both auxiliary statements and their full proof docstrings, including
   the essential canonical component premise of the homology auxiliary.
   Independently checked Stacks Tag 0A8X and Equation 0A8Y, the sign in degree
   minus one, zero complexes, zero differentials, and arbitrary unbounded
   families. Both auxiliaries are true, needed, and strictly part of the
   original conjunction. Independent Loogle search for
   CochainComplex.HomComplex.Cocycle.equivHom returned the categorical
   Hom-group equivalence; LeanFinder search for evaluation of the sheaf product
   Hom complex on the over category returned sheaf Hom and product APIs, not
   the required complex comparison. Independent project rg search found the
   internal-Hom section equivalence and currying constructions, but no
   duplicate localized comparison. Neither auxiliary is a quick direct
   application of those declarations. Verdict: pass with both holes open.
4. Read HomComplex and the internal-Hom construction from the top downward.
   The main proof exactly combines the cocycle and quotient reductions.
   All remaining public imports support the statements; both new proof-only
   imports are plain imports. The report lists the two removed Mathlib imports
   and the sole displaced old proof dependency, def-pur-hom-complex, which
   remains a statement dependency and an auxiliary proof dependency.
   The unit sk-def-sf-operations has empty realized statement and steps;
   no realized route was changed. Verdict: pass.
5. Independently compared all three node Lean signatures to the source text
   and checked that proof_deps equals the union of the proof steps' uses.
   Read the source, origin, creation, ancestry, searches, chapter and unit
   records of both new nodes. The original node's proof follows the actual
   Lean composition. Verdict: pass.

Second reading changed only this report: added the required current review
section and independent verification evidence. No further Lean or node repair
was needed. Accounting remains zero of one original mathematical result fully
proved, one original hole closed, two holes added, and no project module pruned.
