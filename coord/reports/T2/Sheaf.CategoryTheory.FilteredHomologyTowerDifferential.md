## What changed

Repair of the landing rejection at returned head 4669ad90ff: removed the duplicate copies
of `CategoryTheory.inclusion_homology_heq`, `CategoryTheory.filtered_alphaIter`,
`CategoryTheory.connecting_heq`, `CategoryTheory.filtered_initial_f`, and
`CategoryTheory.connecting_representative` from the unclaimed module
`Sheaf.CategoryTheory.FilteredHomologyTowerQuotients`. Their existing signatures and
complete proof bodies are relocated verbatim into the lower-level
`Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives`. The quotient module
now imports and uses that single implementation through a proof-only `import all`.
All five remain private. Its public interface and its other proofs are unchanged.

The existing `CategoryTheory.filteredHomology_tower_differential` is proved with its
original signature. The forward-representative identity computes the page f map;
`finiteCycle_derived_comparison` then computes page g. The supplied differential of a
is a cycle by d squared equals zero and monicity of the filtration inclusion. Homology
naturality for the graded projection identifies the resulting class with y.
The concrete iterated image lift from `FiniteCycleDerivedComparison` is reused through
its proof-only `import all`; no arbitrary witness is chosen from mere existence.

`lcompile.py --all` compiles the forward module, differential module and adapted
quotient module without warnings (9.4, 9.2 and 25.0 seconds respectively).
The change is recorded in
`coord/changes/filtered-homology-shared-representative-helpers.md`.

## Proved and sorry left

Hole closed: `CategoryTheory.filteredHomology_tower_differential`, the item's one
original hole (node `lem-sp-filtered-homology-tower-differential`).
Holes added: zero. No sorry remains in any of the three delivered modules.
`CategoryTheory.filteredHomology_tower_forward_representatives` is completely proved
(node `lem-sp-filtered-homology-tower-forward-representatives`), as are its helpers.
This is a proof, with no postponed split-off obligations.

## No longer needed

Removed direct proof imports from the differential module:
`Sheaf.Algebra.Homology.FilteredComplexSubquotients`,
`Sheaf.CategoryTheory.ExactCouple`, `Sheaf.CategoryTheory.FilteredHomologyCoupleData`,
and `WeilConjectures.Algebra.Homology.ExactCouple.Basic`.
Their declarations remain available through necessary imports. No old DAG node or
library module is claimed as pruned: their definitions or constructions remain used.
The five duplicate helper implementations in the quotient module are removed and
replaced by import and reuse; these are private proved statements, not holed modules.
No imports are removed from the quotient module.

## Where the brief, the DAG or earlier work was wrong

The returned version copied five private library theorems word for word. A private
name does not exempt duplicate statements from the landing guard. The repair retains
one implementation and adapts the unclaimed original module to import it. Importing
the original quotient module directly from the forward module would have introduced
the cycle quotient -> differential -> forward -> quotient, so the shared proofs must
live below both consumers. No checker or tool is changed or bypassed.

The original cover split in an earlier attempt was equivalent to the entire item;
it remains absent. Simultaneous representatives a, a', x, y suffice for a direct proof.
The item's hBZ, eH and hH are unused but retained unchanged. No existing public
statement or definition changes; the unit route remains unchanged.

## New nodes

`lem-sp-filtered-homology-tower-forward-representatives` records the proved f half of
the differential calculation. The proof uses the derived-forward restriction equation,
Mathlib `ShortComplex.ShortExact.δ_eq`, and homology functoriality of filtration
inclusions. Its natural-language proof, Lean signature and dependency list remain
unchanged; `proof_origin` now records the single shared implementation of the helpers.
There are no new nodes beyond the one already present in the returned delivery.
The existing differential node describes the f/g calculation actually used.

Change record: `coord/changes/filtered-homology-shared-representative-helpers.md`.

## Second reading by T2

1. Interface and accidental changes: PASS. I compared all three delivered modules
   with the shared repository using diff. The complete raw signature of
   `filteredHomology_tower_differential` is byte for byte unchanged, including hBZ,
   eH, hH, finite U, normalized j/tQ, arbitrary A and the three representative
   equations. The quotient theorem's raw signature is also unchanged. Each of its
   other surviving declarations has the same signature and private visibility.
   The only quotient edits are the proof-only import all and removal of the five
   helpers listed in the change record; each complete helper block is byte for
   byte identical at its new location. The quotient's remaining proofs are unchanged.
   No target or definition changes. The recorded quotient module was unclaimed;
   this is the declared relocation of existing private proofs, not an undeclared
   interface adaptation.

2. Kernel proof and data: PASS. Fresh `lcompile.py --all` compiled the forward,
   differential and quotient modules without warnings (8.1, 14.7 and 22.4 seconds).
   I compiled scratch copies with `#print axioms` for all three public theorems:
   each reports exactly propext, Classical.choice and Quot.sound, with no sorryAx.
   The delivered code has no sorry, axiom, unsafe, opaque, implemented_by or extern,
   and no lines exceeding 100 characters. The cycle b is an explicit liftCycles
   construction from d squared zero and the monic filtration inclusion. The map e
   is the existing recursive comparisonLift, built with factorThruImage, whose
   inclusion theorem I read. The I family from pageCouple_image_prefix is fixed by
   its identity and recursive-inclusion equations. The derivedMaps choice is fixed
   by the derived restriction equations. No arbitrary existence witness is used as
   new data and no definition is added.

3. New statements and small cases: PASS. There are zero split-off sorry statements.
   The one new public theorem proves only the f half into derived D, before g, so
   it is strictly part of the differential argument and is completely proved.
   I matched j, tQ, their normalizations, I and its recurrence/monicity, e and he,
   a, b, x, ha and hx against its node and signature. For s=0, e is the identity
   after I0, p'=p+1 and q'=q, giving the ordinary connecting formula. At s=1 the
   filtration inclusion is F^(p+2) into F^(p+1) and the total degree remains
   p+q+1. For zero a and b the formula is zero; for a zero graded piece both sides
   vanish by the same connecting calculation and monic cancellation. All integer
   p and q are permitted; no projectivity or epic x is assumed.
   I read the representative differential formula immediately preceding Lemma
   12.24.2 in [Stacks 012K](https://stacks.math.columbia.edu/tag/012K) and the
   derived-map construction in [Stacks 011R](https://stacks.math.columbia.edu/tag/011R).
   The shift r=s+1 and the source/target degrees agree. New searches through
   msearch leanfinder, loogle and grep, with different wording, found the Mathlib
   connecting formula already used but no exact filtered-tower statement. Searches
   of lean/Sheaf, lean/WeilConjectures and the local upstream source found the five
   existing private helpers, now reused rather than duplicated. FiniteCycleFormula
   has the generic forward square as a local have inside its proof, not an available
   theorem; the new private induction exposes that needed calculation.

4. Top-down proof, imports and pruning: PASS. The main proof first computes f by
   the proved forward theorem, then applies the existing finiteCycle_derived_comparison
   for g. Naturality and hy identify its initial graded class with y, and monic
   cancellation plus ht identifies the tower lift. It retains the earlier DAG
   definitions and uses the new dependencies directly; no old proof_deps node is
   omitted from the new list. The four removed direct imports are redundant with
   the remaining necessary imports and were proof-only. The public imports supply
   signature types; all newly added imports are proof-only. No module is claimed
   pruned. I opened dag/units/sk-prop-av-pqf-finite.json: its realized arrays are
   empty and unchanged, and no unit statement, step or route is edited or bypassed.

5. DAG agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin; its statement and lean record are unchanged. Its five steps match
   the explicit cycle lift, recursive image comparison, f identity, finite-cycle/g
   comparison and graded naturality calculation in the Lean proof. The new node's
   three steps match tower_forward_inclusion, the connecting representative formula
   and the alphaIter calculation followed by monic cancellation. I checked that
   each proof_deps list is exactly the union of the uses in its proof steps, and
   that the new lean.statement matches its theorem. Its source, creation, blueprint,
   chapter, unit and actual search records are present. The helper relocation is
   accurately recorded in proof_origin and the change record.

Second-reading changes: no Lean proof or signature changes were needed. I added the
missing `unavailable` verdict for the new node's recorded failed LeanSearch request,
added this independent review, and removed the temporary axiom-probe copies from
lean/. Holes closed: filteredHomology_tower_differential, one of one original holes.
Holes added or left in the delivery: zero. The new forward theorem is proved, not a
postponed obligation. No modules pruned.
