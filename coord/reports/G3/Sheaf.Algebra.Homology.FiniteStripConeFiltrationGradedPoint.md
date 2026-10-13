## What changed

Constructed `finiteStripSourceInclusion`, `finiteStripRowInclusion`, and
`finiteStripGradedMap` in `Sheaf.Algebra.Homology.FiniteStripConeGradedMap`.
The map is real data: the row cone biproduct maps into the ambient cone, factors
through the current tail, and projects to the graded quotient. Proved
`finiteStripRowInclusion_factors` and `finiteStripStep_image_isIso` in Lean.
No arbitrary object is chosen from an unproved existence theorem.

Replaced the target's sorry by a complete Lean assembly of the three canonical
diagonal maps: use their degreewise invertibility, use their adjacent differential
commutation, apply `ShortComplex.isoMk`, and invert. All existing signatures and
public imports stay unchanged. Added two proof-only imports for the two lower
obligations. All four delivery modules compile without warnings locally.

## Proved and sorry left

Closed the original hole in
`HomologicalComplex₂.finite_strip_cone_filtration_graded_point` by decomposition,
not an unconditional proof: one upper hole closed and two lower holes added.

The only remaining sorries in this delivery are:

- `HomologicalComplex₂.finiteStripGradedMap_isIso`, node
  `lem-sc-finite-strip-cone-graded-map-isIso`. This is solely invertibility of the
  explicit degreewise map. It omits the augmentation hypotheses and makes no
  claim about differentials.
- `HomologicalComplex₂.finiteStripGradedMap_differential`, node
  `lem-sc-finite-strip-cone-graded-map-differential`. This is solely one adjacent
  differential square for the explicit map. It makes no invertibility claim.

Proved the tail-factorization theorem and invertibility of the evaluated
filtration inclusion's image factor. Definitions contain no sorry, and use only
these proved facts. The two new statements are independent strictly lower parts
of the argument; neither is the target under another name.

## No longer needed

No original import is pruned. The old direct proof dependencies
`def-sp-filtered-complex-subquotients` and `def-sp-double-complex-total` are
replaced in the target node by the two lower lemmas, but remain used transitively
by the explicit map; neither node nor module is made unreachable. The filtration and
total definitions remain needed by the canonical construction. No extra modules
from the parent filtration proof are imported. The unused exploratory component
comparison was deleted and is absent from the delivery.

## Where the brief, the DAG or earlier work was wrong

The original proof plan named only two definition nodes, without statements for
its non-elementary degreewise quotient and differential calculations. They are
now stated separately for a canonical map that this delivery constructs.

Edge checks: for r=0 every target diagonal object is zero, while the source
survives exactly at n=p-1; the factorization proof handles this using hsupport.
For n-p outside the horizontal strip the target is zero, with no requirement
that p be nonnegative. The source identification is used only at n+1=p, so
negative p and boundary degrees are included. The differential proof in words
kills the source differential and the vertical total term by the next tail.
The horizontal sign is one for integer up shapes; hb and hf identify the
augmentation block. The unit record has no realized node at this item, and its
route has not been changed.

## New nodes

`def-sc-finite-strip-cone-graded-map` records the explicit graded map and its
proved tail factorization in `FiniteStripConeGradedMap.lean`.

`lem-sc-finite-strip-cone-graded-map-isIso` records the objectwise quotient
inverse argument in `FiniteStripConeGradedMapIsIso.lean`.

`lem-sc-finite-strip-cone-graded-map-differential` records the source and target
block differential calculation in `FiniteStripConeGradedMapDifferential.lean`.

No change record is needed: no existing statement, definition, or public
visibility changed. The first worker left the independent second reading to the dispatcher. The initial dry run incorrectly required its section.

## Earlier second reading (a previous round; superseded)

The lower statements are strictly smaller than the target: one concerns invertibility of the explicitly defined degreewise map, and one concerns only its differential square. The target assembly compiles from these statements via `ShortComplex.isoMk`; the unit route remains the finite-strip diagonal quotient route.


## Second reading by G3

1. Compared the item with the repository by diff. Its existing theorem signature,
   docstring and public imports are byte for byte unchanged; only its proof and
   two proof-only imports differ. The other three delivered modules are new.
   No existing definition, statement or visibility changes. Verdict: pass.
2. Compiled all four modules in import order with lcompile.py, without errors or
   warnings. Scanned all delivered Lean for prohibited declarations and hollow
   data. A scratch copy printed axioms for all eight declarations: the three
   definitions and two helper theorems use only propext, Classical.choice and
   Quot.sound; the two named lower holes and the target additionally use sorryAx.
   The only sorries are the two listed lower theorems. Verdict: pass as a
   decomposition, not an unconditional proof (one hole closed, two added; net -1).
3. Read both lower statements and their full docstring proofs. Degreewise
   invertibility is independent of augmentation and differential identification;
   differential commutation is independent of invertibility. Neither restates
   the target. Checked r=0, the source degree n=p-1, arbitrary negative p, and
   n-p at both strip boundaries. The quotient keeps precisely the source when
   n+1=p and target diagonal at vertical index p; the vertical and negative
   source differential blocks enter the next tail. Mathlib's ComplexShapeSigns
   has horizontal coefficient one, so no extra sign twist is required. Searches
   with different queries found cokernelBiproductFromSubtypeIso and total_d/d₁_eq,
   useful generic ingredients but not either complete specialized lemma. Project
   and upstream homology searches found the horizontal first-quadrant comparison,
   whose indices and filtration differ. Neither lower proof can be closed by a
   short application of these results. Verdict: both true and strictly smaller.
4. Read the construction and ShortComplex.isoMk assembly from the target down.
   The map uses only proved factorization and image-isomorphism facts; no data
   is selected from either open lemma. All imports serve statements/constructions
   or the proof; the new lower imports of the target are plain imports. The old
   definition dependencies remain transitively used, so no modules are pruned.
   Read sk-thm-picard-duality.json: this item is not a realized unit node and the
   unit route is unchanged. Verdict: pass.
5. Checked all four node records against the Lean declarations and proof uses.
   The target now depends on exactly the two lower statements, both of which
   depend on the explicit construction; that construction retains the original
   two definition dependencies. New nodes have source, creation, blueprint,
   chapter/unit, Lean and search records. Verdict: pass after metadata repairs.

Changed only report/node metadata: made the canonical-map signature match the checker (which omits declaration modifiers),
expanded its construction/factorization proof description, replaced inaccurate
search summaries by the actual logged queries/results, clarified the replacement
of direct proof dependencies without pruning, and added this independent review.
No Lean proof or statement required repair. Verified the cited Stacks Tag 0133:
it supplies the second-variable context; the specialized cone refinement is the
parent node's explicit argument, as the docstrings say.

Dry-run repair: LeanSearch was actually attempted and returned Internal Server Error;
recorded that unavailability alongside the successful LeanFinder/Loogle/grep searches.
The first dry run caught the missing distinct LeanSearch record and the checker
signature convention; both metadata issues were corrected without Lean changes.
