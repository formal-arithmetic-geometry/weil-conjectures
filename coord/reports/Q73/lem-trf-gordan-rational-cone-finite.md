# Report: lem-trf-gordan-rational-cone-finite

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-gordan-rational-cone-finite.json` — statement node, split; Mathlib searches found no exact match.
- `citations.json` — empty, because all proof steps are elementary and cite no DAG node.
- `searches.jsonl` — the executed LeanFinder, Loogle, source grep, and LeanSearch queries, with corrected source-root greps. The node retains its inherited searches and appends these actual queries.

## Attachments

None. No sorry-free declaration in the project states this item.

## WANTED

None.

## Not duplicates

No new node was created, so there are no new-node duplicate pairs.

## What was wrong or changed

The imported item had an empty proof. Its statement is correct, including the case `r=0`; I left the statement and its empty statement-dependency list unchanged. I checked the downstream use in `lem-trf-fine-monoid-finite-saturation`: it needs exactly the finite-translate decomposition stated here. The proof now gives the standard half-open fundamental-parallelepiped argument explicitly, rather than treating Gordan's lemma as an unexplained input. No statement, blueprint route, or dependency was corrected. ILO VIII 3.2.9 asserts that toric saturation is finite but does not give this coordinate argument, so `proof_origin.by` is `agent`, with ILO identifying the input being expanded.

## What could not be finished

Nothing remains unfinished. The theorem is not stated by Mathlib in the required form, so it remains a project statement node rather than a Mathlib leaf.

## Review by Q73

I read the item node, the `sk-i-curve-zero` unit and `sec-trace-formula` chapter records, the nearest blueprint ancestor `lem-trf-local-term-locality`, the downstream node `lem-trf-fine-monoid-finite-saturation`, and the cited source passage in Illusie–Laszlo–Orgogozo, Exposé VIII §3.2.9 (printed p. 104). I also searched the whole DAG and both blueprint snapshots for Gordan, rational-cone, toric-saturation, and parallelepiped statements, and checked the slopmaster2 source for an exact tagged declaration; none exists.

The first proof step introduces the half-open set `Q` of fractional combinations. In the displayed integral basis of `L`, each coordinate of `Q` is bounded by the sum of the absolute coordinates of the finitely many `v_i`; hence its integral-coordinate points form a finite box. This verifies both finiteness and `F ⊆ C ∩ L`, and explicitly covers `r=0`. The second step checks both inclusions: flooring each rational coefficient produces `p ∈ P` and a fractional part `f ∈ F`, while sums of elements of `C ∩ L` stay in `C ∩ L`. The third step verifies the stated finite-generation consequence from the translate equality and the definition of `P`. These steps use only the definitions and coordinate arithmetic, so no node citation is needed; `citations.json` is consequently empty. I checked that no step assumes pointedness, linear independence of the generators, or a choice of real rather than rational coefficients.


The source-root audit corrected my first grep invocations: `msearch.py` already appends the `Mathlib/` directory, so passing a subdirectory starting with `Mathlib/` searched a nonexistent path. Their zero-hit results are retained and explicitly marked invalid, and were followed by correct greps of the whole source root and of `Geometry`. I read the actual hit at `Mathlib/GroupTheory/Finiteness.lean:618–628`: `AddSubmonoid.fg_eqLocusM` concerns equalizers of homomorphisms on a canonically ordered well-quasi-ordered additive monoid. It does not state the finite-translate assertion for lattice points in a rational cone, and obtaining that form is not a one-line specialization. The other source hit is a comment in `Geometry/Convex/Cone/Face/Basic.lean:24–27`, not a theorem. The second Loogle query had an unknown-identifier error; it is recorded as a query error, not an absence result. Semantic hits on Z-lattices, semilinear sets, and number-field fundamental cones do not state the required finite-translate result.

For delivery-errors B–E, I checked that the full statement introduces its group, basis, generators, rational cone and monoid inline; it needs no imported definition node or Stacks tag. There are no new statements needing a separate proof, source, duplicate comparison or Mathlib match; no content has been moved to another node. The steps are written arithmetic arguments, rather than tags used as black boxes: each coordinate is bounded by a specific integer, each fractional coefficient is explicitly rational, and the remainder lies in the lattice because it is `x-p`. All three steps are below 2000 characters, and none hides an independent non-elementary comparison or lemma. There is no off-unit citation, cycle, SGA source, or change to a target or maintainer metadata.

I tested the small cases: no generators gives `P=C=F={0}`; rank zero has the same result for every generator list; all zero generators do as well. For `L=Z` and `v_1=2`, `F={0,1}` covers the nonnegative integers by two translates of `2N`. For `v_1=2,v_2=3`, the fractional set gives finitely many integer remainders without requiring independent generators. For `v_1=1,v_2=-1`, the cone and `P` both contain the entire line and the bound still works; pointedness is unnecessary. The same coordinate bound works for a cone in a proper rational subspace, so full-dimensionality is unnecessary. No statement dispute arises.
