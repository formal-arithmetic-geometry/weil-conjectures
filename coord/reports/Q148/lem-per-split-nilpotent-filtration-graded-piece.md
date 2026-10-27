# Stage-1 report: lem-per-split-nilpotent-filtration-graded-piece

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-split-nilpotent-filtration-graded-piece.json`: item, statement unchanged, split into seven elementary steps. Mathlib verdict: no exact match or one-line specialization found.
- `citations.json`: the verbatim free-basis definition used in steps 1 and 7.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The item is not a Mathlib leaf: the fixed-coordinate ideal-power calculation requires the argument supplied in its proof.

## Attachments

None. I searched the whole project `lean/WeilConjectures/` for the blueprint tag, the item id, nilpotent filtrations, and split nilpotent terminology, and inspected the graded-piece search hits. The finite-filtration categorical/spectral-sequence results and the polynomial/free-locus results do not state this commutative-algebra calculation. No project declaration was found that proves every clause of this item under its hypotheses.

## WANTED

None for this split. The item expressly requests an agent-written basis calculation, not an external theorem. The unrelated original Bennett sources wanted by its parent are not invoked as theorems here.

## Problems found and changes

The item was genuinely unsplit, with no previous sandbox copy, report, or proof. Its source explains the intended elementary calculation but its proof field was empty. I retained the exact statement, statement dependencies, source and blueprint ancestry and all inherited search records; appended only searches actually run in this session; and supplied the calculation explicitly. No statement dispute or change was needed. Nothing remains unfinished in this one-level split.

I read the latest blueprint's `lem-per-artin-gabber-affine-curve.proof.md` and the chapter/unit records. The long historical regular-resolution ancestry in `blueprint.from` is retained as provenance. The current ancestor proof does not itself state this nilpotent calculation; the nearest relevant local source is the accepted agent calculation in steps 7--8 of `lem-trf-bennett-normal-flat-numerical-criterion`, also explained in the maintainer's accepted review of `lem-per-bennett-normal-flat-local-criterion`. I did not cite that ancestor or either Bennett criterion as a proof dependency (which would be circular), or purport to find this formula verbatim in Stacks. The proof is explicitly marked agent-written. The three blueprint levels and the existing unit realization are unchanged.

## Searches and reuse

No existing sandbox searches were present at start. I read and retained the six inherited item search records. Fresh searches are logged verbatim in `searches.jsonl` and appended verbatim, with verdicts, to the item's `mathlib_searches`:

- LeanFinder: “A nilpotent ideal with finite free lower graded quotients in a commutative D algebra: compute the graded quotient of Q plus pB using a split module filtration”.
- Loogle: `"Ideal", "pow", "quotient"`.
- grep in `RingTheory`: `sup_pow|add_pow|nilpotent.*filtration|filtration.*split`.
- LeanSearch: “Associated graded of sum of base ideal and nilpotent ideal when lower quotients are free modules”.
- LeanFinder, second phrasing: “Finite descending filtration of a module with free successive quotients splits after lifting bases; sum of base ideal and filtered algebra ideal”.
- Loogle, second phrasing: `"LinearEquiv", "quotient", "prod"`.

All six services returned successfully. I read the returned signatures. Filtration structures, Rees-module submodules, adic bases, graded algebras and homogeneous ideal operations do not assert the mixed-ideal quotient. `quotient_prod_linearEquiv` assumes a division ring, whereas D is an arbitrary commutative ring. Ideal-power quotient/unit lemmas do not split the filtration. The grep hits for ordinary binomial formulas, comaximal ideal powers and nilpotence bounds likewise do not give the item. These component facts can help a later Lean implementation but do not make the item a one-line Mathlib specialization.

Whole-DAG searches included titles/statements for split free/projective quotients, ideal-power sums/binomial formulas, and split graded filtrations. I opened `lem-weil-pbc-ses-projective-quotient-splits` and `def-weil-pbc-projective-module`: they are reusable general tools, but unnecessary here since lifting each finite basis gives the section explicitly. I opened `def-weil-pbc-free-module` and used its exact basis statement instead. `lem-trf-split-tensor-quotient-decomposition` has different tensor-product and algebra-product hypotheses and does not assert the item. Blueprint searches `nilpotent free`, `filtration free`, `sum of ideals` found no equivalent node; the four hits for the middle query concern sheaf filtrations or automorphism determinants. No new node was created.

## Not duplicates

No new nodes, hence no new/existing node pairs to distinguish. The elementary module splitting and ideal expansion stay in the proof, rather than becoming duplicates or restated clauses.

## Review by Q148

I read the entire item, its parent statement and relevant proof, the accepted predecessor's explicit basis-lift and coordinate-exponent calculation (steps 7--8), and the latest ancestor blueprint proof. In Stacks `algebra.tex` I read the conventions around `item-free-module` (Tag 00C2 within section-conventions, Tag 00AQ); they supply only the ordinary free-module notion. I checked the actual statement of `def-weil-pbc-free-module` in full. It says every element has unique finite basis coordinates, equivalently a direct-sum isomorphism. This is exactly what steps 1 and 7 use. No new-node sources require review.

Step 1 uses that cited basis definition to choose representatives and verify linear independence by projecting to the quotient. In particular a relation landing in Q^(j+1) has zero coefficients, which proves the needed intersection is zero. Subtracting a representative expansion proves generation. No projectivity theorem, flatness, or splitting of algebras is assumed.

Step 2 is a fully stated finite descending induction: Q^N=M is the base; substitute the already established formula into Q^a=E_a direct-sum Q^(a+1) for the step. Thus all later ideal calculations use the same internal direct sum of B. There are no cited nodes in this step and no assumed filtration-splitting theorem.

Step 3 checks both inclusions of (pB)^e Q^a = p^e Q^a from finite products of ideal generators, including e=0. It uses that Q^a is a B-ideal, and uses only the given D-algebra structure; it never assumes D injects into B or that B/Q=D.

Step 4 proves the expansion of (Q+pB)^q by induction, including q=0. Both multiplications and the index ranges are written out. Terms beyond N vanish because Q^(N+1)=0, not because the final module is free. There are no theorem citations hidden behind “binomial expansion”.

Step 5 distributes scalar multiples in the fixed finite direct sum, lists exactly which Q^a contribute to each coordinate, and computes the smallest exponent using nested powers of p. This calculation is elementary once the actual internal direct sums are established. The E_j need not be ideals and need not multiply homogeneously: all ideal products have already been computed in steps 3--4 before the module-coordinate substitution. I checked this distinction specifically.

Step 6 defines the coordinate quotient map, establishes surjectivity by representatives and identifies its kernel coordinate by coordinate. This supplies the actual isomorphism, without an uncited theorem about quotients commuting with sums. Step 7 again uses precisely the cited free-basis definition: membership in p^e E_j is membership of every coefficient in p^e, so the induced coefficient quotient map is bijective. It then verifies annihilation by p on both sides, which makes the D-linear isomorphism a D/p-linear one. The final module M is never assigned a basis. `citations.json` contains a verbatim substring of the cited node for each of the two citations.

I checked B--E of delivery-errors against these files: all objects are introduced; no new node or missing notion is hidden in a statement; there is no false Stacks attribution, elementary-node inflation, theorem used only from a dependency's proof, new cyclic edge, non-elementary uncited lemma, change of coefficient category, or changed hypothesis. Every elementary label corresponds to the displayed direct basis/ideal/quotient calculation, with the two finite inductions spelled out. Each proof step is under 704 characters, and none meets the 2000-character long-step threshold.

Small cases checked by these explicit formulas: p=0 gives b^N/b^(N+1)=M and all lower terms zero; p=D gives zero on both sides; Q=0 gives the ordinary quotient p^N B/p^(N+1)B of the free D-module B, with only j=0 contributing; N=1 gives Q/pQ plus (p/p^2)^(r_0). For a genuinely nonfree last piece take D=Z, B=Z[x]/(x^2,2x), Q=(x), N=1, p=(2): M=Z/2 is not Z-free, yet b=(2,x), b^2=(4), and both sides are (Z/2)^2. Empty bases and rank-zero summands are allowed by the cited definition. A zero ring D forces B=0; all modules and both sides then vanish. None of these checks imposes reducedness, locality or Noetherianity.

## Validation and delivery

The required server dry run exited successfully: `OK (not pushed)` at `34c53cf2f10`; server preflight passed. After this validation note is recorded, I will run the final dry run and then the push sequentially; their final output determines the delivery response. No Lean was written, and no compiler, Lake or local DAG checker was run. All manual writes were confined to the item sandbox.
