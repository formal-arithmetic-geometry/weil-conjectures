# Q05: lem-sfb-sl2-cubic-gauss-identity

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-sl2-cubic-gauss-identity.json`: statement, split into seven explicit steps; Mathlib verdict no match for the item. The mathematical statement is unchanged. Added statement references for its affine spectrum, polynomial coordinate ring and principal localization.
- `citations.json`: one verbatim statement quotation for each of the seven cited-node occurrences across steps 1, 3, 4 and 6.
- `report.md`: this report. `searches.jsonl` is the unmodified log written by the prescribed search command.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves are reused, including the monic-quotient basis; no elementary subargument was promoted to a node.

## Attachments

None. Searched the live read clone `lean/WeilConjectures/` for the exact blueprint tag/id and for cubic/Gauss notions; also searched the group-theory and representation-theory directories for Weyl, rank-one and SL2 language. The Gauss hits concerned polynomial content or Gaussian elimination, not this theorem. No exact project declaration was found and no sorry declaration was treated as a finished proof.

## WANTED

WANTED: Brian Conrad, *Reductive Group Schemes*, Theorem 6.2.4 and its proof, printed pp.201--203, local archival PDF for lem-sfb-sl2-cubic-gauss-identity. Read the online PDF at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, including equations (6.2.2)--(6.2.4), and the final reduction to the explicit SL2 case. The source omits the actual rank-one word computation, so the completed proof is explicitly agent-written. No SGA source was read or invoked. No Stacks tag states this cubic rank-one calculation; the reused general algebra results retain their own Stacks sources.

## What was wrong or missing

The imported item had no proof. Its statement is consistent with the signs in the source: the Weyl element is x(1)y(-1)x(1), and the cubic relation is (h x(1))^3=1. There is no statement dispute and no added hypothesis. In particular one must not assume that a unit has a square root in the original algebra, or that v is invertible, or that equalities on geometric points detect scheme morphisms. Steps 3, 4 and 6 supply the precise algebraic arguments removing those risks, including for nonreduced rings.

The inherited blueprint ancestry has from.node = null; the prescribed ancestor command confirms this for the current chain. Its long, precise from.place and via chain are retained. Read the chapter and unit records and the latest blueprint chapter, unit, and direct-images proof at snapshot ef6f9619fdbffa59e88528fb56483d76c70258c8. This item is the supporting rank-one calculation already specified in its inherited source chain, not a change to the unit or chapter route. The item is not the key node of the unit; no unit realization fields were changed.

## Searches and reuse

Ran all four prescribed search kinds for the item with the logging msearch.py command. LeanFinder was tried with two different descriptions, one by torus/cubic relations and one by the explicit Gauss formula. LeanSearch returned Weyl groups of abstract root pairings. Loogle on "SpecialLinearGroup" returned the matrix group and its structure. The two source grep queries covered its matrix-group file and then all of Mathlib for Gauss decomposition and Weyl/cubic relations. None states this theorem or a one-line generalization. The returned Lie-algebra sl2 triple is not a group-scheme relation theorem. The node retains the pre-existing searches and appends the six real searches from this run with their exact logged queries and outputs; no old query was falsely represented as newly run.

The whole-DAG keyword searches for Gauss, square roots, monic quotients, and affine coordinate cancellation found the existing `lem-weil-pbc-monic-quotient-free`, `lem-sfb-monic-quotient-faithful-tensor-coordinates` and `lem-sfb-unit-power-fppf-surjective`. Only the first is needed: the basis proves the injection directly, so no flat-descent theorem or new square-root lemma is needed. Read its full statement and its cited Mathlib source `Mathlib/RingTheory/AdjoinRoot.lean` at lines 630--652: `AdjoinRoot.powerBasis'` is the stated monic power basis. Whole-blueprint searches for Gauss, Weyl and cubic returned no imported node; the Laurent search found only a field-specific definition and an unrelated reciprocity theorem. No new Laurent ring node was created.

## Not duplicates

No new nodes. All needed algebraic facts were taken from existing statements or proved in place in a few lines.

## Review by Q05

I read Conrad's equations and the rank-one reduction before writing the argument. They identify precisely the cubic input used here but do not print the calculation, so I did not pass the source's omitted computation off as a cited theorem. The item remains at its original generality: arbitrary nonzero base ring, arbitrary affine target group scheme, and arbitrary algebra-valued parameters. There are no new nodes requiring additional sources or unproved statements.

Step 1 uses the statement of `def-sfb-pinned-split-root-realization` solely for group-scheme operations and homomorphisms, not for the existence of a reductive realization. It gives the group laws used, while the weight-two action and the Weyl conjugation are hypotheses of this item. I wrote out the negative-root torus action and checked the inverse exponent t^(-2).

Step 2 is group word algebra from the assumed cubic relation. I checked that h^2=d(-1) commutes with x(a), that its square is 1, and that replacing h^(-1) with h times the central inverse gives exactly h rather than h^(-1). No outside statement is used in this step.

Step 3 uses `def-pc-scheme` for H being isomorphic to a spectrum and the full statement of `def-weil-affine-spectrum` for the unique ring map underlying a morphism between affine spectra. Both were opened and read. Their statements give H(R)=Hom_A(C,R); cancellation after an injective ring map is then evaluation on each c in C, not a sheaf-descent assertion. The zero algebra has exactly one such map and is disposed of here.

Step 4 uses exactly the free basis clause of `lem-weil-pbc-monic-quotient-free`, not its proof or its separate base-change conclusion. Its hypotheses hold for S^2-t over a nonzero R: it is monic of degree two. The basis (1,s) implies injectivity of R into B, and t being a unit gives the explicit inverse t^(-1)s for s. The step conjugates the previously proved Weyl word by d(s), checks s^2=t in the quotient, and reflects the resulting equality using step 3. I checked the final N(a)d(b)=N(a/b) relation directly from N(a)=d(a)h. This avoids using the fppf square-root lemma as a substitute for an unjustified descent argument.

Step 5 is a displayed calculation, with no external cited fact. It uses only step 4 and the original torus relation to move d(w) across x(w/v). I checked its two fractions: (w/v)/w^2=1/(wv) and 1/(wv)+u/w=1/v. Every denominator is invertible when v and w are units; u is unrestricted. There is no uniqueness-of-Gauss-decomposition assumption and no use of matrices in an arbitrary H.

Step 6 uses `def-weil-polynomial-ring` for the coefficientwise shift by V, `def-weil-ring-localization-away` for the exact fraction-zero criterion, and `lem-weil-pbc-ring-localization-universal-property` for evaluation at u,v once W maps to a unit. I opened their statements and copied the portions used verbatim into citations.json. The key cancellation is explicit: W^n Vp=0 implies W^n p=0 by the coefficient shift, so V is regular even when A has nilpotents. Localization at V is therefore injective. Coordinatewise cancellation in H reflects the equality from that localization back to D. The equality is already an equality of maps Spec D to H, so it proves the claimed scheme identity rather than only a setwise identity over fields. These elementary coordinate and fraction arguments take a few lines each and do not hide an extra geometric lemma.

Step 7 applies the first equality to (-u,-v) and inverts its two sides. I verified the order reversal and that the denominator stays 1+uv; this produces the required d(w)^(-1) in the middle. It holds universally as well. The Weyl assertion is step 2, so every clause of the item is accounted for.

I also checked the small cases u=0 and v=0 (both reduce to identity group factors), and the zero algebra as above. A separate finite matrix sign check over Z/2, Z/3, Z/4, Z/6, Z/8 and Z/9 verified both displayed formulas for all admissible pairs, respectively 3, 7, 12, 21, 48 and 63 pairs, and verified the Weyl sign in each ring. Thus characteristic two, nonunits and nilpotents were included. These matrix checks are sanity checks; the proof for arbitrary H is the word and coordinate-ring argument. The excluded case w=0 over a nonzero field is not used because d(w) is not defined there.

Checked delivery-errors B--E against the written node: the statement and all objects are self-contained; no new nodes, duplicate lemmas or hollow definitions; every non-elementary external input is an existing cited statement; all quotations are literal substrings; no circular proof edge; no change of route; no unmentioned characteristic, smoothness or field restriction. Each step is below 2000 characters (the longest is 982), and none delegates an omitted calculation to an unstated lemma. The non-elementary square-root step is marked false for elementary and cites the monic basis. The other steps are explicit applications of the quoted definitions and finite group or ring calculations.

## What remains unfinished

No mathematical part remains. Delivery validation and push are run with the prescribed tool; their outcome is reported by its terminal result. No Lean was written and no compiler, Lake, repository git command or local preflight/check script was run. All edits are confined to the named sandbox.
