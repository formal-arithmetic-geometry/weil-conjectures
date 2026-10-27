## Files written

- `dag/nodes/sec-trace-formula/lem-trf-quasi-finite-kernel-quotient-dimension-comparison.json`: item split into four steps; statement and statement dependencies retained. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quote for each citation of each proof step.
- `searches.jsonl`: six searches recorded by the mandated search command; the prior six searches in the imported item are retained.

## Attachments

None for the whole item. The upstream declarations `Algebra.finiteType_and_isQuasiFiniteAtPrime_of_four_rings` (WeilConjectures/RingTheory/QuasiFiniteFourRings.lean:45) and `Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime` (WeilConjectures/RingTheory/QuasiFiniteLocalDimension.lean:46) concern existing dependencies, not this entire statement. The project theorem about a polynomial algebra (DimensionQuasiFiniteOverPolynomialAlgebra.lean:49) has a field and polynomial source, so it does not state this item for arbitrary A. Source searches found no declaration tagged with the item's id and no general kernel-quotient theorem carrying all its clauses. I do not claim an attachment on the basis of a partial match.

## WANTED

None. The proof uses the local Stacks source only.

## Problems found and changes

The item was unsplit, with no proof. Its statement is correct; no STATEMENT-DISPUTED correction is needed. The tempting existing `lem-weil-pbc-dimension-supremum-local-dimensions` is about topological local dimension, not dimensions of localized rings. I did not cite it for ring local dimensions. Instead, the existing localization chain formula proves both local-to-global steps directly.

The source's 00QG is stated for polynomial algebras over fields. I use only its proof pattern, not its statement as a theorem in greater generality. The actual mathematical inputs in the proof are the general 00PN and 00QF nodes and the localization chain formula. The quotient map itself is constructed explicitly rather than moved to a new lemma.

I read the latest blueprint chapter, unit and the ancestor `lem-trf-local-term-locality` statement and proof. The item is an auxiliary along its inherited semistable/component-dimension chain, not a new version of the contracting local-term statement. The two generic algebra lemmas from sk-thm-p1 are declared in split_report.tool_uses. They serve as tools for the inherited ring argument and do not replace any unit-level trace-formula step.

## Mathlib and duplicate searches

I searched the whole DAG for 00PN and 00QF and for localization/dimension keywords, read the candidate statements, and reused `lem-weil-pbc-quasi-finite-four-rings`, `lem-weil-pbc-dimension-inequality-quasi-finite`, and `lem-weil-pbc-localization-dimension-chains-below-prime`. Whole-blueprint searches for `quasi-finite dimension`, `kernel quotient`, `four rings`, and `quasi-finite` found no duplicate of the whole item. There are no new-node/existing-node duplicate pairs.

I ran LeanFinder twice, Loogle, LeanSearch, and two Mathlib grep queries with the mandated command; every service returned successfully. The actual queries and results are in searches.jsonl and in the item's mathlib_searches. I read the quasi-finite definitions and quotient-permanence hits in QuasiFinite/Basic.lean, QuasiFinite/Weakly.lean and ZariskisMainTheorem.lean, and the quotient dimension inequalities in KrullDimension/Basic.lean. The latter compare a ring with its own quotient, not the target T with A/ker(phi). The quasi-finite hits do not supply the whole dimension comparison. The local dimension theorem is in the project and is already represented by 00QF. None of the returned Mathlib declarations states the whole item or specializes to it in one line.

## Unfinished work

None in this stage-1 item. Existing dependency nodes are reused without editing or splitting them. No Lean was written, compiled or built; no sub-agents were started. All writes are confined to the dispatched sandbox.

## Review by Q42

I read Stacks algebra.tex, Tag 00PN (lemma-four-rings, lines 30293 onward), Tag 00QF (lemma-dimension-inequality-quasi-finite, lines 31267 onward), and Tag 00QG (lemma-dimension-quasi-finite-over-polynomial-algebra, lines 31291 onward), including their proofs. For the dimension assembly I also read Tag 00KE (definition-Krull), Tag 00KF (definition-height), Tag 00KG (lemma-dimension-height), and Tag 00E3 (lemma-spec-localization); I checked the tag/label mapping in tags/tags. There are no new nodes requiring additional sources.

In step 1 I checked the quotient-definition node's actual statement: it supplies the quotient operations, surjectivity and kernel of the quotient map. Equality of cosets implies a difference in ker(phi), so the displayed formula is independent of the representative. The three written identities establish the ring-homomorphism laws and the composition equation. This is an elementary quotient argument, not an omitted universal-property theorem.

In step 2 I opened the statement of the four-rings node. It explicitly states BOTH finite type of the new vertical map and transfer of quasi-finiteness. Its finite-sum generation version is especially useful: every target element t equals t times the image of 1 in a one-term sum. The square commutes by step 1, the old map is finite type by hypothesis, and the target horizontal map is the identity, so the contraction of q is q itself. All hypotheses hold, with no assumption on injectivity or Noetherianness. This is an application of an existing more general theorem, not a new node repeating the item.

In step 3 I opened the 00QF node and checked that it assumes precisely finite type and quasi-finiteness at the chosen prime; step 2 has established both for psi. Its contracted prime is exactly r=psi^{-1}(q). I also opened the localization-chain node: its statement is a supremum over chains of prime ideals of R ending below r, not a topological neighbourhood dimension. Each such chain is counted in the definition node for dim R, which I read in full, so the second inequality follows without a separate theorem.

In step 4 I used the same localization-chain statement at the last prime of any given chain in T. The chain is one of the chains in that supremum. Its length is therefore bounded by the local dimension, hence by dim R from step 3. The Krull-dimension definition node gives the final supremum argument. This step contains no hidden global dimension comparison lemma; it proves the comparison in a few sentences from the cited formula and definition.

I tested the hypotheses on A=T and phi the identity (equal dimensions); a surjection onto a nonzero quotient (R identifies with T, so equal dimensions); T=0 (no primes, dimension bottom); and A=0 (a unital map forces T=0 and R=0). If R=0, the factor's unit law also forces T=0, so the bottom-dimensional case cannot hide a prime. Infinite dimensions cause no subtraction or finite-height assumption: the proof only takes suprema and compares chain lengths. No domain, Noetherian or injectivity hypothesis is used. All four proof steps are below 2000 characters and their total assembly is below 3000. I checked delivery-errors B through E: self-contained statements retained, no new duplicate/elementary/clause nodes, exact cited statements quoted in citations.json, no circular dependency, no SGA source, and no unproved comparison hidden in a transport phrase.
