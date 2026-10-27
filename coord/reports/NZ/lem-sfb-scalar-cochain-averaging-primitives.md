# Stage-1 report: lem-sfb-scalar-cochain-averaging-primitives

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scalar-cochain-averaging-primitives.json`: split into four steps; no statement change. Reuses two existing analytic nodes. Item Mathlib verdict: no matching declaration.
- `citations.json`: verbatim statements for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified record.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, scalar/cochain wording and averaging. Read `RepresentationTheory/DiscreteModule/Procyclic.lean`, especially `DiscreteModule.exists_fixed_lift`: it concerns lifting invariants in discrete primary modules, not normed scalar cochain primitives. The project contains no declaration giving all the item's clauses. The parallel search of `lean/Sheaf/` for this item's tag found none either.

## WANTED

WANTED: an exact norm-topological reference for signed last-variable averaging of trivial continuous cocycles, for lem-sfb-scalar-cochain-averaging-primitives. The inherited source already requests this. The current blueprint's paragraph (3) supplies geometric motivation only; this delivery writes its own elementary algebraic calculation and explicitly records `proof_origin.by = agent`.

## Problems found and changes

The item was statement-only, with no existing sandbox copy, proof or report. There is no released repair note. Its statement is consistent, including the sign $(-1)^n$, without adding hypotheses. The inherited definition and size dependencies are retained unchanged, as are every source/created/chapter/unit field and the null blueprint ancestor. The unit record is an older six-functors record, while the current source is in six-functors-basics; I read both that unit and the current chapter, then followed the current paragraph (3) as directed. This is an analytic input to its open-direct-image route, not a replacement of that route.

The important available interface is stronger than mere existence of a scalar integral: `lem-sfb-prime-to-ell-complete-scalar-integral` explicitly includes continuity for every profinite parameter space, linearity over its continuous-function ring, and compatibility with every continuous parameter map. Thus no extra continuity/currying lemma is needed. Similarly `lem-sfb-finite-quotient-contractive-average` already includes the bound without completeness. The algebraic cancellation is written in the item instead of creating nodes that would simply restate its finite and complete clauses.

## Searches and duplicate check

Ran the required registered command with LeanFinder, Loogle, grep and LeanSearch, plus a second LeanFinder phrasing. Read all returned signatures. Loogle and grep found no matches. The semantic hits concern continuous cohomology definitions, the inhomogeneous differential, degree-one homomorphisms and finite cyclic resolutions. Read the local Mathlib sources for `Representation.averageMap` / `isProj_averageMap` (Invariants.lean:129,144), `inhomogeneousCochains.d` (GroupCohomology/Basic.lean:87), and `groupCohomology.H1IsoOfIsTrivial` (LowDegree.lean:1014). None supplies the normed, parametrized primitive of this item. The remote semantic service's ContinuousCohomology path does not exist at that exact path in the pinned local Mathlib, so it supplies no additional local match. Kept all the item's earlier search records as history and appended exactly the fresh registered records.

Ran whole-blueprint searches for `averaging` and `continuous cocycle` (both zero blueprint matches), and the ancestor command (None). Searched the DAG for averaging/cocycle combinations and both reused analytic node IDs. The finite-quotient-descent node is the consumer that created this item, not an independent proof to cite back. The two existing analytic lemmas supply the strictly smaller ingredients and introduce no back edge. There are no new nodes and therefore no same-tag new/existing pairs requiring a `Not duplicates` entry.

## Review by NZ

I read the item's full statement, its current blueprint source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, the chapter and unit records, and the full statements of both cited analytic nodes. I also read the coefficient and universe definitions used in the item's statement. The blueprint does not prove this analytic lemma; the proof's agent attribution and the WANTED reference remain explicit. There is no new node whose source would need separate review.

Step 1 uses the finite-average node's actual domain D of functions factoring through open normal quotients, its exact average formula and its norm bound, with B=V and K=G. Every last-variable function in this step has that factorization. Its hypotheses do not require completeness. Continuity of the descended cochain is checked by choosing a lift of each point of the finite discrete quotient, and the finite sum stays continuous. This is a direct finite-sum construction, not an invocation of an unrecorded parameter theorem. The norm estimate is the cited pointwise bound followed by taking suprema; the sign has absolute value one.

Step 2 uses the complete-integral node's parameter clause verbatim, with parameter space R=P times G to the power n-1. This is again profinite by the finite product topology. Completeness is assumed exactly here; no completeness assertion is used in step 1. Linearity over C(P,V) is the restriction of the stated C(R,V)-linearity, and naturality is applied to the explicit map u times the identity. The cited node states precisely these facts, including empty spaces. Its scalar bound gives the operator contraction bound without any extra integral theorem.

Step 3 uses only the two cited statements' linearity, normalization and left translation invariance. I expanded the cocycle equation at (g_1,...,g_n,h), retained the a=n term separately, and verified its replacement using left translation h maps to g_n h. The remaining first n+1 terms are exactly the differential of Tc in degree n-1. The final sign is (-1)^(n+1), so d(Tc)=(-1)^n c, and the formula in the item gives db=c. In the finite case every translated function still factors through the same normal quotient, ensuring the average is always applied inside its domain. This is one displayed substitution and rearrangement, marked elementary; no cohomological vanishing theorem or extra homotopy result is hidden in it.

Step 4 separately treats n=1, since the preceding degree n-1 differential formula was written only for positive degree. Averaging c(h)-c(gh)+c(g)=0 cancels the first two terms and leaves c(g)=0. Thus d^0=0 is consistent with the claimed primitive. I checked the empty P case using the singleton zero function space and the zero supremum norm. The arguments also work for trivial G, Q of order one, and the zero cochain; for n=2 a constant cocycle on the trivial group has constant primitive of positive sign, which checks the sign convention on unnormalized cochains. No characteristic-ell division or completeness is smuggled into the finite case.

I checked delivery-errors B through E against these files: self-contained unchanged statement and existing inline group/space definitions; no new elementary/duplicate/clause nodes; no unsupported source attribution or forbidden source; proof dependencies exactly the union of step citations; each cited statement actually contains every interface used; no cycle through the consumer; no silent statement weakening or additional hypothesis. `citations.json` quotes the complete verbatim statement of each cited node for each occurrence, so the normalization, domain, bound and parameter clauses can all be checked directly. Every proof step is shorter than 2000 characters, and none hides an auxiliary comparison or independent theorem. No Lean file was written and no compiler, Lake or build command was run.

## Unfinished work

None in this one-level split. The exact literature reference remains WANTED as above; the mathematical argument is present in the item. The existing two analytic ingredient nodes remain responsible for their own proofs.
