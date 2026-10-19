# Stage-1 report: det-pe-wc-rings-w-local-refinement

## Files written

- `dag/nodes/sec-proetale-coefficients/det-pe-wc-rings-w-local-refinement.json`: split item, six proof steps; not a Mathlib leaf.
- `citations.json`: thirteen step/node quotations, each copied verbatim from the cited statement.
- No new DAG nodes and no new Mathlib leaves. The existing Mathlib leaf `lem-weil-pbc-faithfully-flat-surjective-spectrum` is reused.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, its blueprint tag, w-local refinement, w-localization, and the relevant ind-étale terminology found no declaration asserting the entire item. The properties in `RingTheory/ProEtale/WLocalization/Ideal.lean` concern its particular ideal-w-localization and do not constitute a declaration with all four clauses of this existence statement. No attachment is inferred by combining separate declarations. The exact upstream master checkout is reference material only.

## WANTED

None.

## What was wrong and what changed

The statement is unchanged and agrees with the current main-20261015 blueprint. Its old three-paragraph proof cited no theorem for surjectivity of the spectrum map of a faithfully flat homomorphism. The earlier sandbox attempt added that citation but still described the retained localization as if its points were just the original generalizing points. Its cited statement actually parametrizes them by pairs `(t,q)`. The revised proof uses those pairs explicitly and needs no unproved identification of the two point sets. It also spells out both canonical local-ring maps and their composite, and cites the definition making ind-Zariski a special case of ind-étale before applying composition stability.

The current imported node has no `chapter` or `unit` metadata and the corresponding new chapter/unit JSON records are absent. I read the chapter and unit `_section.md` files and the unit proof in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/` instead. This detail node is not the key statement of its unit, so no realization fields are changed. The unit's first refinement step is followed without replacing its route. The three proper-base-change lemmas declared in `split_report.tool_uses` are generic construction/stability tools used by the blueprint itself.

## Review by Q63

I read `coord/delivery-errors.md` B through E and checked the split against their actual mathematical requirements. The primary source for this item is the current blueprint statement and its three-paragraph proof. I also read the unit's proof of splitting ind-étale covers, Stacks `proetale.tex`, Tags 0975 (`lemma-make-w-local`), 0979 (`lemma-localize-along-closed-profinite`), and 097A (`lemma-w-local-algebraic-residue-field-extensions`), and Stacks `algebra.tex`, Tag 00HQ (`lemma-ff-rings`). The proof origin remains agent-written because it follows the blueprint and the DAG's finite-principal-localization constructions; I do not silently identify those constructions with Stacks' or the upstream generalization-submonoid construction. No SGA source is used. There are no new nodes requiring further sources.

Step 1 uses `def-weil-pbc-w-localization` for the actual algebra and its ind-Zariski presentation, and `lem-weil-pbc-w-localization-points` for its primes, contractions, canonical local rings, and closed diagonal. I read both full statements, including the explicit zero-ring convention in the definition. The point lemma supplies all these clauses, rather than just w-locality.

Step 2 uses `det-pe-wlocal-strict-contractible` only for the closed maximal locus in a w-local ring, and the point lemma for the closed diagonal and contraction of `(x,x)`. Writing that closed locus as `V(I)`, extending the ideal, and intersecting closed subsets are elementary. The displayed membership equivalences use that contraction of a prime is prime; membership in the chosen `V(I)` then means exactly maximality. No algebraicity-of-residue-fields assertion is smuggled into this step. The stronger input that the spectrum is w-local supplies closedness; the proof does not assume that an arbitrary ring has a closed maximal spectrum.

Step 3 applies the retained-localization definition and theorem to the ring `C=B^w` and the subset `T` just proved Zariski closed. The theorem requires every point of `T` to be closed to conclude w-locality and identify its closed points; this is true because `T` is a subset of the closed diagonal. Its point statement is pairs `(t,q)` of primes of `C` with `q` contained in `t`, exactly what the revised step says. I do not use any internal construction from a dependency's proof.

Step 4 takes the canonical `C_q` local-ring identification from `lem-weil-pbc-retained-localization` and the canonical `B_y` identification and contraction from `lem-weil-pbc-w-localization-points`. For `q=(x,y)` their composite is induced by the structural composite `B -> C -> B'`. For closed points the pair is `(t_x,t_x)`, so contraction is `x` and then `x` contracted to `R`, which step 2 proves maximal. Thus clause 4 concerns the actual local-ring map via `B -> B'`, and clause 3 concerns the actual structural map to `R`.

Step 5 uses the definition of `B^w` and the retained-localization theorem for both ind-Zariski factors. `lem-weil-pbc-ind-etale-stability` explicitly states composition stability for both classes. `def-weil-pbc-ind-etale-algebra` says an ind-Zariski presentation is a choice of the ind-étale presentation with the specified terms, so it supplies the inclusion needed before composing with the assumed ind-étale map `R -> B`. There is no additional finiteness or Noetherian hypothesis.

Step 6 uses the full statement of the existing leaf `lem-weil-pbc-faithfully-flat-surjective-spectrum` with precisely the faithful flatness in the item's hypotheses. Its prime lift need not be maximal in `B`: the diagonal point `t_x` of `Spec C` is closed for every prime `x`, which is why step 2 selected that diagonal. Steps 2 and 3 then give the required closed point of `Spec B'`. I read the leaf's source and Mathlib declaration at `RingTheory/Flat/FaithfullyFlat/Algebra.lean:146` as a consistency check.

Small cases checked: for `R=0`, any unital `R`-algebra is zero and both constructions use the allowed empty partitions/neighbourhood case, so the closed-point assertion is vacuous. For a field or a local w-local `R`, every prime selected over its maximal ideal gives a closed diagonal point without needing a separate theorem that the lift is maximal in `B`; the proof uses only the prime lift actually supplied by spectrum surjectivity. The case `B=R` and finite products of fields also makes each construction and contraction formula consistent. Empty selected subsets cause no false nonempty assertion in the retained-localization theorem; faithful flatness supplies a selected point whenever a maximal ideal of `R` exists.

I searched the whole imported blueprint for w-locality/refinement and the DAG for the retained-localization and closed-point statements; the existing definitions and lemmas suffice. No new elementary, duplicate, or clause-restating node is introduced. I reran Mathlib searches exclusively with `msearch.py` and recorded the seven actual queries/results in the item; both semantic phrasings were read. The first Loogle query had unknown identifiers and is explicitly recorded as inconclusive; the second valid quoted-name query returned none. The apparent `W.Localization` grep hits refer to category localization. I read the `PiLocalization` candidates: they define products of local rings, not this w-local ind-Zariski refinement with all four properties. The searches do not justify making this item a Mathlib leaf.

All cited statements were reread and `citations.json` now includes their complete statements, so it covers every clause used, not just a convenient short sentence. `proof_deps` is exactly the union of the six steps' `uses`. Blueprint fields preserve the item's identity and set `same_as` to the empty result of the search for another node asserting this whole refinement. No new unsplit statement, proof sketch, cycle-inducing child, Lean file, or compiler invocation was introduced.

## What could not be finished

The split itself is complete. Delivery preflight is the authoritative mechanical check. The direct read-only invocation of `tools/review_split.py` in the shared repository failed because its environment chose `/home/ubuntu/weil-nt-live-dag/nodes` and then tried to relativize those paths against `/home/ubuntu/weil-newtargets-shared`. I did not change or work around that script; the prescribed delivery tool supplies its own delivery overlay for preflight. The literal brief command with an extra trailing `.` is rejected by `deliver.py`'s argument parser; its documented two-positional-argument form is used for the dry run. No push is requested; the second reader will deliver.

## Second reading by Q63

- Step 1 checked against `def-weil-pbc-w-localization` and `lem-weil-pbc-w-localization-points`, including the zero-ring convention, pair parametrization, contractions, local rings, closed points, and ind-Zariski presentation; verdict: dependencies and objects match.
- Step 2 checked against `det-pe-wlocal-strict-contractible` and the full point lemma, including the closed maximal locus, contraction of `(x,x)`, and the `V(I)` membership equivalence; verdict: elementary and valid under the stated w-local hypothesis.
- Step 3 checked against the retained-localization definition and theorem, including the `(t,q)` point description, unchanged local rings, closed-point hypothesis, and w-local conclusion; verdict: all asserted consequences are stated by the cited nodes.
- Step 4 checked the two canonical local-ring maps and their composite through `B → C → B'`, plus contraction of closed points, against both point theorems; verdict: the local-ring and closed-point clauses use the actual pair objects and are valid.
- Step 5 checked ind-Zariski composition and its inclusion in ind-étale against the definition and stability lemma; verdict: clause 1 follows with no extra hypotheses.
- Step 6 checked faithful-flat spectrum surjectivity against `lem-weil-pbc-faithfully-flat-surjective-spectrum`, including the zero-ring edge case; verdict: every maximal ideal has the required closed lift.
- The item statement was checked clause by clause against the current `main-20261015` blueprint node and its proof; verdict: unchanged and faithful. There are no new nodes to audit under B1–B7; the existing Mathlib leaf is cited unchanged and its declaration/search record remains valid.

Changes made in this second reading: none to the node or citations; only this audit section was appended to satisfy the delivery review record. The earlier worker repair already made retained-localization pairs, canonical local-ring composition, ind-Zariski-to-ind-étale inclusion, and faithful-flat spectrum surjectivity explicit.
