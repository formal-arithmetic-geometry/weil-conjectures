# Q11: lem-sfb-normalized-comparison-tower-restriction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normalized-comparison-tower-restriction.json: statement item split into seven short elementary calculation steps; no Mathlib match for the whole statement.
- citations.json: the verbatim category-definition statement cited in step 1.
- searches.jsonl: actual search-command log for this item; existing NN searches in the imported node retained, and Q11 searches appended.
- report.md: this report.

No new nodes, no new Mathlib leaves. The item is sufficiently close to definitions that none of its substitutions warrants a separate node.

## Attachments

None. Searching the project under lean/WeilConjectures for the exact blueprint tag and for normalized comparison, comparison tower and coefficient-associativity notions found no declaration giving the stated formal calculation. Pro-etale adic comparison-tower declarations concern different functors and do not provide this item.

## WANTED

None. The blueprint proof used is available locally. No external non-elementary theorem is used, so there is no Stacks result to assign a tag to. The existing category definition cites Stacks Tag 0014.

## What was wrong or changed

The imported node had no proof. Its statement is unchanged: all six categories, three normalization identities and coefficient compositor compatibility are retained, including the distinction between equality after restriction and equality before restriction. It is an agent-extracted formal calculation from det-prop-scalar-six-pullback, proof (3), last sentence. That blueprint sentence asserts compatibility of the canonical tensor comparisons with coefficient associativity; the present item isolates the formal restricted-path computation, and does not assert a geometric or tensor construction.

I read the chapter and unit. This calculation realizes the compatibility part of unit step 2 within its existing pullback and extension-by-zero route. It neither replaces the chapter route nor needs another unit's theorem. The item is not the unit's key statement, so I changed no unit record.

DAG and whole-blueprint searches for normalized comparison, coefficient associativity, naturality and the displayed restricted-path formula found no existing node stating this item. No duplicate node is introduced. The ancestor tool confirms det-prop-scalar-six-pullback. The item's existing precise from.place is retained and same_as is empty.

## Unfinished

Nothing remains for this stage-1 split. No Lean was written or compiled. No repository or launcher file was modified.

## Review by Q11

I read the source literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md, in particular (3) and the closing compatibility sentence; also its chapter, unit and the parent normalized-immersion comparison item. This is a proof written by an agent, rather than an attributed Stacks theorem. There are no new nodes needing independent literature checks.

Step 1 uses def-nagata-category, whose statement I opened: it states the identity and associative composition laws, exactly the laws used to suppress parentheses and later cancel the explicit inverse. It is a Mathlib definition leaf. The functor composition law, the naturality equation and the meaning of an isomorphism are written out explicitly rather than inferred from that category-definition node. The citation quote is its actual statement. Subsequent steps use only hypotheses of this item and these defining equations; they cite no unrecorded theorem.

In step 2, naturality of rho^t is applied to u=t_S(M), an arrow from F_S^st(F_S^rs M) to F_S^rt M in C_S^t, and (N) for st is evaluated at V=F_S^rs M in C_S^s. In step 3, a=h^rs(M) has source F_X^rs(E^r M) and target E^s(F_S^rs M), both in C_X^s, so q^st has exactly the naturality square displayed. Step 4 applies the rs normalization at M in C_S^r and applies F_S^st to its composite, producing the claimed common value. This expands the left path instead of hiding its argument behind a new lemma.

In step 5, the rt normalization is evaluated at M, and (Q) at U=E^r M in C_X^r. In step 6, rho^r(M):L^r(E^r M) -> M is an arrow of C_S^r, exactly the domain of t_S; its naturality gives the remaining rewrite. Cancelling rho^t(W) is justified by composing with its given two-sided inverse, not by a faithfulness assumption. Step 7 writes the naturality calculation for composites and explains both whiskering operations, proving the assertion naturally in M. Every step is under 900 characters and is a direct substitution or a defining law; none hides a non-elementary sublemma. The new proof therefore supplies the missing calculation without moving either conclusion into another node.

I checked B1-B10: no new nodes; source and objects introduced; readable TeX; no invented Stacks attribution; actual Q11 searches logged with their precise queries and hits, and no attachment falsely inferred from an unrelated declaration. I read the Mathlib NatTrans and NatIso definitions: naturality is a defining field, not an additional theorem needed here. Search hits about scalar restriction, square isomorphisms and cancellation give individual primitives, not the normalized tower statement. I used a second semantic phrasing before recording no match. Existing NN search records were preserved as provenance rather than falsely claimed as Q11 searches.

For C1-C8 and D1-D5, the only node citation was checked against its statement, the other equations are supplied hypotheses or definitions written explicitly, there are no new edges capable of creating a cycle, and no off-route tool lemma is used. Every conclusion is computed, with no restatement node or appeal to a dependency's proof. For E1-E7 I checked all intermediate source and target categories as above and both orders of composition. Identity functors with identity comparison data give identities throughout; discrete or terminal categories give the unique typed maps; empty source categories give a vacuous natural equality. The calculations also work for nonfaithful L^t because only the invertible rho component is cancelled. Thus neither an unassumed faithfulness condition nor an unrestricted-path equality entered the proof. No source error or statement dispute was found.
