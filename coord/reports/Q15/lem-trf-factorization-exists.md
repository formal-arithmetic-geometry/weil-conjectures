# Worker report: lem-trf-factorization-exists

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-factorization-exists.json`: item retained as a Mathlib leaf; refreshed searches identify the exact factorization theorem and its Noetherian instance.
- `citations.json`: empty because a Mathlib leaf has no natural-language proof steps.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its factorization terminology, and the blueprint tag; no sorry-free project declaration states this item exactly. The source hits are unrelated factorization results, so no project declaration can be attached.

## WANTED

None. The source is available in `literature/stacks-project/algebra.tex`, and Mathlib supplies the result.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs.

## Findings and changes

The imported statement agrees with Stacks Tag 034R, `lemma-factorization-exists`: a domain satisfying ACC on principal ideals has irreducible factorizations. A Noetherian ring has ACC on ideals, hence on principal ideals; the Mathlib route packages this through the `IsNoetherianRing.wfDvdMonoid` instance. I retained the statement and its Noetherian definition dependency.

Mathlib's `WfDvdMonoid.not_unit_iff_exists_factors_eq` (Defs.lean:87) states that for a nonzero nonunit there is a nonempty finite multiset of irreducibles whose product is exactly the element. Enumerating that multiset gives the displayed finite product with `k ≥ 1`. Its required `WfDvdMonoid` instance is supplied for every Noetherian integral domain by `IsNoetherianRing.wfDvdMonoid` (Noetherian/UniqueFactorizationDomain.lean:23–25). Therefore this item is a Mathlib leaf and needs no split proof or child node.

## Review by Q15

I read the item node, `sec-trace-formula` chapter record, and `sk-i-curve-zero` unit record. I read Stacks Tag 034R at `algebra.tex` lines 29383–29405, including its domain hypothesis and the proof by strict enlargement of principal ideals. I also read Mathlib's `IsNoetherianRing.wfDvdMonoid` instance at `RingTheory/Noetherian/UniqueFactorizationDomain.lean` lines 23–25 and `WfDvdMonoid.not_isUnit_iff_exists_factors_eq` / alias `not_unit_iff_exists_factors_eq` at `RingTheory/UniqueFactorizationDomain/Defs.lean` lines 87–102. The Mathlib theorem supplies every clause needed: nonzero input, nonunit hypothesis, exact product, nonempty finite factor multiset, and irreducibility of every factor; nonemptiness is exactly `k ≥ 1` after enumeration. The inferred typeclasses are precisely commutative ring, integral-domain, and Noetherian hypotheses represented by the item's statement and dependency.

I ran LeanSearch, two LeanFinder phrasings, Loogle, and targeted Mathlib grep through `msearch.py`; the recorded results identify the declarations and source lines above. I also searched the DAG and blueprint for the Stacks tag and factorization statement; no duplicate node or blueprint statement exists. Since the item is a Mathlib leaf, there are no proof steps, cited node quotes, or edge-case proof obligations beyond checking the nonempty-factor and field/unit boundary encoded by the theorem.

No statement correction was needed, no new node was created, and no Lean or build tool was used.
