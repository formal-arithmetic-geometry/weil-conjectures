1. Files written:

- `sbc-def-derived-categories-with-allowable-torsion.json` (definition, split; no Mathlib match).
- `sbc-lem-p-torsion-etale-sheaf.json` (statement, unsplit; no Mathlib match).

2. Attachments: none.

3. WANTED: none.

4. The source repository has `Etale.DerivedCategory.Plus.torsionHomologyOfPrimes` and `boundedTorsionHomologyOfPrimes`, but these are coefficient-module ObjectProperty definitions and do not by themselves state the blueprint's full pair of bounded and bounded-below full subcategories of abelian étale sheaves. No sorry-free declaration states the complete item exactly. The split introduces only the underlying P-torsion sheaf predicate and leaves the category construction as the item's definition.

## Review by NG

I read the blueprint node `sbc-def-derived-categories-with-allowable-torsion` and the unit record `sk-rem-rest`, then checked the source declarations and docstrings in `WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/TorsionSheaf.lean` (the `torsionHomologyOfPrimes` definition at lines 490–496 and the `Scheme.IsTorsionSheafOfPrimes` class at lines 507–513) and `SmoothBaseChange/Derived.lean` (the bounded intersection at lines 238–241). The existing `def-weil-pbc-derived-categories` node supplies D, D⁺ and Dᵇ, while `def-weil-pbc-geometric-stalks` supplies the stalk notion. The new statement records exactly the stalkwise positive annihilator and prime-divisor condition used by the source class; no proof steps or citations are needed for a definition node. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches; Mathlib had no matching torsion-sheaf notion, and LeanSearch was unavailable. I checked edge cases conceptually: the zero stalk satisfies the condition using n=1, and an element killed by n=1 has no prime divisors, so the definition does not accidentally exclude zero objects.

## Second reading by NG

- Item definition (no proof steps): read the exact blueprint file `sec-smooth-base-change/sk-rem-rest/sbc-def-derived-categories-with-allowable-torsion.md`, the unit `sk-rem-rest`, and the complete statements of `def-weil-pbc-derived-categories` and `def-weil-pbc-geometric-stalks`. Verdict: all original hypotheses and both boundedness clauses preserved; made T explicit and cited the definitions providing the ambient categories, cohomology, and stalks.
- New node `sbc-lem-p-torsion-etale-sheaf`: read `Scheme.IsTorsionSheafOfPrimes` at TorsionSheaf.lean:197–202, `torsionHomologyOfPrimes` at :490–495, and boundedTorsionHomologyOfPrimes at SmoothBaseChange/Derived.lean:238–241, in the read-only slopmaster2 source. Verdict: it merely defines the stalkwise predicate already used in the item's sole clause; removed it and put the positive-annihilator condition explicitly in the item (D1), leaving no new nodes.
- Citations: no proof steps or proof citations; citations.json remains [] correctly. Statement dependencies define precisely D, Dᵇ, D⁺, H^q, geometric points and geometric stalks.
- Edge cases: zero objects satisfy the condition with n=1; P empty forces each stalk element to be zero because n has no prime divisors only when n=1; over a field Z/p qualifies exactly when p is in P; empty schemes impose no additional condition. No uniform annihilator is asserted. Boundedness means cohomological boundedness, as the existing derived-category node specifies.
- Whole-blueprint/DAG searches: `tools/blueprint_refs.py ancestor` confirms the item is its own nearest blueprint ancestor; `search torsion` and DAG keyword searches found the ambient derived-category and stalk definitions but no independent duplicate of this pair of subcategories. Read the blueprint itself, not a fictitious Stacks tag; source is this blueprint definition. Searched Stacks etale-cohomology.tex for the related stalkwise torsion wording, which concerns invertible orders and is not the arbitrary-P definition here.
- Independent Mathlib searches: LeanFinder `torsion abelian group elements annihilated integers prime factors set` returned additive torsion/exponent and torsionBy declarations, not the sheaf predicate; Loogle `"IsTorsion"` returned module torsion-free notions; grep `torsion.*prime|prime.*torsion|IsTorsionSheaf` returned algebraic torsion decompositions and the TODO in GroupTheory/Torsion.lean:38 to generalize to sets of primes. No Mathlib leaf for the complete category definition. Searches are recorded verbatim by msearch.py in searches.jsonl.

Changed: removed the clause-restating auxiliary node (and its dependency), expanded its elementwise condition directly in the item, introduced T explicitly, and cited the existing ambient definitions. The original worker sections, including Review by NG, are retained above; their auxiliary-node discussion describes the superseded first draft. Corrected that review's line reference: the torsion-sheaf class is at :197–202, not :507–513 (which defines the full subcategory).
