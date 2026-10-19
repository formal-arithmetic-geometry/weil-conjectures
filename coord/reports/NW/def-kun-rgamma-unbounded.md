# Stage-1 report: def-kun-rgamma-unbounded

Files written:

- `dag/nodes/sec-smooth-purity/def-kun-rgamma-unbounded.json` — definition, split, no new nodes.

Attachments: none. The earlier proposed attachment was rejected after checking the exact statement.

WANTED: none.

## Source error

The prior sandbox report attached `AlgebraicGeometry.Etale.rightDerivedGlobalSections` and `AlgebraicGeometry.Etale.cohomology`. This is not an exact attachment: at lines 227–236 of `WeilConjectures/SixFunctors/Etale/Derived/LowerShriek.lean`, those declarations require an arbitrary Grothendieck abelian category `A` and define categorical functors `R(Sheaf.Γ ...)` and its homology. The item instead introduces a commutative ring `\Lambda`, a complex `K`, an explicitly chosen K-injective resolution `K\to I`, and the objectwise formula `\Gamma(T_{\Et},I)`. The generic declarations therefore do not state every clause under the item's hypotheses.

## Review by NW

I read the item blueprint at `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-rgamma-unbounded.md`, the unit record, and the three cited DAG nodes. The item’s statement uses exactly the definitions of K-injective resolutions, their existence, and étale cohomology represented by `def-weil-pbc-kinjective-resolutions`, `prop-weil-pbc-kinjective-resolutions-exist`, and `def-weil-pbc-etale-cohomology`; no additional proof fact is needed for a definition, so there are no proof steps or citations. I searched the whole blueprint for duplicate definitions and found none. Mathlib searches (LeanFinder, Loogle, grep, and unavailable LeanSearch) found only generic K-injective, global-sections, and derived-homology APIs, so the item is not a Mathlib leaf. I checked the source declarations and their hypotheses and corrected the earlier mistaken attachment. The node is now marked `split`, with the three existing statement dependencies retained and no new node created.

## Second reading by NW

- Item statement: checked clause by clause against the blueprint node `def-kun-rgamma-unbounded` (order 1661), including arbitrary scheme, commutative coefficient ring, unbounded derived object, chosen K-injective resolution, the two displayed formulas, and the deferred independence and bounded-below agreement; verdict: faithful and self-contained.
- Definition dependencies: checked `def-weil-pbc-kinjective-resolutions` for the meaning of K-injective resolution, `prop-weil-pbc-kinjective-resolutions-exist` for existence, and `def-weil-pbc-etale-cohomology` for the bounded-below étale construction; each cited statement supplies exactly the referenced notion under the stated hypotheses.
- Proof steps: there are no proof steps because this node is a definition; consequently there are no uncited non-elementary facts or citation quotations to repair.
- New nodes: none; the duplicate search covered the full blueprint and DAG, and the existing dependency nodes were reused rather than restated.
- Edge cases: the definition permits the zero complex, a field as coefficient ring, and arbitrary schemes (including the empty scheme); no finiteness, boundedness, or nonzero hypothesis was introduced.
- Source/attachment audit: the source blueprint text was read in full and the slopmaster2 declarations `rightDerivedGlobalSections` and `cohomology` (LowerShriek.lean lines 224–236) were checked hypothesis by hypothesis; they are generic derived functors and do not state this explicit ring/K-injective definition, so no Lean attachment is appropriate.

Changes made in this second reading: no node or citation changes; appended this audit and retained the correction rejecting the earlier generic Lean attachment.
