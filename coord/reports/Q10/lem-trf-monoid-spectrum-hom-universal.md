# Stage-1 report: lem-trf-monoid-spectrum-hom-universal

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-monoid-spectrum-hom-universal.json`: statement, split; Mathlib no match. The statement is unchanged. Four proof steps, 2117 characters total, none exceeding 2000 characters.
- `citations.json`: a verbatim statement quote for each of the five step/node citation pairs.
- `report.md` and the search command's `searches.jsonl`.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searches in the live `lean/WeilConjectures/` and `lean/Sheaf/` for the item id, ordinary monoid spectrum, and the defining notions found no declaration giving this statement. No Lean was written and no compiler was run.

## WANTED

None. The required ILO source is present locally.

## Findings and changes

The imported item had no proof. Its bijection, including naturality, is already stated by the existing `lem-trf-affine-monoscheme-hom-universal`, created by Q06 from ILO VIII Lemma 3.1.8(i). The present item additionally specifies the image prime and the localized stalk homomorphism. I reused that existing node for the bijection rather than creating a second universal-property node. The explicit formulas are proved here; they are not moved into new nodes. No statement dispute or hypothesis correction is needed.

The ordinary stalk computation uses `lem-trf-monoid-prime-minimal-neighborhood`, not the sharpened localization lemma: the latter's statement gives quotient stalks and would not supply the ordinary stalk needed here. The minimal-neighborhood statement gives the smallest open D(b), the equality P_b=P-F, and the precise unit criterion. Sections over that smallest open are the stalk directly by the definition of germs.

I read the current latest blueprint's ancestor `lem-trf-local-term-locality.md` and `.proof.md`, and the unit/chapter records. The latest ancestor uses contracting correspondences; the item's recorded provenance is explicitly the historical alteration branch. This item remains the assigned local affine-functoriality input, and I do not change the ancestor, chapter, or unit route. All cited statement nodes are in the item's own unit. The item is not its unit's key statement, so no realization fields are changed.

The inherited Mathlib searches are retained. Five fresh searches were run with the prescribed command (LeanFinder twice, LeanSearch, Loogle, and grep), and their exact logged queries and results were appended. I read the returned GammaSpecAdjunction source: its objects are locally ringed spaces, and its target category is commutative rings (lines 63--76 and 331--340). The ring spectrum adjunction does not specialize to sheaves of arbitrary commutative monoids. Neither Loogle nor the source grep found the monoidal-space notions. The result is not a Mathlib leaf.

## Not duplicates

No new nodes. `lem-trf-monoid-spectrum-hom-universal` vs `lem-trf-affine-monoscheme-hom-universal`: the natural bijection is shared, so the existing node is cited; this item also asserts the point-prime and stalk-fraction formulas, which the existing statement does not display. `lem-trf-affine-fan-localization-sections` concerns the sharpened quotient sheaf and cannot replace the ordinary-stalk calculation. Searches of the whole DAG by monoid-spectrum terminology, local homomorphisms and ILO 3.1.8, and whole-blueprint searches by monoid and spectrum/hom/universal found no imported blueprint node with this monoidal universal property. The latter is therefore not added to `same_as`.

## Review by Q10

I read ILO, Expose VIII, printed pp.98--99 (PDF pp.104--105): localization in 3.1.2, the ordinary structure sheaf in 3.1.3, neighborhoods in Remark 3.1.4, local homomorphisms in 3.1.5, monoidal morphisms in 3.1.6, and Lemma 3.1.8(i) with its proof. Its proof constructs the prime as the complement of the inverse image of units and the unique local localization map. It imposes no sharpness condition in (i); (ii) is a different, sharpened assertion. No SGA source is used, and no Stacks tag states this monoidal-space result.

For Step 1 I opened the full statement of `lem-trf-affine-monoscheme-hom-universal`. It permits an arbitrary topological space and arbitrary sheaf of commutative monoids and the same local-stalk convention. It explicitly supplies the natural bijection by pullback of canonical sections. Our P is fine and integral; fineness in that node already includes integrality. Consequently the application has every required hypothesis, including allowing nonsharp and torsion monoids. This is an existing node, not a new restatement of the item.

For Step 2 I opened `lem-trf-monoid-prime-minimal-neighborhood` and `def-trf-fine-fan-blowup`. The former's statement supplies exactly the finite-generator construction of D(b), its minimality, P_b=P-F, and p being a unit in P-F iff p belongs to F. The latter states that ordinary sections on D(b) are P_b and defines germs and the canonical localization restrictions. Restricting any germ representative to the smallest neighborhood gives the claimed ordinary stalk; equality of germs restricts there too. This is a short argument from those statements, not an unsupported use of a sharpened-sheaf computation.

Step 3 uses the local-homomorphism definition in `def-trf-fine-fan-blowup`: inverse images of units are precisely units. Canonical-section pullback commutes with germs by the restriction-compatible morphism definition. Step 2's criterion identifies that inverse image with P minus h(t), giving the precise asserted prime. No local-ring theorem is being used for a monoid.

Step 4 uses only the preceding computation and additivity: f and -f sum to zero in the localization, hence their images are mutual inverses. Applying the existing stalk map to p-f proves the displayed formula, so there is no unjustified descent of a formula through a fraction equivalence. Its existence and locality come from Step 1, and every fraction is covered by Step 2. Naturality is already expressly part of Step 1's cited statement.

I checked B--E against these files: all uses have verbatim quotes, no proof-only data from a cited node is used, no new node needs searches or a separate source, and proof_deps is exactly the union of uses. A read-only dependency traversal of every cited node's statement/proof closure finds no path back to the item, so reusing the universal-property node introduces no cycle. None of the steps hides a new lemma or exceeds 2000 characters.

For small cases, T empty gives one morphism and one homomorphism to the one-element section monoid. P={0} and any finite abelian group P give a one-point spectrum with empty prime and only invertible canonical germs; torsion causes no failure. For P=N, the two primes distinguish whether the generator's germ is invertible, as claimed. For the fine nonsaturated monoid generated by 2 and 3 in N, minimal neighborhoods and P-F still compute the ordinary stalk without saturation. Nonsharp target stalks are allowed throughout: units are tested as units, never replaced by zero. No hypothesis on integrality of the target stalk is used, because Step 4 applies its actual stalk homomorphism rather than embedding that stalk into a group completion.

## Unfinished work

None in the stage-1 split. The existing universal-property dependency retains its own separate stage-1 work; this delivery neither modifies nor pretends to prove it.
