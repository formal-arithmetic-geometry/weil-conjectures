## Files written

- `lem-pur-integral-braiding-naturality.json` — statement item, split with a three-step proof and no new nodes.
- `citations.json` — verbatim statement quotations for every cited node in every proof step.

## Attachments

None. No sorry-free declaration in the source checkout states this item exactly.

## WANTED

None.

## What was checked

The live item and its source place (`literature/stacks-project/sites-cohomology.tex`, Tag 0FPQ) were read, together with the current definitions of the coherently normalized integral tensor and braiding (`def-pod-integral-tensor-constraints`), the generic signed total tensor symmetry (`def-pur-ringed-site-signed-tensor-models`), and the coherent-reduction full-faithfulness lemma (`lem-pod-integral-system-reduction-fully-faithful`). The prior parent item and its use of this item were also checked; the item has no repair note, no abandoned archive, and no exact source declaration.

Step 1 uses the tensor-constraint statement only for what it says: the integral braiding is uniquely pinned by its coherent reductions and the specified tensor comparisons. Step 2 is the signed total calculation on a homogeneous bidegree: both composites are $(-1)^{ij}(b(y)\\otimes a(x))$, and the displayed signed total differential verifies that the swap is a chain map; this is the generic construction in the cited ringed-site tensor statement. Step 3 uses the same reduction-pinning sentence to identify the reductions of the two composites, then uses exactly the full-faithfulness assertion for derived-complete bounded constructible integral objects to lift their equality. The item hypotheses match that full-faithfulness domain, and no finite-field, perfectness, extra boundedness, or torsion-freeness assumption was introduced.

I checked edge cases of identity arrows, zero arrows, degree $(0,0)$ and degree $(1,1)$ homogeneous terms, and the zero object. The formula reduces respectively to the identity, zero, the ordinary swap, and the expected minus-sign swap. The existing Mathlib search log was retained; the recorded LeanFinder, Loogle, grep, and LeanSearch searches found only generic braided-category APIs and no exact completed integral coefficient theorem.

## Review by NC

I compared the live statement with the tensor-constraint definition and verified that every proof step cites a statement containing the fact it uses. In particular, the full-faithfulness citation is the exact domain needed for the lift, while the signed-total citation supplies the bidegree sign and chain-level symmetry. I verified the hypotheses on $W$, invertibility of $\\ell$ in residue fields, and the constructible integral category against all three cited statements. I corrected the initial citation quote to include the exact `$\\chi` formula from the existing signed-total statement; the final `citations.json` quotes were checked as literal substrings. No duplicate or new node was necessary.
