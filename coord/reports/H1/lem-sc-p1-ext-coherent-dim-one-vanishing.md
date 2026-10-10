1. Files written

- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-coherent-dim-one-vanishing.json`: statement, five proof steps, dependencies, and split report; non-Mathlib.
- `lem-sc-ext-sheaf-to-global-spectral-sequence`: statement node, Mathlib no match.
- `lem-sc-ext-stalk-localization`: statement node, Mathlib no match.
- `lem-sc-regular-local-ext-vanishing`: statement node, Mathlib no match.
- `lem-sc-ext-support-cohomology-vanishing`: statement node, Mathlib no match.
- `lem-sc-p1-regular-dimension-one`: statement node, Mathlib no match.

2. Attachments

None. The source checkout has no declaration tagged `(blueprint: lem-sc-p1-ext-coherent-dim-one-vanishing)` and no sorry-free declaration stating this item exactly.

3. WANTED

None.

4. Problems found

The imported item had no proof split even though its parent theorem cites it. The Stacks proof is not a one-line regularity invocation: it uses the local-to-global Ext spectral sequence, the stalk calculation, regular-local global dimension, and support-dimension cohomology vanishing. Those facts were therefore made separate statement-only nodes. The P^1 specialization also needed an explicit regular/Noetherian/dimension-one statement because the item introduces that specialization.

5. Unfinished

The five supporting nodes remain unsplit by design; each is a strictly smaller fact with a complete statement and recorded Mathlib searches.

## Review by H1

I read the item, its parent `thm-sc-p1-duality`, the unit `sk-thm-picard-duality`, and the Stacks source `equiv.tex`, Lemma `lemma-Ext-0-regular` (Tag 0FZ3), at the proof beginning around line 1657. The item statement matches part (1): regular Noetherian finite-dimensional X, coherent F and G, and vanishing for n>d. I checked the P^1 clause separately: the new `lem-sc-p1-regular-dimension-one` statement supplies exactly the regularity, Noetherianity, and dimension-one hypotheses used for the specialization.

Step 1 cites `lem-sc-ext-sheaf-to-global-spectral-sequence`; its statement explicitly gives the E2 sheaf-Ext spectral sequence and the Ext abutment. Step 2 cites `lem-sc-ext-stalk-localization` for the stalk identity and `lem-sc-regular-local-ext-vanishing` for the local Ext bound; the finite stalk hypothesis and the regular local ring hypothesis are stated in those nodes. Step 3 cites `lem-sc-ext-support-cohomology-vanishing`, whose statement is exactly the support-dimension and cohomology bound required. Step 4 uses the explicit spectral-sequence vanishing consequence included in the spectral-sequence node. Step 5 cites the P^1 regularity/dimension node. No step is marked elementary because each invokes a nontrivial cited theorem.

Before creating each node I searched all DAG nodes and the blueprint with the relevant tags and phrases. I found the existing general Noetherian cohomology node, but it does not state the support-dimension bound needed here, so I did not cite it as if it did. I searched Mathlib by LeanSearch, Loogle/semantic search, and source grep for every new statement; only abstract Ext/projective-dimension APIs appeared, with no scheme-theoretic match. I tested edge cases conceptually: d=0 makes all q>0 stalk Ext vanish and the support bound forces positive-degree cohomology to vanish; d=1 gives the required total-degree >=2 vanishing; P^1 has d=1. All citation quotes are verbatim portions of the cited node statements.
