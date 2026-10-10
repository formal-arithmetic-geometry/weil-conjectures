1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-etale-local-ring-stalk-faithfully-flat.json`: item, statement node, split; no new nodes.
- `citations.json`: verbatim dependency quotes for all proof-step citations.

2. Attachments: none.

3. WANTED: none.

4. The imported item was unsplit even though its proof is the standard local argument in Varieties Tag 0C4Y. I retained the statement and its hypotheses. The proof now separates (i) faithful flatness of `B -> B tensor_k K`, (ii) flatness after localization at corresponding primes, and (iii) the flat-local faithful-flatness conclusion. The existing global field-extension node supplies the first step and the flat-local Mathlib leaf supplies the last; the middle step is the direct `RingHom.Flat.localRingHom`/`instFlatAtPrime` specialization recorded in the proof text. No clause was moved into a new node and no duplicate node was created.

## Review by M1

I read the item source, Varieties Lemma 33.9, Tag 0C4Y (`literature/stacks-project/varieties.tex`), and checked the statement against its setup: `k` is a field, `B` is a finitely presented `A`-algebra, `q_K` contracts to `q`, and the map is between the corresponding local rings. I also opened the cited DAG nodes `lem-weil-pbc-field-extension-base-change-faithfully-flat` and `lem-pc-local-flat-faithful-flat-reflects-surjective`. The first explicitly states faithful flatness of `D -> D tensor_K K'`, which is exactly the tensor map used in step 1 and supplies flatness in step 2. The second explicitly states that a flat local homomorphism of local rings is faithfully flat, exactly the conclusion used in step 3. The localization assertion in step 2 was checked against Mathlib search results for `RingHom.Flat.localRingHom` and `instFlatAtPrime`; its hypotheses are met because `q_K` contracts to `q`, and localization maps at corresponding primes are local. I corrected the inherited search records to the exact four `msearch.py` queries run for this item, preserving the unavailable LeanSearch result as unavailable. Small cases checked include `K = k` (identity localization map) and `B = k[x]` with a prime and its scalar-extension prime.

## Second reading by M1

- Item statement: checked hypothesis by hypothesis against Varieties Lemma 33.9, Tag 0C4Y; verdict correct for the stated affine finitely presented specialization.
- Step 1: checked the tensor map against `lem-weil-pbc-field-extension-base-change-faithfully-flat`; verdict correct.
- Step 2: checked contraction and prime localization against `lem-weil-pbc-flat-local-ring-maps` and Tag 00HT; verdict corrected to cite the existing node.
- Step 3: checked the flat-local conclusion against `lem-pc-local-flat-faithful-flat-reflects-surjective` and Tag 00HR; verdict correct.
- New nodes: none; the localization fact already exists as `lem-weil-pbc-flat-local-ring-maps`.
- Small cases: checked `K = k`, a field `B`, and `B = k[x]` with corresponding primes; all give the expected identity or localized scalar-extension maps.

Changes: added the existing flat-localization node to step 2 and `citations.json`; recorded the second-reading audit and why no new node was created.
