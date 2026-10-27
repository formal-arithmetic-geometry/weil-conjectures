# Q74 — lem-trf-cm-affine-associated-generic

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cm-affine-associated-generic.json`: statement, split; no exact Mathlib match. Four proof steps, using existing nodes only.
- `citations.json`: ten verbatim statement quotations, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's actual log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the item's id, Cohen–Macaulay terminology, associatedPrimes, and associated/minimal combinations. The local theorem `Ideal.mem_minimalPrimes_of_depth_ge` in `WeilConjectures/RingTheory/AssociatedPrimeMinimalOfDepth.lean` proves only the local algebra ingredient, and already belongs to `lem-weil-pbc-cm-local-associated-prime-minimal`. It does not state this item's affine-stalk equivalences and is not an attachment for this item.

## WANTED

None: every source used is present in the read-only repository.

## Errors and corrections

The imported item is true as stated; no statement, hypothesis, or definition was changed. The empty proof and dependency list have been replaced by a checked proof. The initial source mentions 0BUS, 05BV, and 05BZ; the split makes the necessary stalk, Noetherian-localization, finite-dimensional-local-ring, prime-localization, and spectrum-component results explicit. In particular, finite dimension is not inferred merely from a general Noetherian ring: it is applied only to the local ring at the specified prime.

The item's existing blueprint provenance is retained. Read the current `main-20261015` locality node and the chapter/unit records. This is a generic algebra lemma inherited through the nearby-cycle/semistable branch and 05DC; it neither replaces a unit step nor asserts that the current locality node itself explicitly states this algebra lemma. Whole-blueprint searches for associated/minimal, Cohen, and generic points yielded no blueprint node stating the item. All the actual algebra and topology ingredients already exist in the DAG.

## Not duplicates

No new nodes are proposed. Reused, rather than duplicated: the local Cohen–Macaulay associated-prime theorem (0BUS), the minimal-prime associated-prime leaf (05BV), the localization leaf (05BZ), the prime-localization correspondence (00E3), the finite-dimensional local-ring leaf (00KQ), the Noetherian localization leaf (00FN), the affine-stalk leaf (01HV), and the affine component leaf (00ES). The existing `lem-trf-affine-minimal-prime-stalk-annihilator` covers the direction (ii) implies (i), so it was not recreated; the split instead gives that direction using its existing algebra ingredients. It does not state the Cohen–Macaulay converse or the three-way equivalence.

## Review by Q74

I read Stacks `divisors.tex` Tag 05DC, especially its final associated-prime paragraph, and `algebra.tex` Tags 0BUS (lemma-CM-ass-minimal-support), 05BV (lemma-ass-minimal-prime-support), 05BZ (lemma-localize-ass), 00E3 (lemma-spec-localization), 00ES (lemma-irreducible), 00FN (lemma-Noetherian-permanence), and 00KQ (proposition-dimension and its following finite-generator bound). I also read `schemes.tex` Tag 01HV, part (6). The tag/label correspondences were checked in `tags/tags`. There are no new-node sources to review.

For step 1 I opened the statements of `lem-weil-pbc-spec-domain-stalks-function-field` (its first clause applies to every commutative ring despite its title), `def-weil-pbc-localization-at-prime`, `lem-weil-pbc-localization-noetherian`, and `lem-weil-pbc-noetherian-local-finite-krull-dimension`. They give exactly the stalk isomorphism, local maximal ideal, Noetherianity and finite dimension used here. The multiplicative set is the complement of the given prime. Ring isomorphisms preserve units and annihilators directly, so the associated-point condition becomes the annihilator condition in the local ring. No field/domain hypothesis from the stalk node's second clause is used.

For step 2 I opened `lem-weil-pbc-cm-local-associated-prime-minimal` and `lem-weil-pbc-primes-of-localization`. The former requires a Noetherian local ring of finite dimension e, depth at least e, and an associated prime. Step 1 supplies all of these, with the associated prime equal to the maximal ideal. The latter gives an inclusion-preserving bijection, with extension inverse to contraction, so a prime strictly below q gives a prime strictly below qA. This is precisely the contradiction needed; I did not silently use the converse localization of association or a global Cohen–Macaulay theorem.

For step 3 I opened `lem-weil-pbc-noetherian-minimal-prime-associated` and `lem-weil-pbc-associated-prime-localization-depth-zero`. They give an annihilator element globally and then locally under exactly the Noetherian and prime hypotheses at hand. Despite the second node's title, its statement gives the local annihilator witness itself, which is all the step uses. That element cannot be zero because its annihilator is a proper maximal ideal. Step 1's ring isomorphism then gives the requested stalk witness.

For step 4 I opened `lem-weil-pbc-spec-irreducible-components-minimal-primes` and `def-sc-generic-point`. The former states exactly the classification of components by minimal primes; the latter defines genericity by singleton closure. The closure formula is proved inline from the defining sets V(I), not smuggled in as a theorem stated by a definition node. Equality V(q)=V(p) for two primes forces equality of the primes by evaluating membership at p and q. This checks the converse generic-point direction as well.

The only off-unit non-leaf ingredient is the local Cohen–Macaulay theorem. Its generic-tool use is declared in `split_report.tool_uses`; it supplies the algebra in the inherited 05DC route and changes no unit route. Every other theorem cited is an existing Mathlib leaf. The citations file copies whole statements verbatim, preventing a quotation from suggesting a stronger assertion than a cited node contains.

I tested the statement on the zero ring (empty spectrum, hence vacuous), a field (one associated minimal generic point), k[x] (only the zero prime is associated; closed points fail (i)), k[epsilon]/(epsilon^2) (nonreduced but Cohen–Macaulay of dimension zero), and a product of fields (one component per factor). The non-Cohen–Macaulay ring k[x,y]/(x^2,xy) has the embedded associated prime (x,y), showing that dropping the local Cohen–Macaulay hypothesis would invalidate the converse. Each proof step is under 800 characters and carries a single application or routine argument; none exceeds the 2000-character review threshold or hides a new independent lemma. I checked delivery-errors B–E against the actual statements and sources: no restated-clause nodes, no cycle introduced, no missing non-elementary dependency, no unsupported C4 citation, and no SGA route.

The search log records actual LeanFinder, Loogle, grep, and LeanSearch calls, including a second semantic phrasing. I read the returned signatures: the component theorem and minimal-prime inclusion are ingredients, not exact matches for the item. Read the relevant Mathlib source at AssociatedPrime/Localization.lean:128 and Spectrum/Prime/Topology.lean:1267. Existing search records from the item were retained and current command results appended with their actual query texts and digests.

## Unfinished work

None for this one-level stage-1 split. Its existing dependencies remain responsible for their own stages. No Lean was written or compiled, and no repository or launcher file was changed.
