1. files written:

   - `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-affine-denominator-module.json`: statement node, split, no direct Mathlib match.
   - `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-module-regular-from-minimal-assoc.json`: statement node, unsplit; Mathlib generalization recorded.

2. attachments: none.

3. WANTED: none.

4. The item was unsplit before this work. I checked the source proof in `/home/ubuntu/c1-stacks-review/divisors.tex`, Tag 02P2 (the proof of `lemma-make-maps-regular-section`): it reduces to an affine trivialization, defines `I={x | x(a/b) in A}`, embeds `M` in `M_b` using regularity of `b`, constructs the two maps, and ends with the two annihilation claims. No declaration tagged `(blueprint: lem-sc-hilbert-affine-denominator-module)` exists in the Lean source. The existing DAG has no duplicate for the affine module calculation. The only genuinely reusable non-elementary input is that a ring nonzerodivisor acts injectively on a finite module when all associated primes are minimal; this is recorded as the new node and tied to Mathlib's `biUnion_associatedPrimes_eq_compl_regular` generalization. I ran LeanFinder, Loogle, grep, and LeanSearch for both the item and the new node; LeanSearch was unavailable, and those results are recorded verbatim in `mathlib_searches`.

## Review by H1

I read the complete Tag 02P2 affine proof and matched each item step to its source paragraph. Step 1 checks closure of `I` under addition and scalar multiplication directly from the fraction definition, then invokes Noetherian finite generation. Step 2 uses the new node exactly for the hypotheses actually present: `a` and `b` are ring nonzerodivisors, and `M` is finite with associated primes among minimal primes; it then checks the localization construction and the fact that `(a/b)x` lies in `A` for `x in I`. Steps 3 and 4 verify separately that the first quotient is killed by `I` and the second by `(a/b)I`, as stated in the source's final sentence. I checked the new node's statement against the Mathlib search hit and kept it unsplit because the exact bridge is a short set-theoretic specialization of the cited regularity theorem. The copied item metadata, blueprint ancestor, source, and hypotheses were preserved; only proof, dependencies, status, and split report were added.

## Not duplicates

lem-sc-hilbert-module-regular-from-minimal-assoc vs lem-sc-hilbert-affine-denominator-module: the new node states only the auxiliary regularity implication for multiplication on M; the item states the denominator ideal, two maps, and cokernel annihilation.
lem-sc-hilbert-module-regular-from-minimal-assoc vs lem-sc-hilbert-nowhere-dense-dimension-drop: the new node is an affine module injectivity statement, while the existing node is a dimension drop for supports of nowhere-dense closed subsets.
lem-sc-hilbert-module-regular-from-minimal-assoc vs lem-sc-hilbert-difference: the new node concerns scalar regularity on a finite module, while the existing node proves the global Hilbert-function finite-difference identity.

## Second reading by H1

- Item statement: checked against Stacks `divisors.tex`, Tag 02P2 (Lemma 31.25.5), including the Noetherian affine reduction, denominator ideal, two maps, injectivity, and annihilation conclusions; verdict: agrees hypothesis by hypothesis.
- Auxiliary node `lem-sc-hilbert-module-regular-from-minimal-assoc`: checked against the associated-prime argument in Tag 02P2; verdict: the ring nonzerodivisor and minimal-associated-prime hypotheses give exactly module injectivity, with all notions stated self-containedly.
- Step 1: checked against the definition of `I` and Noetherian finite generation in Tag 02P2; verdict: elementary closure and finite-generation argument is complete.
- Step 2: checked against the `M \to M_b` and `\sigma` paragraphs of Tag 02P2 and the cited auxiliary statement; verdict: cited statement supplies module regularity, and the localization and denominator calculations are explicit.
- Step 3: checked against construction and injectivity of the maps `1` and `s` in Tag 02P2; verdict: the cited regularity statement supplies the only non-elementary input and the composition argument is stated.
- Step 4: checked against the first final annihilation sentence of Tag 02P2; verdict: the quotient calculation is elementary and complete.
- Step 5: checked against the second final annihilation sentence of Tag 02P2; verdict: the scalar action and quotient calculation are elementary and complete.
- New-node form and duplication audit: searched existing DAG nodes and the imported blueprint for denominator-map and module-regularity statements; verdict: no duplicate or blueprint restatement, and the auxiliary node has statement-only form with recorded Mathlib searches.
- Small cases: tested the denominator ideal and maps for a field, `A = k[t]` with `a=t`, `b=1`, and the zero module; the full-support hypothesis correctly excludes the zero module from the item, while the auxiliary regularity statement remains consistent.

Changes made: corrected the item node's `created.item` provenance to this item; corrected the auxiliary source document to `divisors.tex`, where Tag 02P2 is defined; and expanded the item statement to define the total quotient ring as localization at all non-zero-divisors. These repairs address delivery provenance, source accuracy, and self-contained statement requirements without changing the mathematical conclusion.
