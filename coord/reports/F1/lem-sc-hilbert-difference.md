1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-difference.json` — statement, split proof, and three supporting citations.
- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-affine-denominator-module.json` — statement-only auxiliary; Mathlib searches found no exact match.
- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-denominator-ideal-nowhere-dense.json` — statement-only auxiliary; Mathlib searches found no exact match.
- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-nowhere-dense-dimension-drop.json` — statement-only auxiliary; Mathlib searches found no exact match.
- `citations.json` — verbatim statement excerpts for every proof dependency.

2. Attachments: none. No sorry-free declaration in `WeilConjectures/` states the item or any of the three new auxiliaries.

3. WANTED: `literature/stacks-project/divisors.tex`, Tags 02P0 and 02P2, for the denominator-ideal and affine denominator arguments.
WANTED: `literature/stacks-project/varieties.tex`, Tag 0BEM, for the Euler forward-difference identity.
WANTED: `literature/stacks-project/coherent.tex`, Tags 01XZ, 01Y0 and 01Y1, for coherence and kernel/cokernel closure.

4. No statement error was found. The imported item had an empty proof; I retained its statement and made the affine reduction explicit. The source's omitted affine reduction is the first auxiliary node, and the denominator-ideal lemma it invokes is the second. The dimension claim is made explicit in the third auxiliary rather than being hidden behind “nowhere dense”.

5. Nothing remains unfinished in the split. The literature source files are not checked into this repository, so the WANTED entries above record the source gap; the Stacks pages were checked externally against Tags 02P0 and 02P2.

## Not duplicates

lem-sc-hilbert-affine-denominator-module vs lem-sc-hilbert-difference: the new node is the affine A-module calculation for a/b, with annihilator conclusions, while the item is the global sheaf statement including coherence, support dimensions, and the Euler-characteristic identity.
lem-sc-hilbert-nowhere-dense-dimension-drop vs lem-sc-hilbert-difference: the new node is the general topological dimension lemma for a nowhere-dense closed subset, while the item constructs two specific cokernels and proves the forward-difference formula.

## Review by F1

I read the item, its parent proof in `lem-sc-hilbert-polynomial`, the unit record `sk-def-av-ample-degree`, and the Stacks statements for Tags 02P0 and 02P2. Tag 02P2's affine proof writes a regular meromorphic section as `a/b`, uses full support and absence of embedded associated primes to make `a` and `b` nonzerodivisors on the module, and obtains the two injective maps with annihilating ideals. That is exactly the content of the new affine denominator-module statement. Tag 02P0 gives the denominator ideal's quasi-coherence and the two ambient nowhere-dense cokernel supports; this is the second new node. The third node states the finite-dimensional Noetherian dimension argument needed to turn nowhere-dense support into a strict dimension inequality.

For item step 1, I checked that the affine auxiliary supplies precisely the two local injections and annihilators, while the denominator-ideal auxiliary supplies quasi-coherence and the closed nowhere-dense ambient supports; the local maps agree on overlaps, so the gluing is elementary. Step 2 uses `pqf-lem-coherent-ft-locnoeth` for quasi-coherent finite-type modules, `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` for the product, `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` for coherent cokernels, and the invertible-module definition for local finite freeness. I opened each cited statement and verified those clauses are present. Step 3 uses the two new support statements exactly as quoted in `citations.json`; the hypotheses nonempty, locally Noetherian, and finite-dimensional match the item. Step 4 uses the existing exactness of tensoring by finite locally free modules and Euler additivity; tensoring the two short exact sequences by `L^n` gives the displayed sign after cancellation of the common `I F tensor L^n` term.

I tested the new statements on the basic cases `A = k[t]`, `a=t`, `b=1`, `M=A` (both maps are multiplication by `t` and the cokernel is supported at `(t)`), and `A=k`, where the denominator ideal is the unit ideal and both cokernels vanish. The no-embedded-primes and full-support hypotheses are necessary: for `A=k[epsilon]/(epsilon^2)` and `M=A/(epsilon)`, the ring nonzerodivisor condition does not give the required module behavior. I also searched the DAG and blueprint for denominator ideals, regular meromorphic sections, and nowhere-dense dimension statements; no duplicate node or blueprint statement was found. Mathlib searches were run and recorded on every new node, with LeanSearch marked unavailable where the service returned an internal error.

## Second reading by F1

- Item statement: checked against Stacks Tags 02P2 and 0BEM and the imported parent statement; hypotheses and the forward-difference sign agree.
- Step 1: checked the affine `a/b` calculation and gluing against Tag 02P2; the two injections and annihilators are exactly supplied by the affine node and denominator-support node.
- Step 2: checked coherence against Tags 01XZ, 01Y0, and 01Y1; finite generation of the denominator ideal on affine Noetherian charts and coherence of `I F` are now stated explicitly.
- Step 3: checked annihilator support and strict dimension drop against Tag 02P2 and the finite-dimensional Noetherian argument; both support inclusions use the stated hypotheses.
- Step 4: checked tensor exactness and Euler additivity against the existing nodes and Tag 0BEM; tensoring by `L^n` and cancellation give the displayed identity.
- Auxiliary affine node: checked definitions, the nonzerodivisor hypotheses, ideal finite generation, injections, and annihilators against Tag 02P2; small cases `k[t]` and `k` behave as stated.
- Auxiliary denominator node: checked quasi-coherence, injectivity, and nowhere-dense support against Tag 02P0; the zero and unit denominator cases are consistent.
- Auxiliary dimension node: checked the nonempty locally Noetherian finite-dimensional hypotheses and the strict inequality on proper closed subsets; no Mathlib declaration or duplicate DAG node was found.

Changes made: corrected the Tag 02P2 label from 31.5.9 to 31.25.5; added the ideal/finiteness clause to the affine auxiliary; repaired Step 2 to establish coherence of `I F` before applying coherent kernel/cokernel closure; synchronized the citation quote with the repaired node.
