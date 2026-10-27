# Stage-1 report: lem-per-g-ring-finite-domain-generic-test

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-g-ring-finite-domain-generic-test.json`: unchanged statement; split into six proof steps; new searches appended to the inherited searches.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-semilocal-jacobson-completion-product.json`: statement-only comparison lemma, unsplit; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every node cited by every item step.

One new node, zero Mathlib leaves. The new node has an actual isomorphism with its algebra compatibility, not an assertion of regularity or a clause of the item's equivalence.

## Attachments

None. I searched the exact blueprint tag and the G-ring, finite-domain, semilocal and generic-formal-fibre notions in `lean/WeilConjectures/`. `GRingPairsOfPrimes`, `GRingCompletionRegular`, `GRingNagata` and `FiniteTypeGRing` concern inputs or different criteria, not this complete equivalence. Their presence is not an attachment for the item. No Lean was written or compiled.

## WANTED

WANTED: Matsumura, Commutative Algebra, (33.E), as cited by Rotthaus (1979), for the historical proof of the criterion. Neither a local Matsumura copy nor a local Rotthaus copy was found in the named literature directory. This does not block the supplied proof: I read Rotthaus pp.173–174 directly from the item's Cambridge PDF URL, and read the complete proofs of Stacks 07PQ and 07PT locally. The proof is explicitly agent-written because Rotthaus states the criterion by reference, while the available Stacks criterion has a different finite-free hypothesis.

## Issues found

The imported statement agrees with Rotthaus Lemma 1(a)–(b), p.174. Her p.173 definition of “quasiausgezeichnet” means geometrically regular formal fibres, hence G-ring here, and does not silently add a J-2 hypothesis. The notation for the completed semilocal domain and localization above zero agrees as well. There is no statement dispute or change.

Stacks 07PQ is not this statement: it tests all formal fibres of finite free algebras. I did not cite it as a node proving the desired implication. Instead I adapted its finite-model and completed-factor argument, using the existing finite-extension completion theorem and a separate semilocal completion comparison. In particular I did not replace the condition with regularity only over injective finite extensions, nor confuse an ordinary regular fibre with a geometrically regular one. Testing every finite domain algebra provides the purely inseparable base changes needed for the latter.

The current blueprint ancestor and unit were read. The exact item is a created algebra tool on the existing local G-ring adic lifting chain below `lem-per-artin-gabber-affine-curve`; it is not an imported Fourier or perverse theorem. The current ancestor proof contains no explicit Rotthaus argument. The preserved `blueprint.from` chain and its refined place identify that inherited algebra input. Searches with `blueprint_refs.py` for G-ring, semilocal, Jacobson radical, Jacobson completion, semilocal completion and finite completion found no blueprint node stating the new comparison. Searches of the whole DAG by 07N9 and completion/maximal-ideal keywords found the finite-extension and finite-quotient comparisons distinguished below.

## Unfinished

No portion of the item's split remains unfinished. The one new comparison is intentionally statement-only and joins stage 1; its future proof is described below without putting a proof in its node. Searches were run with the prescribed `msearch.py`, and their exact responses are retained in `search-results.jsonl`, alongside the tool's unmodified `searches.jsonl`. Both semantic services and Loogle responded successfully. Mathlib's `AdicCompletion.piEquivOfFintype` (Functoriality.lean, around lines 316–324) concerns completion of an already given product at one fixed ideal. `Ideal.quotientInfRingEquivPiQuotient` concerns a finite CRT quotient. Neither states the completion-at-Jacobson-radical comparison with completed localizations.

## Review by Q31

I read Rotthaus, *Komplettierung semilokaler quasiausgezeichneter Ringe*, Nagoya Math. J. 76 (1979), pp.173–174, from the Cambridge PDF in the item. Page 173 specifies the terminology and the Jacobson-adic convention, and Lemma 1 on p.174 states the exact finite-domain test and notes the local-to-semilocal passage. For the proof I read `more-algebra.tex`, `lemma-check-G-ring` (07PQ), `lemma-check-G-ring-maximal-ideals` (07PT), and the G-ring definition (07GH). For the new comparison I read `algebra.tex`, `lemma-completion-finite-extension` (07N9), especially its quotient-product/inverse-limit argument, and the Chinese remainder lemma (00DT). This is an algebra lemma with a genuine completion isomorphism, not a renamed implication of the item.

For step 1 I opened the statements of `lem-weil-pbc-finite-algebra-noetherian`, `lem-weil-pbc-finite-algebra-is-integral`, `lem-weil-pbc-integral-extension-dimension`, and `lem-weil-pbc-completion-finite-extension`. They respectively give Noetherianity, integrality, contraction of maximal ideals, and finiteness of primes over each prime. Only that last finiteness clause, not a claim about an arbitrary semilocal completion, is taken from 07N9 here. This checks the parenthetical semilocal assertion without injectivity. The zero ring is handled using the definition of G-ring; it admits no unital algebra structure on a nonzero domain.

For step 2 I read the finite-type ascent and arbitrary ideal-completion regularity nodes. Finite module generators also generate the algebra, so the finite-type hypothesis is satisfied. The completion theorem works for the Jacobson radical itself. Its statement gives a Noetherian geometrically regular fibre at zero; the trivial extension in the geometric-regularity definition gives ordinary regularity. The localization/base-change node identifies that fibre with inversion of nonzero elements. The displayed fraction maps, and the definition of a regular ring, then give exactly the local ring required by the item. There is no assumption that completion itself is a regular ring.

Step 3 keeps the finite-model construction in the item's proof. The only non-elementary input to finiteness is the existing finite-integral-generators leaf, followed by the finite-module transitivity leaf. Pure inseparability gives the displayed powers of each basis element; multiplying by a common denominator produces monic equations over A. The model B is an actual subring of the field L, so it is a nonzero domain. It is finite over R although the map R to B has kernel q. The proof that its fraction field is L is written out. In characteristic zero the construction reduces to A itself. I did not use a normalization-finiteness theorem, which would need an unwarranted Nagata assumption.

For step 4 I checked the statements of completion Noetherianity, localization/base-change and localization Noetherianity. They provide all ring-finiteness conditions used. Primes of the generic fibre are exactly the primes covered by the hypothesis, and the local-ring isomorphism was already written in step 2. The new node gives an isomorphism of B-algebras, so localizing its factors uses the same denominator set B minus zero. The finite common-denominator argument and coordinate-idempotent argument justify the localization/product and regularity assertions. This step never claims the new node itself proves regularity.

For step 5 I reread the full algebra-compatibility clause of `lem-weil-pbc-completion-finite-extension`; this matters because it is then tensored over B with L. R is Noetherian, B is finite over R, and m is prime. A prime above m is maximal by the elementary monic-inverse argument written in the step, so every factor was covered in step 4. Tensor cancellation is exactly the statement of the cited Mathlib leaf. Finite localization/product and coordinate ideals give the regular product, including a zero factor or an empty product. No infinite-product assertion is used.

For step 6 I checked `lem-weil-pbc-fibre-ring-noetherian`: it assumes only that the target is Noetherian, which has been established for H. The geometric-regularity definition tests all finite purely inseparable extensions, precisely those constructed in step 3. I expanded the localization prime and residue-field correspondence rather than concealing it in “transport”; extension/contraction and the fraction formula identify each fibre of the local completion with H tensor kappa(q). The completion flatness node applies because R localized at m is Noetherian. Finally the maximal-ideal criterion says exactly that these regular local completion maps suffice for a G-ring. All cited statements were reread, and `citations.json` copies their actual statement text verbatim.

I checked small cases: a field (the semilocal completion is itself), a product of two fields (the comparison is the two coordinate projections), a local ring with nilpotents (the one-factor comparison does not assume reducedness), and a domain with two maximal ideals such as Z localized away from the union of (2) and (3), whose Jacobson completion is the product of its two completed localizations. The empty-maximal-spectrum case is the zero ring and gives the empty product, hence the zero ring on both sides. For the item, R=k[epsilon]/(epsilon^2) and B=k tests the permitted noninjective algebra maps. In characteristic p, K=F_p(t) and L=K(u), u^p=t, tests the integral-multiple construction without a perfect-field assumption. No characteristic, catenarity, excellence, normality, or injectivity assumption entered the proof.

Against delivery-errors B–E: the new node is self-contained, has its three definition dependencies, an actual literature place and fully logged searches; it has no proof. Existing same-tag nodes were opened and are distinguished below. Each item step names every non-elementary input and uses its statement, not its proof. The new comparison does not restate the item and has no dependence on it. The finite-model and finite-product elementary calculations stay in the proof. Every step is under 2000 characters. Cross-unit commutative-algebra tools are declared in `split_report.tool_uses`; they realize the existing adic-lifting branch and replace no unit-level route. I changed no maintainer fields and wrote only in the sandbox.

The future proof of the new comparison is the CRT construction, which is not included in its statement: for distinct maximal ideals, their powers are pairwise comaximal. With J their finite intersection, J is their product, hence J^n is the intersection of their nth powers. CRT identifies A/J^n with the product of A/m_i^n. Every element outside m_i is a unit modulo m_i^n: choose an inverse modulo m_i and correct its nilpotent error with the finite geometric series. Thus A/m_i^n equals the corresponding localization quotient. These quotient isomorphisms commute with reduction in n. Taking compatible sequences coordinatewise gives the claimed A-algebra isomorphism, including its stated structural maps. This comparison, involving different ideals and localization on each factor, is not a one-line instance of Mathlib's fixed-ideal product equivalence.

## Not duplicates

lem-per-semilocal-jacobson-completion-product vs lem-trf-normalized-curve-branch-coordinates: requires a normalized curve over an algebraically closed field and gives DVR/power-series coordinates; ours allows any Noetherian semilocal ring and gives only its completion product.

lem-per-semilocal-jacobson-completion-product vs lem-sfb-finite-formal-quotient-pullback: is descent of a finite representable stack pullback over a complete local quotient chart; ours is an ordinary semilocal ring completion isomorphism without stack data.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-at-quasi-finite-prime: assumes a finite-type map and quasi-finiteness at a selected prime, and splits one completed tensor factor; ours has no base ring map and decomposes a Jacobson completion over all maximal ideals.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-finite-quotient-data: requires a monic polynomial quotient finite over a Noetherian local ring and constructs its completed tensor map; ours is not restricted to such quotients or a local base.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-localized-algebra-product-surjective: proves only surjectivity for a prescribed map from completion of a localized finite algebra; ours constructs the full algebra isomorphism for an arbitrary Noetherian semilocal ring.

lem-per-semilocal-jacobson-completion-product vs new-lem-weil-pbc-finite-model-formal-fiber-derivation-extension: extends derivations to a generic formal fibre under a normal-domain hypothesis; ours has no derivation, normality or fraction-field hypothesis.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-tensor-local-maps-injective: gives injectivity of a specified completed-tensor comparison for a finite algebra over a localized base; ours gives the Jacobson-completion isomorphism without a chosen finite base.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-local-tensor-quotient-power-bound: bounds powers of maximal ideals by the extended ideal of a localized base; ours identifies the full semilocal completion and has no chosen base ideal.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-tensor-local-maps-surjective: gives surjectivity of a specified completed-tensor map for a finite algebra; ours is a Jacobson-completion isomorphism with no finite base map.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-another-helper-g-ring: proves geometric regularity of special polynomial formal fibres over a complete local domain of characteristic p; ours is an unrestricted semilocal completion decomposition and asserts no regularity.

lem-per-semilocal-jacobson-completion-product vs new-completion-finite-extension-tensor-bijective: gives bijectivity for an already constructed completed tensor map of a finite algebra over R_p; ours constructs the Jacobson-completion product with no chosen R.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-localized-finite-quotient-charts: identifies localizations of positive finite-algebra quotients and their maximal-prime indexing; ours is a full inverse-limit isomorphism for an arbitrary semilocal ring.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-another-helper-g-ring-noetherian-component: is a component of Noetherianity for a special polynomial formal-fibre construction; ours is an algebra isomorphism for an arbitrary Noetherian semilocal ring, with no polynomial or field hypotheses.

lem-per-semilocal-jacobson-completion-product vs new-completion-finite-extension-tensor-map: constructs a tensor-to-completion map without claiming its product decomposition; ours gives the semilocal Jacobson-completion product isomorphism.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-local-tensor-quotient-component-map: gives an injective linear map of finite quotient tensors to localized quotients for a finite base algebra; ours gives a canonical algebra isomorphism of completed rings without that base.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-localized-algebra-finite-quotients: gives finite quotient comparisons and ideal cofinality for an algebra finite over R_p; ours identifies the full completion of a semilocal ring not assumed finite over a local base.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-finite-extension-tensor: identifies a completed-base tensor with completion of the localized finite algebra; it has no completed maximal-factor conclusion and requires a finite base map, unlike ours.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-finite-extension: assumes S finite over a chosen Noetherian R and decomposes the completion over one prime p of R; ours assumes only A semilocal and decomposes its Jacobson completion over all maximal ideals. Not every semilocal A is supplied as a finite algebra over a local base.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-finite-over-complete-local-product: requires a finite algebra over an already complete local base and decomposes the algebra itself; ours completes an arbitrary Noetherian semilocal ring and supplies no decomposition before completion.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-finite-extension-decomposition: is finite-extension completed-tensor decomposition with coordinate compatibility over a selected R_p; ours is the Jacobson completion of an arbitrary semilocal ring without a chosen finite R-algebra presentation.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-another-helper-g-ring-geometric-component: is a geometric-regularity component of a special polynomial formal fibre; ours is a completion isomorphism that assumes no regularity or polynomial presentation.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-tensor-quotient-separated: says quotient evaluations separate the completed tensor of a finite base algebra; ours is an algebra isomorphism with the completed maximal-local factors.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-helper-g-ring-char-p: proves geometric regularity for power-series polynomial generic formal fibres in characteristic p; ours asserts only a semilocal completion product in arbitrary characteristic.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-completion-finite-quotient: compares completion with a local quotient R[z]/(z^p-f) over local R; ours treats any semilocal ring and its full maximal-ideal product.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-local-tensor-quotient-base-ideal-detection: detects vanishing in finite quotient tensors using extended base-ideal powers; ours is a Jacobson-completion isomorphism without a chosen base or tensor presentation.

lem-per-semilocal-jacobson-completion-product vs lem-weil-pbc-local-tensor-quotient-detection: detects vanishing of finite quotient tensors by sufficiently deep local reductions; ours gives the full semilocal completed-ring decomposition.
