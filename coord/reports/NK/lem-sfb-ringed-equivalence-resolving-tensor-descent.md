# Stage-1 worker report

Item: lem-sfb-ringed-equivalence-resolving-tensor-descent. Group: NK. Date: 2026-10-22.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-equivalence-resolving-tensor-descent.json: existing statement, now split into ten proof steps; statement unchanged; no Mathlib match for the whole assertion.
- dag/nodes/sec-six-functors-basics/lem-sfb-symmetric-monoidal-equivalence-transport.json: new statement and Mathlib leaf. CategoryTheory.Monoidal.Transported.instSymmetricCategory, together with the cited transport, tensor-data and monoidal/braided-functor instances, supplies each clause. No new unresolved node.
- citations.json: all 22 step/node citations, each with an exact quotation from that node's statement.
- report.md: this report. Existing searches.jsonl and write_split.py were retained as interrupted-attempt material; the JSON nodes are the delivery, and the script has not been rerun after the coherence correction below.

## Attachments

None. I searched the live WeilConjectures library for the blueprint tag and resolving-localization/tensor-equivalence notions. I read WeilConjectures/CategoryTheory/DerivedCategory/Monoidal/Equivalence.lean: tensorLeftCompMapDerivedCategoryIsoOfKFlat and tensorLeftCompMapDerivedCategoryIso give tensor comparisons under additional functorial-flat-resolution and closed Grothendieck hypotheses; they do not assert this item's resolving-subcategory equivalence, prescribed two-variable normalization, arbitrary K-flat normalization and native symmetric coherence under the stated hypotheses. Thus they are not an attachment for the item.

## WANTED

None. The source material used is available locally.

## Corrections and scope

The live item has no proof and is unsplit. The interrupted sandbox already had a ten-step proof, one searched Mathlib leaf and citations. I compared its statement with the live node and retained it verbatim. The required initial dry run exited with a missing report/Review-by-NK diagnostic; no earlier delivery was active. I retained all recorded searches after reading their hits and the relevant Mathlib sources.

The coherence argument in the interrupted proof had an imprecise associativity residual and mixed a complex-level comparison with homogeneous component notation. I replaced it with the correctly typed oplax-monoidal associativity equation and a complex-level Koszul-symmetry equation, explaining its homogeneous components separately. This repairs the proof, not the statement. There is no statement dispute and no change to the unit or chapter route.

The proof is explicitly agent-written: Stacks provides the ringed-site construction, not the assertion for an arbitrary equivalent coefficient category. I do not attribute that transfer to Tag 0G7D alone. No SGA source is used.

## Not duplicates

lem-sfb-symmetric-monoidal-equivalence-transport vs lem-sfb-exact-monoidal-equivalence-total-kflat: the latter derives total tensor comparisons and flat/K-flat preservation from an already monoidal coefficient equivalence; the new leaf equips a category with a symmetric monoidal structure along an equivalence of plain categories, without abelian, exactness or complex hypotheses.

lem-sfb-symmetric-monoidal-equivalence-transport vs lem-coef-model-equivalence-transport: that node transports model-category and simplicial structures, not an arbitrary symmetric monoidal tensor, its constraints and monoidal unit/counit.

lem-sfb-symmetric-monoidal-equivalence-transport vs lem-coef-equivalence-finite-model-axioms: that node transports finite model axioms and lifting/factorization classes, not tensor constraints.

lem-sfb-symmetric-monoidal-equivalence-transport vs lem-coef-dgfunctor-coherent-transport: that node is about enhanced dg functor categories and enriched evaluation/composition with higher homotopies, not an ordinary monoidal category transported along an ordinary equivalence.

lem-sfb-symmetric-monoidal-equivalence-transport vs lem-sfb-compositor-equivalence-conjugation: that node compares compositor and unit pastings for indexed functors, not construction of a tensor and braiding on an arbitrary equivalent category.

lem-sfb-symmetric-monoidal-equivalence-transport vs lem-coef-cartesian-monoidal-structure-uniqueness: that node concerns cartesian symmetric monoidal infinity categories and equivalence spaces; the new leaf concerns arbitrary ordinary symmetric monoidal categories, with no cartesianness.

I searched the entire DAG for transportStruct, Transported.instSymmetricCategory, transported symmetric monoidal structures and monoidal equivalence transport, and used blueprint_refs.py search for monoidal transport, transport and equivalence. No imported blueprint statement states this general ordinary transport lemma. The nearest blueprint ancestor is sk-prop-sf-rf-shriek-preservation. The from/via fields record the auxiliary coefficient-equivalence chain, whose purpose is the fourth proof paragraph's restriction of the adjunction. No new node duplicates the item or merely restates one of its clauses: the single new node is a reusable Mathlib theorem on plain categories, with none of the resolving-localization conclusions.

## Review by NK

I read stages/1-dag.md, the worker brief, the three blueprint levels in SETUP.md, GOAL.md, and delivery-errors.md B through E (including the duplicated new-target version). I read the chapter and unit records, the current blueprint unit text, every cited node statement, the local Stacks source for Tags 06YS, 06YT, 06YU, 0G7D and 0FPT, and their labels in tags/tags. In sites-cohomology.tex these are lemma-K-flat-resolution (3207), lemma-derived-tor-quasi-isomorphism-other-side (3233), definition-derived-tor (3300), lemma-factor-through-K-flat (3418), and lemma-symmetric-monoidal-derived (13136). The last proof is omitted by Stacks: its native coherence content is therefore cited through the existing lem-sf-ringed-derived-native-tensor statement rather than silently supplied by that omitted proof.

For the new leaf I read Mathlib/CategoryTheory/Monoidal/Transport.lean 138–222 and Braided/Transport.lean 29–83. transportStruct defines precisely E(HX tensor HY), E of the tensor of inverse images on maps, the image unit, and the associators/unitors. transport supplies the laws, equivalenceTransported and its instances give the strong monoidal inverse/forward functors and monoidal unit/counit, and the braided and symmetric transport instances give exactly the asserted braiding and symmetry. The Transported type synonym changes no underlying category. The match records the actual declarations and line locations for these clauses. Recorded grep results with a file as subdirectory show line numbers in the top field; I checked the numbered source rather than treating those numbers as declaration names. LeanSearch, Loogle and LeanFinder all returned this transport machinery; the leaf's source and match reflect the files actually read.

Step 1 uses lem-sf-exact-functor-derived-triangulated only for termwise descent of the additive exact F and G. It uses lem-weil-pbc-localization-universal-property for descending their termwise unit/counit and detecting the equations; its parts (2) and (3) explicitly cover natural transformations and equality, not merely factorization of functors. Homotopies are preserved by applying additivity to f-g=dh+hd. The localized triangle identities are therefore proved, not assumed for independently chosen derived equivalences.

Step 2 uses the exact statement of lem-weil-pbc-site-derived-tensor-descent for the flat-term K-flat resolving localization, and the full functor-category localization property of lem-weil-pbc-localization-universal-property. Flat and K-flat preservation/reflection are hypotheses of this item, not facts borrowed from a definition. The displayed factorization of a W-inverting V is through the ringed-site localization followed by H. The termwise quasi-inverse and localization comparisons identify its restriction with V. The same construction on natural maps proves full faithfulness and uniqueness. The source being a small site in the coefficient universe ensures the ringed-site theorem applies; no arbitrary-large-index colimit is invoked.

Step 3 uses lem-sfb-product-localization, which really states the finite product universal property, and lem-weil-pbc-localization-universal-property, which really gives fully faithful precomposition on natural transformations. Identities lie in each quasi-isomorphism class, as required by the product lemma. Only one to four variables occur. This justifies the later descent and detection of diagrams without a functorial replacement.

Step 4 uses lem-sf-ringed-derived-native-tensor for the symmetric source derived tensor and all its native model constraint squares, and lem-weil-pbc-site-derived-tensor-descent for the specified model maps. These sources apply to the category of sheaves of modules on the small ringed site; the standard additive sheafification hypotheses mentioned by the native-tensor node hold for module sheaves here. The new Mathlib transport leaf is applied to the exact derived equivalence established in step 1. This supplies coherence on the target derived category as an actual theorem, rather than assuming coherence merely because a tensor bifunctor exists. The image of R[0] is identified with the ordinary target unit by kappa and the supplied unit comparison.

Step 5 uses lem-sf-ringed-derived-native-tensor precisely for its model map when GU and GV are arbitrary K-flat complexes, without imposing flat terms. I checked every arrow of the displayed composite: it starts at Q_A(U tensor V), passes through EH, lambda, the inverse total comparison psi, the source model map, and inverse lambda maps to E(HQ_AU tensor HQ_AV). All arrows are isomorphisms. lem-pc-kflat-resolution explicitly gives a flat-term K-flat complex with a quasi-isomorphism to GC; exactness of F and its assumed flat/K-flat preservation give a replacement of C after the counit. No coherent choice of such replacements is used.

Step 6 uses the native model coherence of lem-sf-ringed-derived-native-tensor, the transported monoidal constraints of the new leaf, and the tensor/K-flat tests defined in def-sfb-preserves-kflat-quasi-iso. The cancellation is by the specified natural unit/counit and their triangle identities, leaving the now-explicit associativity equation for psi. Both unitor residuals are the assumed unit coherence of the inverse comparison; the symmetry residual is written for total complexes and checked on each (p,q) summand with sign (-1)^(pq). Associativity and two successive acyclic tests show a tensor of K-flat complexes remains K-flat, and the unit is K-flat by its identity tensor functors. These are direct uses of the definition, not new non-elementary lemmas or claims that total tensor necessarily preserves flat terms under the abstract hypotheses.

Step 7 uses the natural-transformation extension clause of lem-weil-pbc-site-derived-tensor-descent. Its statement explicitly quantifies over an arbitrary target category E and arbitrary two bifunctors from D(R)^2, so it applies to the two bifunctors with values in D(A) here. The five maps in theta have the domains/codomains in the requested normalization. Descending the inverse and using uniqueness proves that t is an isomorphism. Thus the new leaf does not take over the content of the item: the item's own proof constructs and normalizes t.

Step 8 uses lem-pc-kflat-resolution for separate replacements of the two arbitrary K-flat representatives. def-sfb-preserves-kflat-quasi-iso supplies the two-sided quasi-isomorphism tests. Factoring a tensor b through a tensor identity and identity tensor b requires only the stated K-flatness of P and Q', not that tensoring by an arbitrary complex preserves a quasi-isomorphism. Naturality and cancellation with invertible vertical maps then give the normalization without flat terms. This step is marked non-elementary because it includes an application of the resolution theorem, although its comparison after that application is direct.

Step 9 uses the native source constraint squares of lem-sf-ringed-derived-native-tensor and the finite-variable detection provided by lem-sfb-product-localization and lem-weil-pbc-localization-universal-property. K-flat closure was established in step 6, and step 8 applies to the intermediate products; no unsupported closure of the flat-term resolving subcategory is needed. The associativity residual is the assumed associativity for tau; the two unit residuals are its supplied unit equations; the symmetry residual is the supplied Koszul symmetry for tau. This proves compatibility with the specified native constraints rather than merely defining transported constraints with an arbitrary braiding.

Step 10 uses lem-weil-pbc-localization-universal-property and lem-sfb-product-localization to compare another ordinary K-flat tensor carrying the same canonical model maps. On resolving pairs the comparison is the composite of the two model isomorphisms; the full faithfulness extends it uniquely and detects its constraints. The conclusion applies to an independently specified ordinary K-flat tensor with its usual model compatibility, not an arbitrary unrelated symmetric structure on the same bifunctor.

I tested the new leaf on the identity equivalence, on the terminal category and on a non-strict equivalence: its tensor is respectively the original tensor, the unique tensor and the genuinely transported tensor with unit/counit corrections. For the item I checked zero complexes, the zero coefficient ring, unit complexes in degree zero and complexes concentrated in degrees p,q; the symmetry becomes (-1)^(pq) times the underlying symmetry, including the odd/odd minus sign. The argument does not require boundedness, finite generation, enough projectives in A, or a functorial flat resolution in A. Countable signed total sums and their coherences are part of the hypotheses. Every cited statement was read, not its proof used as an unstated interface. citations.json has one exact statement quotation for each of the 22 step/node pairs, checked against the current files. No proof step exceeds 2000 characters; the largest is 1440 characters and contains only the specified coherence calculation and the immediate K-flat tests.

The generic off-unit tools are declared in split_report.tool_uses: ringed-site tensor descent, localization's universal property, K-flat resolutions, and native ringed-site tensor coherence. They supply general tools used by this coefficient-equivalence argument and do not replace a step of the fixed unit route. Product localization and exact-functor descent are already within the relevant generic coefficient route; the new Mathlib leaf is a tool automatically.

## Unfinished work

No mathematical clause of this stage-1 item is left unfinished. The new leaf has no proof, as required for Mathlib status. This delivery contains no Lean writing or compilation. The maintainer's independent mathematical review remains the next project stage after delivery.
