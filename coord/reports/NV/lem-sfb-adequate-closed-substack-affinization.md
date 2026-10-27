# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adequate-closed-substack-affinization.json: item, statement unchanged; four-step split.
- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-power-lifting-universal-homeomorphism.json: new statement-only algebra lemma, unsplit, no Mathlib match.
- citations.json: exact statement quotes for every proof-step use.

## Attachments

None. Searched lean/WeilConjectures/ by the item blueprint tag and adequate/adequately terminology, and by polynomial power/homeomorphism terminology. There is no project declaration for either the item or the new algebra criterion. The references in lean/Sheaf/AlgebraicGeometry/AffinePGLFiniteStabilizerQuotient.lean are docstring references to adequate-moduli inputs, not an attachment for this item. No Lean written and no compiler invoked.

## WANTED

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, literature/alper-adequate-moduli-spaces-arXiv-1005.2398.pdf, Lemma 5.2.11, Remark 3.2.2 and Proposition 3.3.5, for the item and the new algebra criterion. Read the primary published PDF at https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf (printed pp.496,498,510). No download made.

## Findings and route

The imported statement is correct, including arbitrary closed substacks and arbitrary algebraic-space base change. It remains verbatim. The existing node lem-sfb-adequate-relative-spectrum states the general first assertion of Alper Lemma 5.2.11, so making another node for adequate affinization of a closed substack would duplicate it. The new node is instead a general ring theorem, with no stacks or adequate-moduli hypothesis, and does not restate a clause of the item. Its hypotheses must be proved, which step 3 does using all polynomial extensions.

The proof deliberately distinguishes adequate power lifting for one ring map from its universal variant. The inclusion of finite fields F_q into F_{q^2} lifts positive powers, but after extension to F_{q^2} its spectrum has two points. This rules out the incorrect shortcut from power lifting with n=0 to universal homeomorphism. Finite polynomials are essential. Polynomial lifts descend to arbitrary scalar extensions by the algebra argument of Alper Remark 3.2.2; Proposition 3.3.5 supplies the required nilpotent-kernel control after base change. That nontrivial general algebra argument is the one new node, left statement-only as required.

Read the chapter and unit records and the latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. This is the supporting moduli input on the ancestor chain already recorded in the item; the unit/chapter route and bindings are unchanged. blueprint_refs.py ancestor reports None for this imported supporting chain, so the inherited null ancestor is retained, with an explicit place and full via list. Whole-blueprint searches for adequate, universally adequate, power spectrum, polynomial power, closed substack, closed immersion algebra and polynomial universal homeomorphism returned no equivalent blueprint node. No source uses SGA.

## Searches

All Mathlib searches were made by the required msearch.py command and are retained in searches.jsonl. The new node records the eight actual ring-criterion searches (LeanFinder in two phrasings, LeanSearch, Loogle in two patterns, and source grep). Read Mathlib/RingTheory/Spectrum/Prime/Homeomorph.lean lines 33–60: PrimeSpectrum.isHomeomorph_comap proves the single-map homeomorphism criterion only. Its field-tensor specializations have hypotheses about purely inseparable field extensions, absent here. The source grep for adequate found only unrelated power-series terminology. No hit proves the polynomial-to-all-base-changes implication in one specialization. For the item, searches returned scheme affine spectra, scheme closed immersions and specTargetImage; none gives the stack assertion.

## Not duplicates

lem-sfb-polynomial-power-lifting-universal-homeomorphism vs lem-pc-homeo-pure-insep: the existing node starts with a purely inseparable field extension and a scheme over that field; the new node treats general ring inclusions satisfying polynomial power lifting, including rings with nilpotents and no field-base hypothesis.
lem-sfb-polynomial-power-lifting-universal-homeomorphism vs lem-weil-pbc-pth-root-algebra-local: the existing node proves locality of a particular finite p-root quotient over a local F_p-algebra; the new node assumes neither locality nor a p-root presentation and concludes homeomorphisms after all tensor base changes.
lem-sfb-polynomial-power-lifting-universal-homeomorphism vs lem-weil-pbc-radicial-prime-unique-degree-p: the existing node assumes integral domains in characteristic p and a single p-root extension and concludes uniqueness of primes; the new node has arbitrary commutative rings and polynomial power lifting, and concludes the topology of every scalar extension.

lem-sfb-polynomial-power-lifting-universal-homeomorphism vs lem-pur-all-element-powers-spectrum-homeomorphism: the existing Tag 0BR8 Mathlib leaf gives a homeomorphism for one map with nilpotent kernel; the new statement starts with an injection and power lifting on all finite polynomial extensions and gives homeomorphisms after every tensor base change. Tensor base changes need not remain injective; this is a substantive additional algebra argument.
lem-sfb-polynomial-power-lifting-universal-homeomorphism vs lem-pur-power-generated-spectrum-homeomorphism: the existing Tag 0BRA node assumes fixed-prime power and prime-multiple conditions on generators; the new criterion has arbitrary characteristic and no such fixed-prime hypothesis.
lem-sfb-polynomial-power-lifting-universal-homeomorphism vs lem-sfb-adequate-relative-spectrum: the existing node concerns adequate morphisms and relative spectra of stack algebras; it has no ring polynomial criterion.
lem-sfb-polynomial-power-lifting-universal-homeomorphism vs lem-sfb-adequate-closed-substack-affinization: the new statement is a general algebra input, not a closed-substack moduli factorization. Steps 1–3 still construct the adequate map, the closed image, and the polynomial power lifts.

DAG searches included the full graph for adequate homeomorphism, universally adequate, polynomial power/homeomorphism, the Alper places 3.2.2/3.3.5, Stacks Tag 0BR8/lemma-powers, and PrimeSpectrum.isHomeomorph_comap. Existing exact single-map input was found and read, not duplicated. The numerous unrelated numerical-section matches were inspected by title/statement before excluding them.

## Review by NV

I read Alper's published Lemma 5.2.11 on p.510, including both its general relative-spectrum assertion and final closed-image assertion; the item matches it, with the adequate-homeomorphism conclusion used only for its universal-topology consequence. I also read Definition 3.2.1 and Remark 3.2.2 on p.496 and Proposition 3.3.5 with its proof on pp.498–499. These verify the new ring statement: injectivity gives zero initial kernel, the polynomial hypothesis is precisely the universal-adequacy test, and the proposition concludes universal homeomorphism with no finiteness assumption. The finite-type condition appears only for the alternative bounded-exponent clause, which the new statement does not use. I checked Stacks algebra.tex Tag 0BR8 (lemma-powers), and the Mathlib source above, to separate that weaker result from the new one.

For step 1 I opened lem-sfb-disjoint-closed-substacks-algebra-quotient, lem-sfb-adequate-relative-spectrum and def-sfb-stack-quasi-coherent-algebra. The disjoint node explicitly gives the quasi-coherent quotient algebra with its scheme-test formula; taking the second substack empty makes its algebra zero, hence its product the first algebra. On a scheme chart the closed immersion is a quotient ring, so its relative spectrum is exactly that closed chart, with the same inclusion. The general relative-spectrum node explicitly gives both quasi-coherence of phi_*A and adequacy of the canonical evaluation map. The direct-image convention identifies this algebra with j_*O_Z on every etale test, rather than assuming a big-fppf direct image is automatically quasi-coherent. The first node's hypotheses hold for Z and the empty stack with no finite-type assumption.

For step 2 I read lem-sfb-space-qcoh-affine-chart-calculus, lem-sfb-space-closed-ideal-correspondence and lem-sfb-space-relative-spec-correspondence. Their statements respectively give the quasi-coherent kernel and its affine chart values, the closed subspace with quotient structure algebra, and the contravariant relative-spectrum map. The minimality argument is written out: any closed factorization kills its ideal, so that ideal lies in the kernel. Thus the identification as scheme-theoretic image is not inferred from mere equality of point sets. No reducedness of the quotient is assumed.

For step 3 I read lem-sfb-adequate-moduli-etale-locality, lem-sfb-affine-target-adequacy-criterion, def-weil-pbc-flat-ring-map, lem-sfb-stack-flat-scalar-sections and lem-sfb-adequately-affine-affine-target-base-change. The first gives adequate restriction to X_U and its affine global-functions criterion; the second gives adequate affineness and power lifting over any affine target. Polynomial flatness is checked coefficient by coefficient from the definition, using the monomial basis (no finite-dimensional-module hypothesis). The scalar-sections lemma states both the ring isomorphisms and preservation of the quotient; its naturality preserves the restriction map and powers. The affine-target-base-change lemma imposes no diagonal assumption and allows arbitrary algebraic stacks over the affine base; it makes X_P adequately affine. Applying the affine criterion there gives the exact polynomial power lifts required next. I avoided lem-sfb-adequate-flat-base-change because its recorded statement imposes extra diagonal hypotheses not present here.

For step 4 I read the new algebra statement, the full relative-spec correspondence, lem-sfb-smooth-presentation-closed-subsets and lem-sfb-stack-etale-local-qcqs-homeomorphism. The quotient R/I injects into B by construction, and polynomial lifts pass through the coefficient quotient; no claim is made that arbitrary base-changed ring maps stay injective. The new lemma supplies the homeomorphisms on all affine tests. On scheme tests these glue on affine open covers. On arbitrary algebraic-stack tests, a smooth scheme atlas and the atlas statement gives open quotient surjections and the equivalence relation by the atlas overlap, so the bijection and topology descend as written. The etale-local universal-homeomorphism node then descends from W_U to W, and explicitly includes arbitrary-stack base changes, which is stronger than needed. I checked Stacks stacks-morphisms.tex Tag 0DTQ, lemma-check-universal-homeomorphism-covering, for this final locality use. No part uses the ancestor's surjectivity or closed-map theorem, which would produce a cycle.

Small cases: Z empty gives B=0 and E=W empty; Z=X gives E=Y and e identity. A nonreduced closed subscheme for an identity moduli map gives E=W with its nilpotents, so the proof does not silently reduce. For the new algebra statement I checked identity maps, the zero ring, and purely inseparable field inclusions; a proper finite separable finite-field inclusion fails the polynomial hypothesis as explained above. No uniform exponent, finite generation or Noetherian hypothesis is introduced. All four steps are below 2000 characters; none hides a lemma by excessive length. New node has no proof, source and statement dependencies are explicit, TeX is escaped once, and all proof citations have verbatim statement quotes in citations.json.

This is the direct-delivery self-review authorized in the brief; no second worker or agent was started. Nothing was corrected in the mathematical statement. The main corrections to a naive split are reuse of the general relative-spectrum theorem, the polynomial test needed for universality, and avoidance of a flat-base-change citation with unavailable diagonal hypotheses.

## Unfinished work

The one new ring criterion remains unsplit for a subsequent stage-1 item, as required for children created in a one-level split. No remaining work on this item's assembly proof is intentionally deferred. Server dry run and delivery are recorded below when complete.

## Dry-run repairs

The first dry run requested three additional Tag 0BR8 comparisons. Opened all three node statements and added their exact differences above. None gives the general polynomial criterion. No mathematical statement or proof changed.

Final content audit after the passing dry run: made the atlas argument explicitly apply to arbitrary algebraic-stack tests, with smooth atlases, before invoking the locality node whose definition quantifies over stacks. This strengthens the verified intermediate assertion and leaves the item statement unchanged. Re-running the dry run after that clarification.
