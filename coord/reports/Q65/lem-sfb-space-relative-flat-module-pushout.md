## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-flat-module-pushout.json: statement unchanged; eight proof steps, status split. Existing Mathlib searches are retained; none gives this algebraic-space relative-flat patching equivalence.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-fp-module-fp-algebra-pushout.json: new statement-only lemma; no Mathlib match. This is the full flat-then-finitely-presented ambient-algebra version of Stacks 08KP.
- citations.json: one verbatim quotation for each of the item's 24 step citations.

Attachments: none. Searches for the exact blueprint tag and for relative flatness, pushout, patching and fibre-product module terminology in lean/WeilConjectures found no declaration stating the item or the new lemma. Scheme flat-morphism and relative canonical-module base-change declarations do not state either result.

WANTED: none.

The item arrived with no proof and no lean_audit record. Its statement already corrects two source typos in 08KV; I have not changed it. The proof now spells out the quasi-inverse, flatness, the two recovery isomorphisms and their action on compatible morphisms, and the finite-presentation test. I did not assume that the ambient map h is flat. The existing lem-sfb-relative-fp-module-fibre-product assumes its ambient algebra is flat, so it cannot supply the needed arbitrary locally finitely presented case. The new node records exactly the missing version from the source, with its factorization hypothesis.

Nothing remains unfinished in the one-level split. The new lemma intentionally remains unsplit. Its source proof first replaces the ambient algebra by a polynomial algebra over the flat intermediate algebra, then proves finite presentation by the finite-generation theorem applied to the patched syzygy modules; it is not a two-line fact from the flat special case. This is background for its future worker, not a proof inside its node.

## Source error

Stacks 08KV, lemma-space-over-pushout-flat-modules, prints flatness over X instead of Xprime for the module on Uprime in (2)(b). There need not even be a map Xprime to X: Spec(F_2) into Spec(Z/4) has no retraction, since there is no unital homomorphism F_2 to Z/4. The intended base is Xprime, as the restriction functor and algebraic Lemma 07RW show. In 08KV(b), O_Y for the module G must be O_V: G is a module on V, not generally on Y. These corrections are already in the live item's statement and source place. No further statement repair is made in this delivery.

## Not duplicates

lem-sfb-relative-fp-module-fp-algebra-pushout vs lem-sfb-relative-fp-module-fibre-product: the existing 08KP node assumes D itself is flat over R; the new node permits any D finitely presented over a flat R-algebra E, including nonflat finitely presented R-algebras (take E=R).

lem-sfb-relative-fp-module-fp-algebra-pushout vs lem-sfb-fibre-product-algebra-etale: the latter patches etale algebra structures over the base ring; the new node concerns modules over an independent ambient algebra D and proves their finite presentation, without etaleness.

lem-sfb-relative-fp-module-fp-algebra-pushout vs lem-sfb-fibre-product-algebra-flat-presentation: the latter concerns flatness and finite presentation of the patched algebra itself; the new node concerns modules over a possibly nonflat ambient algebra.

lem-sfb-relative-fp-module-fp-algebra-pushout vs lem-sfb-patched-module-base-change: the latter recovers the two modules by scalar extension, with no finite-presentation conclusion and no ambient-algebra factorization.

lem-sfb-relative-fp-module-fp-algebra-pushout vs lem-sfb-flat-module-fibre-product-patching: the latter proves flatness over the base fibre-product ring and recovery of flat base modules; it does not prove finite presentation over a separate ambient algebra D.

lem-sfb-relative-fp-module-fp-algebra-pushout vs lem-sfb-finite-module-fibre-product-patching: finite generation over the base fibre product is weaker than finite presentation over D, and the existing node has no relative ambient algebra.

lem-sfb-relative-fp-module-fp-algebra-pushout vs lem-sfb-fibre-product-finite-projective-patching: finite projective modules over the base pieces are a different class from modules finitely presented over D_i and merely flat over the base pieces; these relative modules need not be finite over the base pieces.

The whole DAG was searched for 08KP, 08KH, 07RW, relative-module-over-fibre-product, finite presentation and patching. I opened the seven same-source-tag candidates above. blueprint_refs.py search was run for flat modules, finitely presented module and fibre product across all chapters; none states the new lemma. blueprint_refs.py ancestor reports None for this item. I preserved the inherited null ancestor and extended its via chain for the new node. The current latest blueprint unit and its direct-image proof were read; no chapter or unit was changed.

## Review by Q65

I read spaces-pushouts.tex Tag 08KV (lemma-space-over-pushout-flat-modules), including its explicit fibre-product formula and the reference to 07RW and 08KP. I read more-algebra.tex Situation 08KH and Situation 08KK and Lemmas 07RU, 07RW and 08KP. The new node states 08KP with the same three hypotheses: relative finite presentation of the two pieces, their flatness over B and Aprime, and the flat-then-finitely-presented factorization of the ambient algebra. The ideal is neither finitely generated nor assumed nilpotent in that algebraic result. The ambient algebra need not be flat. All rings, actions, modules and the overlap isomorphism are introduced explicitly; its proof, proof_deps and proof_origin are empty. Its definition dependencies name tensor product, flatness, finitely presented algebras and finitely presented modules, rather than merely referring to a tag for meaning.

For step 1 I checked the statement of lem-sfb-infinitesimal-pushout-affine-charts: applying it to the identity pieces really gives the affine inverse images of each P_a, and R=B times_A Aprime. I added the existing Mathlib leaf lem-weil-pbc-fibre-product-affine-spectra for the tensor rings of the base changes, rather than attributing this calculation to the abstract definition of a fibre product. I also read Schemes Tag 01I4 (lemma-fibre-product-affine-schemes). The proof never asserts D=D_2 times_{D_0} D_1 for an arbitrary chart W; that assertion would require an additional hypothesis.

For step 2 I opened the affine-chart calculus, the scheme Zariski/etale equivalence, and the affine pullback-chart flat-stalk criterion. The first states the section-module dictionary, kernels and finite-presentation detection. The second explicitly compares tensor pullbacks. The third really allows a single arbitrary affine open, and with the identity base change it states exactly the required equivalence between flat sections over R and stalkwise relative flatness. I did not use a definition of flatness as a substitute for that theorem.

For step 3 I checked that the quasi-coherent pullback theorem has no flatness assumption, that pointwise-module-flatness-base-change clause (1) has no finiteness assumption on the module or morphism, and that chart-adjunction-tensor-realization actually supplies the specified pullback-composition isomorphism. These statements justify the functor and its arrows, not just its object assignment.

For step 4 I read spaces-cohomology.tex Tag 07U8 (lemma-affine-base-change) and the cited node's statement. It supplies quasi-coherence of the affine direct images and their canonical comparison on every etale chart, without a flat base-change hypothesis. The affine-chart calculus supplies the kernel assertion; the fibre product is the kernel of a difference map. The maps are the actual restriction maps, so the construction defines a global functor and does not hide an effectiveness-of-descent theorem.

For step 5 I checked the exact statements of flat-module-fibre-product-patching and patched-module-base-change. The first supplies flatness and flat-module reconstruction over R; the second supplies both canonical projection/tensor isomorphisms, including naturality. They apply after forgetting the ambient D action because the overlap comparison is in particular A-linear. The displayed maps also preserve the D action coordinatewise, so their inverse bijections are D-linear. Tensor associativity is written on generators and the quotient identification uses the existing tensor-over-quotient-ring node. This accounts for every non-elementary algebraic input in this step.

For step 6 the same flat-module node states exactly the map l to (l tensor 1,l tensor 1) used for the unit. It is natural and D-linear. The recovery maps in step 5 are the canonical ones, so they agree on the overlap with alpha. Thus compatible pairs of all module homomorphisms lift uniquely; no restriction to isomorphisms is introduced. The two natural isomorphisms globalize because their forward sheaf maps were constructed globally, rather than because I assumed that tensor pullback along either closed piece preserves arbitrary kernels.

For step 7 I verified that local finite presentation of h is tested on scheme charts by def-sfb-space-morphism-properties and that def-sbc-locally-finite-presentation provides affine neighbourhoods with a finitely presented ring map. The proof chooses such neighbourhoods at each point. It does not infer the property for an arbitrary affine restriction solely from this definition. Sectionwise finite presentation comes from the exact clause of the affine-chart calculus. The new algebraic node is applied with E=R, whose identity algebra is flat by the tensor unit, not with the possibly nonflat ambient algebra D as its flat intermediate algebra.

For step 8 the adjunction in def-trf-space-etale-module-functors makes preservation of finite presentations an elementary cokernel argument. The fibre-products-etale-covers node explicitly states stability of covering families under base change, which is what is needed to retain a local presentation. Thus the reverse direction needs no finiteness hypothesis on h. Only this step is marked elementary; the other steps use the cited substantive results.

I tested zero rings, zero modules, the empty source, the identity thickening (I=0), and the overlap A=0. The algebraic patching results permit all of them. To test the missing nonflat case, take R=k[epsilon]/epsilon^2, Aprime=R and A=B=k, D=R[x]/(epsilon*x), and the D-module R via x=0. Here D is finitely presented but not R-flat; its two pieces are k over k[x] and R over D, with overlap k, all given by x=0. They are finitely presented over their ambient piece rings and flat over their base rings, and patch to R=D/(x), finitely presented over D. The old flat-ambient lemma cannot be applied to this D. This checks that the new node is necessary and has the right hypotheses. No proper-support, separatedness, quasi-compactness, Noetherian, or flatness-of-h hypothesis was inserted.

The Mathlib searches ran through the required msearch.py command and were recorded in searches.jsonl. I read their hits: finite-presentation base-change and transitivity theorems, flat/projective and finite-free factorization results, scheme pullback finiteness results, and general sheaf gluing do not state ring-fibre-product patching. In particular I opened FinitePresentation.of_isBaseChange (FinitePresentation.lean:353), the flat factorization theorem (EquationalCriterion.lean:270), and Algebra.FinitePresentation.baseChange (FiniteStability.lean:55). None is a one-line specialization proving the new node. Both semantic phrasings, Loogle and grep are recorded truthfully, with no unavailable search misreported as absence.

All proof steps are shorter than 2000 characters. I checked B1-B9 (statement-only shape, self-contained objects, definitions, TeX, source tags, no false leaf, blueprint ancestry), C1-C8 (all substantial facts cited from statements, duplicate search, no use of a cited proof's internal construction, generic off-unit tools declared), D1-D5 (the item carries the sheaf construction and equivalence argument; only a smaller algebraic input is new), and E1-E7 against the files and source as described above. I corrected the draft's source-situation tag to 08KK and supplied the missing affine-spectrum tensor-product citation before delivery. No Lean was written and no compiler or Lake command was run.

## Validation

The first delivery dry run rejected the wording "the item's definition" in step 2 as non-self-contained. It now says "the stated definition of relative flatness"; the mathematical argument and hypotheses are unchanged. A further LeanFinder query explicitly included the full flat-then-finitely-presented factorization and returned the same unrelated factorization/base-change results; it is recorded in the new node.
