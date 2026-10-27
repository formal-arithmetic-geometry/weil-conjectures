## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-fppf-flat-lfp-affine-acyclicity.json`: item, split into five proof steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fppf-flat-lfp-zero-cohomology.json`: one new statement-only node, Stacks 0755(1); no Mathlib match and no proof or proof dependencies.
- `citations.json`: one verbatim statement quotation for every node used by every step. Full statements are quoted to retain all qualifications.
- `searches.jsonl`: actual search-command records. `write_split.py` is sandbox-only preparation code.

## Attachments

None. Searches in the project `lean/WeilConjectures/` for the item's tag, fppf, acyclicity and big/small comparisons found topology-covering lemmas and general site cohomology, not a declaration with this statement. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are present in the Stacks source checkout.

## Corrections and scope

The imported item has the correct statement. Its original source note names the right theorem, but an application of 0756 as a new node would merely repackage this item's argument. The proof instead follows that theorem's kernel/image/cokernel argument, retaining its weak flat-lfp hypothesis. The existing associated-sheaf vanishing result is about underlying abelian cohomology; I explicitly use the objectwise ringed-site module/abelian comparison to obtain the requested injective-module-resolution cohomology. I do not identify an injective module's underlying abelian sheaf as injective.

I initially considered a new small-to-big comparison prerequisite. Whole-DAG searches located `lem-sfb-big-fppf-zariski-ringed-comparison`, so no such node was created. The new 0755 node is about every sheaf zero on the flat-lfp tests, over a possibly nonaffine scheme. It says nothing about an arbitrary quasi-coherent restriction or comparison map and is not a clause of the item. The item's content is the comparison morphism, its testwise invertibility, and the resulting two long exact sequences.

The item's inherited blueprint ancestor is null; `tools/blueprint_refs.py ancestor` explicitly reports None. I retain that metadata and specify the exact scheme-local use in the inherited `from.place`. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. Its current node is named `sk-thm-sf-ctf-stability-direct-images` and has frontmatter `of = det-thm-sf-ctf-stability-direct-images`. The current proof (3) supplies the direct-image context; the longer inherited alteration genealogy is historical and no route substitution is made here. Whole-blueprint searches for fppf acyclicity, fppf quasi coherent, parasitic, big small, small etale fppf, 070S, 03FH and 0755 found no blueprint statement that supplies the new lemma.

## Not duplicates

No existing node has source Tag 0755 or statement of the new parasitic vanishing lemma. Broad numeric-tag grep has incidental hits from other numbers, so these were distinguished by reading the source fields and statements. In particular:

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-sfb-affine-scheme-fppf-qcoh-acyclic: the new lemma assumes sectionwise zero only on flat-lfp tests and concludes vanishing there in every degree on any base; the existing one assumes an associated quasi-coherent big sheaf on an affine base and concludes positive-degree abelian vanishing.

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-sfb-scheme-fppf-flat-lfp-affine-acyclicity: the item has a potentially nonzero quasi-coherent small restriction and canonical comparison isomorphisms; the new input has zero values on the whole flat-lfp collection and no quasi-coherence/comparison/affineness assumptions.

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-sfb-flat-object-fppf-derived-sections: the existing theorem compares resolution diagrams for associated quasi-coherent sheaves on algebraic spaces under flat maps; the new input is vanishing for arbitrary sheaves supported away from the specified tests. It supplies no associated-sheaf or resolution-diagram comparison.

The first dry run listed the following additional pairs sharing secondary source Tag 03FD. I opened every listed node and checked the complete statement:

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-pqf-open-module-cohomology-comparison: the existing node compares module and abelian cohomology on a Zariski open, without asserting vanishing; the new statement is flat-lfp-test vanishing on a big fppf site.

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-sc-module-cup-flasque-acyclicity: the existing node assumes an underlying flasque sheaf on a scheme; zero values only on the specified big-fppf test collection neither assert nor require global flasqueness.

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-sc-picard-external-cup-scalar-comparison: the existing node identifies scalar cup products in degrees zero and one on a product of schemes over a field; it has no parasitic fppf vanishing assertion.

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-sc-picard-external-cup-unit-comparison: the existing node compares external cups with unit classes and pullbacks in degree one over a field; it has no zero-section or big-fppf vanishing assertion.

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-sc-scalar-unit-cohomology-pullback-comparison: the existing node compares restricted-scalar unit-module H1 with abelian H1 compatibly with field-scheme pullbacks; it has no vanishing assertion for arbitrary fppf modules.

lem-sfb-fppf-flat-lfp-zero-cohomology vs new-picard-derived-fibre-naturality: the existing node concerns proper flat finitely presented families, an invertible module and derived residue-fibre comparison naturality; the new statement has no such geometric input and concerns testwise-zero sheaves.

lem-sfb-fppf-flat-lfp-zero-cohomology vs new-sc-scalar-abelian-ext-factorization: the existing node identifies a scalar degree-one comparison with a specific Ext formula on one scheme; it supplies no higher fppf evaluation vanishing.

lem-sfb-fppf-flat-lfp-zero-cohomology vs new-sc-scalar-unit-comparison-family: the existing node asserts bijectivity of a particular degree-one scalar-unit comparison; it does not conclude any cohomology group is zero.

lem-sfb-fppf-flat-lfp-zero-cohomology vs new-sc-scalar-unit-pullback-naturality: the existing node asserts naturality of explicit scalar unit comparison maps for scheme morphisms over a field; it asserts no vanishing.

lem-sfb-fppf-flat-lfp-zero-cohomology vs def-sc-topological-abelian-cohomology: the existing node defines abelian sheaf cohomology of topological spaces and its long exact sequence; it gives no vanishing criterion for big-fppf module sheaves.

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-sc-additive-cohomology-scalar-comparison: the existing node compares H1 of an etale sheaf identified with additive sections on a curve to structure-sheaf H1 with scalar action; it does not cover arbitrary section-zero big-fppf modules or general degrees.

lem-sfb-fppf-flat-lfp-zero-cohomology vs lem-sc-etale-qcoherent-source-comparison-natural: the existing node compares the associated etale sheaf of a quasi-coherent module on a qc separated scheme with module cohomology; it has no testwise-zero big-fppf vanishing assertion.

## Review by Q68

I read `descent.tex` at 0756 (lemma-quasi-coherent-and-flat-base-change), including its entire proof, and 0755 (lemma-cohomology-parasitic), including its proof via the covering-stable collection. I read 06ZL (definition-parasitic): the relevant condition is zero on flat locally finitely presented tests, not zero on all flat objects. The new node spells out that condition rather than using the word parasitic as a definition. I corrected a preliminary source-number typo: 06ZL is the definition; 0754 is unrelated. I also read 070S (lemma-compare-sites), 03FH (remark-change-topologies-ringed-sites), 03DW (proposition-same-cohomology-quasi-coherent), coherent.tex 01XB, sites-cohomology.tex 03FD, and derived.tex 015B.

Step 1 uses the existing associated big-fppf equivalence to define A, the Zariski-etale equivalence to restrict the given alpha to a Zariski beta, the big-fppf/Zariski ringed comparison to identify A with tensor pullback, and the general ringed-topos module adjunction to produce a single morphism phi. I opened all four statements: each supplies exactly that data. In particular the associated-sheaf equivalence alone is not claimed to give maps to arbitrary nonquasi-coherent G; the additional adjunction supplies that map. This is a short composition of the four existing statements, not a new lemma.

Step 2 uses the scheme Zariski-etale equivalence's explicit canonical pullback comparison, the identity-on-opens unit normalization of the big/small comparison, and naturality of the module adjunction. Both candidate maps have the same adjunct, namely restriction of beta; on tensor sections both send a tensor to the scalar times the restricted beta section. This checks equality with the canonical c_g rather than choosing an arbitrary isomorphism. The hypothesis says c_g is invertible only when g is flat and locally of finite presentation, and that is exactly where the step uses it. Evaluating the resulting small-site isomorphism at id_V proves the section map is bijective.

Step 3 uses the category definition for sectionwise kernels and its abelian structure. For the cokernel I added explicit citations to the general-site exact forgetful theorem and the general-site epi/local-surjectivity theorem: the quotient G -> C therefore locally lifts every section. This avoids silently assuming that restriction to a smaller site preserves cokernels, or that a big-site cokernel is the sectionwise quotient. I read both statements: they concern arbitrary sites, not only small etale sites or ordinary topological spaces. The flat-composition and locally-finite-presentation-composition statements ensure each covering source remains in the test class. Its lifted section is a phi image by step 2 and hence is zero in C. Sheaf uniqueness gives C(V)=0. The new node now applies to K and C at id_U in ALL degrees, including zero. Kernels and cokernels may remain nonzero at other big-site objects; they are never asserted globally zero.

Step 4 uses the small-site Grothendieck statement in the K-injective-existence node, then the existing Grothendieck-enough-injectives theorem. The long exact derived-functor statement assumes exactly an abelian source with enough injectives and a left exact additive functor; sectionwise kernels/products verify the latter for evaluation. Reading its exact sequence shows the first comparison uses H^q(K) and H^{q+1}(K), and the second uses H^{q-1}(C) and H^q(C). Zero-degree acyclicity in the new lemma is essential at q=1 and in the initial segment. I checked those boundary degrees explicitly.

Step 5 uses the existing affine associated-big-fppf vanishing node, whose statement is for underlying abelian sheaves and arbitrary modules with no Noetherian hypothesis. The evaluation comparison node is for module resolutions and explicitly requires enough injectives; step 4 provides them on the small model. It gives exactly the identification needed at the final object. Neither the global unbounded comparison theorem nor any unjustified flatness of the structure sheaf over the integers is used.

I tested the item and the new statement on the empty base, the zero module, q=0 (new node only), and q=1 in the two exact sequences. For an empty scheme the empty covering forces zero sheaf sections. The item intentionally has no q=0 vanishing conclusion: nonzero M supplies a counterexample to such a strengthening. I also checked a nonflat test such as Spec(F_2) -> Spec(Z): the argument imposes no invertibility there and does not infer that K or C is globally zero. Infinite modules and a non-Noetherian affine base do not change any cited hypothesis. The new lemma's tests need not be affine. Its future proof follows the explicit covering-stable zero-values argument in 0755; that mathematical argument is source material here, not a hidden proof in its statement.

Against delivery-errors B: the new node introduces every object, cites definitions for its terms, uses single TeX escaping, records actual command searches, and is statement-only. Searches used two semantic phrasings plus LeanSearch, Loogle and grep; all services answered. The hits were quasi-coherence and finite-presentation definitions, affine-limit sections and general cohomology objects. I read Mathlib's SheafCohomology/Basic, the nonabelian H1 grep hits and PullbackContinuous's adjunction; none is a one-line specialization of the new result. Against C: all non-elementary inputs have node citations, all their statements were opened, quotes are verbatim, and generic off-unit tools are declared in split_report. Against D: the new node neither restates an item clause nor absorbs its construction/comparison argument, and it has no dependency on the item. Against E: all base schemes, flatness/lfp conditions, coefficient categories and cohomology conventions are matched as detailed above. Every proof step is below 2000 characters; none hides a long lemma.

## Unfinished work

None for this one-level stage-1 split. The new statement-only node is intentionally queued for a later split. Server dry-run results and delivery are recorded by the delivery tool.
