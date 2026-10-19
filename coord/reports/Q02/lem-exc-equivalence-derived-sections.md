1. Files written

- dag/nodes/sec-smooth-purity/lem-exc-equivalence-derived-sections.json — statement, split into seven proof steps; not a Mathlib leaf. Statement unchanged. No new nodes and no new Mathlib leaves.
- citations.json — 14 records, one verbatim statement excerpt for every step/node citation.
- report.md — this report. searches.jsonl is the actual msearch command log.

2. Attachments

None. Searched the read-only slopmaster2 WeilConjectures source for the exact blueprint tag/id and for equivalence, rightDerived, derived sections, and the possible comparison names. The general exact/derived category framework gives ingredients; no project declaration gives this entire degreewise statement with its arbitrary-resolution and degree-zero normalization clauses. Upstream master is not used as evidence of a finished proof.

3. WANTED

None. All sources used are present in literature/stacks-project/.

4. Problems found and changes made

The imported node was a correct statement with no proof. Its original searches were retained. New logged searches used two semantic phrasings, Loogle for both the expected comparison and the resolution API, grep in CategoryTheory, and LeanSearch. I read the returned declarations in Mathlib/CategoryTheory/Abelian/RightDerived.lean:114,126,141,164,376, as well as Injective/Resolution.lean:94,102,108. rightDerivedNatIso at Functor/Derived/RightDerived.lean:133 compares functors with the same source; it does not state this precomposition-by-equivalence comparison. The resolution lemmas are ingredients rather than a one-line specialization giving the whole item. No search failure was reported as absence and no search was invented.

Before considering a subordinate lemma I searched the full DAG and blueprint for equivalence, derived functors and injective resolution, and the DAG for 015M, 015Z, 013P and the returned Mathlib names. This found all necessary existing nodes. In particular the map-via-lift leaf is more appropriate than using the bounded-below derived-category naturality node, whose statement additionally assumes derived categories. No extra assumptions of that stronger statement are imported. The site-equivalence cohomology node is a site-specific consequence, not a duplicate of the present arbitrary abelian-category tool. No new nodes were created.

The main-20261015 ancestor proof places the application at paragraph 3, first sentence, where etale cohomology is identified with continuous Galois cohomology. The already-reviewed parent also uses the tool to change the encoding of module sheaves. The item's historical sec-smooth-purity/sk-prop-a1-kummer binding is retained; the main blueprint files are now under sec-six-functors-basics. I read both the chapter/unit records and the current ancestor statement and proof. Nothing changes the chapter or unit route. All proof inputs are Mathlib leaves, so there are no undeclared off-route tool uses. No SGA source is used.

5. Unfinished work

None for this stage-1 split. No Lean was written or compiled.

## Review by Q02

I read Stacks derived.tex Tag 015M, lemma-compose-derived-functors, including its proof on an injective resolution; Tag 013K, lemma-injective-resolutions-exist, proof of (1); Tag 013P, lemma-morphisms-lift, part (2); Tag 05TD, lemma-left-exact-higher-derived; and Tag 015B, lemma-higher-derived-functors, (2). I also read homology.tex Tag 015Z, lemma-adjoint-preserve-injectives. These justify the exact-equivalence special case without the Grothendieck or K-injective hypotheses that would be unnecessary here. There are no new nodes requiring independent sources.

For step 1 I opened def-sp-enough-injectives, def-sp-injective-resolutions and def-sp-abelian. Their statements supply embeddings into injectives and the kernels and cokernels used in the explicit successive-cokernel construction. Exactness is checked directly: the next differential is a cokernel projection followed by a monomorphism, hence its kernel is the preceding image. This is the usual object-resolution construction, with zero negative degrees. I wrote the construction rather than appealing to an uncited existence theorem.

For step 2 I opened lem-weil-pbc-equivalence-injective-resolutions. Its clauses (1)–(3) explicitly give exactness, preservation of injectives, the transported injective resolution and augmented chain maps. The given E is additive and an equivalence, exactly its hypotheses. No assertion about section cohomology is taken from that lemma.

Step 3 uses def-sp-left-exact-additive solely for termwise additive functors and the meaning of the right-derived section computation. The chain equation is written out using the supplied alpha; its inverse equation follows by multiplication with inverse components. Applying kernel/image quotients to mutually inverse chain maps gives mutually inverse cohomology maps by composition. This is elementary and not a separate new lemma.

For step 4 I opened lem-weil-pbc-derived-functor-map-via-lift. Its statement supplies the isomorphism iota for every specified injective resolution, not just a chosen resolution. It applies to S on C and T on B, both additive, with enough injectives in their respective sources. D only needs to be abelian. The comparison is the displayed composite j inverse, H(alpha), i. This gives the prescribed component formula, rather than asserting an unspecified isomorphism.

For step 5 I opened lem-weil-pbc-injective-resolution-lift-exists. Its statement gives the strict augmented lift for resolutions vanishing in negative degrees, exactly the ones constructed in step 1. The equivalence lemma then supplies E(u). I checked that map-via-lift supplies both displayed equations, one for S and one for T, with the correct source and target. Naturality of alpha on u in each degree supplies the intervening square. Cancelling i and j gives the naturality equation in the correct direction. No assertion of naturality is borrowed from a node that only asserts objectwise well-definedness.

Step 6 uses those same three statements, now with f the identity and J any other resolution of X. The map-via-lift node explicitly states that the derived construction is a functor, so its identity maps are identities. Consequently the same square proves equality of the two comparisons. This proves the arbitrary-resolution clause as well as choice independence, without needing an uncited comparison-homotopy theorem or a functorial choice of chain lifts. The inverse naturality equation follows by cancelling the already-constructed component isomorphisms.

For step 7 I opened lem-sp-derived-well-defined and def-sp-left-exact-additive. The former explicitly states the natural R^0 v = v identification; the latter defines preservation of kernels. The explicit kernel calculation shows that these canonical identifications give alpha itself. The key equation is naturality of alpha on the augmentation s, not a claim that an arbitrary degree-zero comparison must equal alpha. Negative terms are zero, so there are no degree-zero boundaries. Left exactness is used exactly here.

I checked the elementary steps against their stated definitions and the non-elementary steps against each cited statement (C1/C4); citations.json records exact excerpts. The proof never uses the proof of another node as its interface. It is a genuine resolution argument, with no new node restating a clause (D1/D2). All objects are the given C,B,D and E,S,T,alpha; neither an auxiliary coefficient category nor a stronger category hypothesis is silently substituted. The statement is true as imported, so no STATEMENT-DISPUTED correction is needed. Edge cases checked: identity equivalence and alpha identity give the identity; a nonidentity alpha in degree zero is retained; zero functors and the zero abelian category give the unique zero-object isomorphism; q>0 on an injective X is the zero-object comparison. No faithfulness, exactness or injective-preservation assumption on S or T is used. Every proof step is below 2000 characters (maximum 808); there is no long step hiding a subordinate standard lemma.
