# Stage-1 delivery: lem-trf-fixed-tensor-kernel-stalk-criterion

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fixed-tensor-kernel-stalk-criterion.json: statement item, split into four steps; Mathlib has ordinary localization tools but not the full normalized contracted-prime tensor statement.
- citations.json: six step/node entries, each quoting the cited statement verbatim.
- report.md: this report. searches.jsonl records five actual searches in this session.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for fixed-tensor, contracted-prime tensor, kernel-localization, and universal-injectivity notions. No declaration states all clauses of this item. The ordinary kernel-localization and maximal-injectivity declarations are Mathlib, not project attachments.

## WANTED

None. All mathematical sources used are available in literature/stacks-project/algebra.tex.

## Corrections and route

The live item was unsplit and the sandbox had no item or report to preserve. I retained the entire statement, its statement dependencies, provenance, blueprint fields and the earlier recorded searches, and appended only searches actually run for Q99. There is no statement dispute. No Lean files, compiler or build commands were used.

The source is Tag 05CL, lemma-universally-injective-check-stalks. Its proof keeps an arbitrary test module N fixed before quantifying over N; the present statement isolates that fixed-N argument. I checked 00CS (proposition-localization-exact), 00HN (lemma-characterize-zero-local), and 00E0 (lemma-Zariski-topology), with their tags verified against tags/tags. The latest blueprint files read were sec-trace-formula/sk-i-curve-zero/_section.md and lem-trf-local-term-locality.md and its proof. The current ancestor concerns contracting local terms; the inherited provenance points to the older lower flatification-support chain. This delivery only proves its assigned algebra support lemma and does not change the chapter or unit route or claim that the latest blueprint explicitly contains this algebra statement.

## Search and reuse

DAG statement/title searches covered localization of kernels, exact localization, detection at maximal ideals, vanishing of modules and annihilators. Blueprint searches for "localization kernel", "injectivity maximal", and "05CL" found no equivalent blueprint theorem. I read the existing contracted-prime tensor comparison in full: it includes the needed naturality equation, not just object isomorphisms. I reused lem-weil-pbc-localization-module-exact, a Mathlib leaf stating exactness for arbitrary modules, and lem-weil-pbc-proper-ideal-contained-in-maximal, a Mathlib leaf supplying a maximal ideal above any proper ideal. No additional node is needed for a few-line restriction of a commutative square to kernels, nor for the annihilator contradiction once maximal-ideal existence and the fraction criterion are cited.

Five new msearch.py queries are logged verbatim in searches.jsonl and appended to the item's mathlib_searches. LeanSearch and both LeanFinder phrasings returned tensor-injectivity results with extra flatness/invertibility hypotheses or ordinary localization results. Loogle returned LinearMap.toKerLocalized_isLocalizedModule. The grep found it at Mathlib/Algebra/Module/LocalizedModule/Submodule.lean:360 and injective_of_localized_maximal at Mathlib/RingTheory/LocalProperties/Exactness.lean:103. I read Submodule.lean:326--367 and Exactness.lean:25--117. These are ordinary localization facts and do not assert the specific tensor comparison over the contracted base, so the full item is not a one-line Mathlib specialization.

## Not duplicates

No new nodes. In particular, I did not create a localization-kernel lemma duplicating exact localization, an injectivity-detection lemma duplicating 00HN, or a node restating one of the item's clauses. The existing ring-only prime-localizations-jointly-injective node cannot be used for arbitrary modules; the existing bijective-at-maximal node assumes bijectivity and cannot be cited as injectivity detection. Their statements were read and neither was misapplied.

## Review by Q99

I checked delivery-errors B--E against the node and the opened sources. There are no new statement-only nodes or Mathlib leaves to audit. The statement is self-contained through its four retained definition/comparison dependencies, and the proof uses ordinary fractions with no finite-generation or presentation assumptions. TeX has single escapes after JSON decoding. The proof dependency list is exactly the union of step uses. No step exceeds 2000 characters, and the only constructions done inline are the routine kernel restriction and annihilator argument described below.

Step 1 uses the exact-sequence assertion of lem-weil-pbc-localization-module-exact over A, not over R: K to X to Y is exact by the definition of K, and A minus q is multiplicative because q is prime. This gives image equal to kernel; it does not by itself assert that the localized inclusion is injective. I explicitly prove that injectivity using the fraction equality criterion from def-weil-pbc-module-localization and the original inclusion's injectivity. This repairs a possible hidden identification between an image submodule and the localized kernel domain. Its scalar linearity follows directly from (a/t)(k/s)=ak/(ts).

Step 2 cites the literal naturality equation in lem-trf-contracted-prime-tensor-comparison. I checked its hypotheses with P=M, P'=M', v=u and the same R-module N; it assumes no flatness. The proof writes both directions of the kernel restriction using the invertibility of c on source and target, so the resulting isomorphism is specifically c composed with the localized inclusion, not an unspecified isomorphism of modules. This is a few-line consequence of the cited equation and does not hide a separate comparison lemma.

Step 3 uses the localization definition to localize the zero kernel, then the kernel isomorphism already proved. Its maximal-ideal implication includes the elementary argument that a maximal ideal in a commutative ring is prime. Injectivity is equivalent to zero kernel because these are linear maps of modules over rings, with subtraction available.

Step 4 cites the statement of lem-weil-pbc-proper-ideal-contained-in-maximal for the proper ideal I={a:ak=0}; additivity and stability under multiplication show that I is an ideal, and k nonzero makes 1 absent. I checked that its maximal ideal lies in A, and that the denominator supplied by the localization definition lies outside that same ideal. The contradiction s in I and s outside m proves zero kernel. This expands 00HN's annihilator proof rather than taking an uncited module-detection theorem. The cited node really gives existence above an arbitrary proper ideal, not only existence in a nonzero ring. I verified all six citation quotes by literal substring checks of the live statements.

Small cases: for A the zero ring all unital A-modules are zero; both quantifications are empty and the map is injective, so no nonzero-ring hypothesis is missing. For N=0 or M=0 all source tensors and kernels vanish. For u the zero map, the assertion reduces to zero detection for M tensor N. For R=A=Z, u multiplication by 2 and N=Z/2, tensoring makes u zero and noninjective; the bad maximal ideal (2) also gives a zero map on a nonzero localized tensor, whereas other prime tests vanish. This checks that the proof never incorrectly deduces tensor-injectivity from injectivity of u or presumes N flat. Finally, an algebra maximal ideal can contract to a nonmaximal base prime (Z to Q, q=0), and the proof consistently tests at the algebra maximal ideal and localizes the base at its contracted prime only through the cited comparison.

## Unfinished work

None for the one-level stage-1 split. The independent maintainer review remains the review of the delivery.
