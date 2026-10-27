## Worker report

Item: lem-trf-affinoid-finite-galois-envelope. Group Q64, stage 1, 2026-10-24.

Files written: the item's JSON (split, seven proof steps); the four new JSON files listed below; citations.json and this report. Auxiliary write_split.py and the honest msearch.py log remain only in this sandbox. No repository or launcher file was written, no git command was run in the shared repository, and no Lean or compiler work was done.

## New nodes

- lem-trf-tate-noetherian-normal: statement, unsplit, no Mathlib match. Tate Noetherianity and normality are independent algebraic inputs, not normalization or the desired envelope.
- lem-trf-tate-variable-roots-separable-compositum: statement, unsplit, no Mathlib match. Describes a specific finite free coordinate-root extension and separability of a fraction-field compositum; it constructs neither an integral closure nor an affinoid Galois envelope.
- lem-trf-finite-algebra-affinoid-presentation: statement, unsplit, no Mathlib match. A general module-finite algebra over a strict affinoid acquires a Tate quotient Banach presentation; it assumes no Galois extension or normalization.
- lem-trf-affinoid-homomorphism-bounded: statement, unsplit, no Mathlib match. Automatic boundedness for any homomorphism of two already presented strict affinoids; it constructs no envelope.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, affinoid, Tate normalization, and Galois envelopes. There is no declaration giving all the item clauses. The existing restricted-series and affinoid modules under Sheaf are reference material, not attachments. General Mathlib normalization and field-theory hits are reused through existing nodes where applicable, not claimed as proofs of an analytic assertion.

## Sources wanted

WANTED: Kedlaya, More on affinoid algebras, https://kskedlaya.org/18.727/spectra2.pdf, Theorem 4 proof, PDF p.2, for the item and lem-trf-tate-variable-roots-separable-compositum.

WANTED: Kedlaya, Tate algebras, https://kskedlaya.org/18.727/tate-algebras.pdf, Propositions 4,5,7 and Corollary 11, PDF pp.5–7, for lem-trf-tate-noetherian-normal and the analytic input checks.

WANTED: Bosch, Lectures on Formal and Rigid Geometry, April 2008, https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf, section 1.2 Proposition 14 (printed p.15, PDF p.17), explicitly identifying normality, for lem-trf-tate-noetherian-normal.

WANTED: Conrad, Several approaches to non-archimedean geometry, https://math.stanford.edu/~conrad/papers/aws.pdf, Theorem 1.2.6(2),(3), printed p.6, and the quotient-norm paragraph and Exercise 1.2.4 on printed pp.5–6, for lem-trf-finite-algebra-affinoid-presentation and lem-trf-affinoid-homomorphism-bounded.

I read these primary sources online; none is locally archived in literature/. The item proof is marked agent, with its precise source locations and the variable-root clarification identified. The brief authorizes reporting WANTED rather than writing into literature/ or coord/. No SGA source is used.

## Corrections and scope

The item statement is unchanged. In particular there is no new characteristic-zero hypothesis, no claim that an individual C-to-B_i map is injective, and no replacement of Galois by merely normal. The source's generic phrase “normal closure” must be combined with its purely inseparable part (a). A finite inseparable extension cannot be embedded over its original base into a separable extension. For example, in characteristic p, X has no p-th root in Frac(K⟨X⟩), whereas K⟨Y⟩ with X=Y^p has that root. The source of the imported item already mentions the variable-root repair; the split implements it rather than changing the statement.

The current blueprint ancestor lem-trf-local-term-locality and the current unit sk-i-curve-zero were read from literature/blueprint/latest/. They now concern contracting correspondences; their text contains no finite affinoid Galois envelope assertion. This item belongs to the explicitly recorded historical analytic branch below that ancestor (through Temkin's normalization preparation), and the blueprint fields say so. This delivery changes no chapter/unit route, and does not pretend that the current ancestor's proof literally contains the analytic statement.

## Search and duplicate review

I searched the whole DAG by affinoid, Tate algebra, restricted series, normal closure, minimal prime, integral closure, p-power roots, and the relevant titles; blueprint_refs.py searches included affinoid, Tate algebra, Tate algebras, restricted series, restricted-series, 1.2.6, normal closure, Noetherian normal domain and 032L. The ancestor command reports lem-trf-local-term-locality; every new node has that ancestor and the item's complete via chain. Lean project searches found no attachment for any new analytic input. All recorded Mathlib searches were actually run by msearch.py and their output was read. Each new node has both alternative semantic phrasings, LeanSearch, Loogle, and source grep where pertinent. Their exact records are drawn from searches.jsonl. No service failure was recorded as absence.

I read Mathlib/RingTheory/MvPowerSeries/Restricted.lean: it constructs the restrictedness predicate and subring, not Noetherianity or normality. Mathlib/RingTheory/NoetherNormalization.lean treats polynomial finite-type algebras; a Tate algebra is not a polynomial finite-type algebra over K. The semantic boundedness hits AlgHom.toContinuousLinearMap and AlgHom.norm_apply_le_self have target K; the ContinuousAlgHom hits assume continuity. Neither supplies automatic boundedness into an arbitrary strict affinoid. Abstract purely inseparable/separable closure hits do not identify bounded roots of restricted series with Frac(T_q). Existing DAG finite-domain fraction-degree, finite-is-integral and normal integral-closure leaves are cited directly. All four new nodes remain statement-only, with no proof sketch in the statement.

## Not duplicates

lem-trf-tate-noetherian-normal vs lem-trf-tate-normalization-lift: the existing node embeds a Tate algebra finitely into a quotient; it states neither Noetherianity nor normality of the Tate algebra.

lem-trf-tate-noetherian-normal vs lem-trf-tate-weierstrass-norm-division: division/preparation is a possible proof input, not the Noetherian and normal-domain conclusions.

lem-trf-tate-noetherian-normal vs lem-trf-tate-gauss-multiplicative: Gauss multiplicativity does not give finite ideal generation or integral closedness.

lem-trf-tate-variable-roots-separable-compositum vs lem-weil-pbc-finite-rooted-extension: the existing node concerns finitely many rational-function coordinates and finitely many coefficient roots, not coefficientwise roots of restricted series or separability after a uniform Tate-field enlargement.

lem-trf-tate-variable-roots-separable-compositum vs lem-per-finite-extension-separable-core-bounded-exponent: the existing leaf bounds an abstract purely inseparable tail; it does not identify F^(1/q) as a finite free Tate-variable extension or assert that the resulting compositum is separable.

lem-trf-finite-algebra-affinoid-presentation vs lem-trf-affinoid-quotient-norm-topology: the existing node assumes a complete Banach algebra and a continuous surjective Tate presentation; the new node constructs an affinoid presentation for an initially purely algebraic finite algebra.

lem-trf-affinoid-homomorphism-bounded vs lem-trf-affinoid-finite-module-strictness: the existing node is about A-linear maps between already normed finite A-modules with bounded scalar actions; it cannot establish that the scalar action associated to an arbitrary affinoid algebra homomorphism is bounded without assuming the conclusion.

lem-trf-affinoid-homomorphism-bounded vs lem-trf-continuous-linear-map-norm-bound: the existing node assumes continuity; the new input proves automatic continuity for strict affinoid algebra maps.

lem-trf-finite-algebra-affinoid-presentation vs lem-trf-finite-affinoid-canonical-reduction: the latter assumes both algebras are already affinoid and studies reduction; it does not give a Banach presentation to an algebraic finite algebra.

## Review by Q64

I checked the actual source and node statements while writing this review. Kedlaya spectra2, Theorem 4 proof, p.2, starts with the finitely many minimal-prime quotients, then finite Tate normalization and normal closure. Parts (a) and (b) distinguish inseparable and Galois extensions. That is exactly the algebraic preparation being isolated here; I do not cite its spectral-completeness conclusion, since this item is a dependency of that conclusion. For the first new node I read Kedlaya's Propositions 4 and 5 and Bosch's explicit “factorial and hence normal” Proposition 14. For the other two analytic nodes I read Conrad's Theorem 1.2.6(2),(3) and the quotient-norm construction before Exercise 1.2.4. They apply to ordinary strict Tate quotients, complete nontrivially valued fields, and arbitrary finite commutative algebras, exactly as stated here; no discreteness or characteristic-zero assumption is used. The root-compositum node is the agent's precise additional algebraic formulation of Kedlaya part (a), not a claimed quotation of his theorem.

Step 1 uses the new Tate Noetherianity conclusion; lem-weil-pbc-finite-algebra-noetherian applies to the quotient because 1 generates it as a module. I opened lem-sc-finite-minimal-primes-over-ideal: it says exactly that there are finitely many minimal primes over the zero ideal in a Noetherian ring. I opened lem-per-nilradical-minimal-prime-intersection: it identifies their intersection with nilpotents, including its empty-family convention. Reducedness gives zero intersection; nonzeroness excludes the empty family. Each quotient by a prime is a domain directly from the definition. This does not assume C connected or equidimensional.

Step 2 uses exactly the injective finite Tate normalization map of lem-trf-tate-normalization-lift, applied to the proper kernel of the composite onto C/p_i. The kernel is proper because the quotient is nonzero. The finite-domain fraction-degree leaf explicitly concerns arbitrary injective finite maps of domains, so it applies without normality. The finite-algebra-is-integral leaf supplies the monic equations; I do not extract them from the definition of finiteness alone.

Step 3 uses the entire new root-compositum statement, with the finite field extension from step 2. To test its correctness, group every series in Y by exponents modulo q: the q^d restricted coefficient series in X give the displayed free basis of T_q over T. Since K is algebraically closed, its q-th roots exist uniquely in characteristic p and their absolute values are |a|^(1/q). Thus a null coefficient family remains null on taking q-th roots. In an algebraic closure, Frac(T_q) identifies with F^(1/q), since the q-th root of f/g is f^(1/q)/g^(1/q). For finitely many field generators alpha of L/F, each minimal polynomial has the form Q_alpha(Z^(p^e_alpha)) with Q_alpha separable. Choose e at least their maximum. Taking p^e_alpha-th roots of the coefficients produces a separable polynomial for alpha over F^(1/p^e_alpha), and enlarging this to F^(1/p^e) preserves separability. A field generated by finitely many such separable algebraic elements is finite separable. These are the mathematical reasons for the new node; they are not inserted as proof steps into that unsplit node. The characteristic-zero branch has q=1 and finite extensions are separable. This verifies existence, compatibility and finiteness without assuming the Tate fraction field perfect.

Step 4 uses only the actual conclusion of lem-weil-pbc-finite-galois-receiving-separable-extensions, on a single finite separable extension. Its supplied embedding fixes F'_i; all ring maps stay compatible. The integral-closure definition is opened and cited: elements satisfying monic equations form the closure. The equations over S_i from step 2 also have coefficients in T_i; therefore A_i embeds into B_i. This is not a claim that every element of the fraction field is integral.

Step 5 uses precisely Noetherianity and normality of T_i, together with finite separability of N_i/F'_i. I read Stacks algebra.tex, lemma-Noetherian-normal-domain-finite-separable-extension, Tag 032L: those are its hypotheses and finite integral closure is its conclusion. I also opened the existing integral-closure-finite-extension-normal node, which explicitly includes both normal-domain and fraction-field-identification clauses. Stacks 034L (lemma-integral-closure-in-normal) gives normality, and the existing leaf carries the fraction-field clause. I do not misuse the finiteness theorem as a fraction-field theorem. The Galois statement transfers along this actual identification.

Step 6 is elementary finite-generator arithmetic. Products of two finite generating families span a composite finite extension; the same family spans over the larger intermediate ring A_i; every coefficient lifts through C onto A_i. The product map's kernel is the intersection of the p_i because the component inclusions are injective. This step uses previous conclusions and writes the calculation; no extra node for transitivity or finite products is appropriate.

Step 7 first applies the finite-affinoid-presentation node to a nonzero finite T_i-algebra, giving an actual quotient Banach norm. The bounded-homomorphism node then applies to C and to T_i as sources, with B_i as target, and returns two separate positive constants. This avoids the circular shortcut of using finite-module strictness before bounded scalar actions are established. Both hypotheses (presented strict affinoids and complete nontrivially valued base) are checked, and no norm is assumed to be the spectral norm.

Small cases checked: C=K, C=K×K, and C=K⟨X,Y⟩/(XY). They verify s≥1, dimensions zero or mixed by components, and that only the joint map is required injective. For the root node I checked d=0, e=0, the identity field extension, L=F(X^(1/p)), and a separable Artin–Schreier extension. In the purely inseparable example the enlarged base already absorbs L; in the separable example q=1 suffices. The ordinary formal-series-ring results cannot substitute for the restricted-series assertions. For the finite-affinoid input I checked B=A, a nonzero quotient of A, and A[epsilon]/(epsilon^2): injectivity and reducedness must not be hypotheses, and are not. For boundedness I checked the identity and quotient maps, including nilpotents. Every non-elementary step cites statements that actually supply its conclusion; all 15 quotation entries copy the cited statements verbatim. No proof step exceeds 2000 characters or hides an inline comparison lemma. The root comparison is a new node. All new statements introduce every object, give their definitions or definition-node dependencies, contain single-escaped TeX, and have no proof/proof_deps. No new node is a restated clause of the item.

This is the author's direct-delivery self-review, as the current brief requires. No second worker or sub-agent was started. No repair note for this item exists. There was no earlier sandbox split to discard or redo. I corrected no item hypothesis; the substantive repair relative to the informal source is making the positive-characteristic base enlargement and the two distinct module structures explicit.

## Unfinished work

None at stage 1 beyond the four explicitly unsplit child statements, which are intentionally left for their own items. Dry-run and delivery results are recorded by the required delivery commands.
