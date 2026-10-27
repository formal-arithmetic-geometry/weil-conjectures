# Q93 repair report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-lisse-lattice-potential-kummer-tameness.json: existing statement, unchanged verbatim; four assembly steps, 2156 characters in total.
- dag/nodes/sec-six-functors-basics/lem-sfb-residually-trivial-lattice-monodromy.json: statement; unsplit; no Mathlib match after five logged searches. This is finite-level congruence monodromy, not boundary tameness.
- dag/nodes/sec-six-functors-basics/lem-sfb-lisse-lattice-constant-reductions.json: statement; unsplit; no Mathlib match after five logged searches. This is global compatible trivialization and reconstruction on any scheme, not the existence of a cover with local bases.
- citations.json: every citation of every assembly step, copied verbatim from the cited statements.
- report.md: this report. searches.jsonl is the search command's unmodified log. repair.py and write_report.py are sandbox-only preparation scripts, not DAG deliveries.

## Attachments

None. The project search under lean/WeilConjectures for the blueprint tag and for potential Kummer/residual-monodromy wording gave no finished declaration. The live Sheaf.Paper.LisseLatticePotentialKummerTameness theorem lisseLattice_potential_kummer_tame ends in sorry. Its statement and eight-step docstring agree with the repair baseline, so this is a stage-1 re-split, not ATTACH. No Lean file was written or compiled.

## WANTED

None. The Bhatt–Scholze and ILO PDFs, and the Stacks source, were present and read locally.

## Returned point and repair

The return asks to distribute the 7666-character proof among at least two new statement-only items of comparable size, while keeping this statement and reducing its assembly to at most 3000 characters. The named sandbox initially contained only dispatcher marker files; there was no retained node, report or previous search log. I copied the current repository item, whose eight steps exactly match the returned lengths, and preserved all metadata and recorded earlier searches. No git command was run in the shared repository.

Two independent work items now carry the substantial arguments: the coefficient/site bridge, finite congruence filtration and actual monodromy torsor construction (old steps 1, 4, 5), and the global compatible-basis recursion followed by full-faithful reconstruction (old steps 7, 8). Their statements have 2645 and 1909 characters respectively. Both are unsplit, with empty proof and proof_deps and null proof_origin. Neither restates the item's boundary conclusion: the first has no boundary geometry and only finite-level conclusions; the second has no cover selection, monodromy or boundary and assumes that every finite reduction is already globally free. Existing nodes already provide the geometric splitting used in old step 6 and the strict-local algebra in old step 3; their applications, residual cover selection (old step 2), and the final pullback identification remain as short assembly. There is no need for a new node that only repeats the existing geometric splitting theorem.

The complete old argument is retained below, not shortened or replaced by a vague promise. Its assignment to the new work items is explicit so their future workers have the original mathematics. The new nodes' statements ask for precisely the interfaces those arguments establish. The item statement, coefficient categories, hypotheses, universal parameter choices and edge cases are unchanged. This repair changes no chapter or unit route.

## Sources read

For the item I read Bhatt–Scholze, Definitions 6.8.1 and 6.8.3, Lemma 6.8.2 and Proposition 6.8.4(1) (printed pp.58–60; especially p.59), and ILO Exposé IX Proposition 2.1 with the strict-local root description and its continuation (printed pp.133–134; PDF pp.139–140). The latter is the geometric input already isolated in lem-sfb-strict-local-prime-to-p-kummer-splitting.

For the monodromy node I read the same Bhatt–Scholze integral reduction assertion and Stacks 099Y, proetale.tex lemma-compare-locally-constant (lines 4121ff), and pione.tex theorem-fundamental-group and section-finite-etale-under-galois (03SF, lines 1217ff and 1344ff). They supply finite etale models and the exact image quotient torsor. The finite congruence filtration is the old explicit agent argument, not a purported verbatim theorem in those sources. The new node records this honestly. In particular the finite Galois group, rather than the degree of an arbitrary cover, must have order prime to p.

For the constant-reductions node I read Proposition 6.8.4(1) on an arbitrary scheme and the continuous-function identity in Lemma 6.8.2, and checked the statement of lem-sfb-totally-disconnected-coefficient-realization for finite discrete matrix sets. Proposition 6.8.4 leaves its proof to the reader; the old argument supplies the required extra global basis recursion in this new agent-formulated lemma. Global trivializations at each level do not themselves constitute compatible markings. The new conclusion therefore explicitly gives compatibility and reconstruction, extending any prescribed first basis.

The definition of regular scheme already includes locally Noetherian and regular local rings; I checked it rather than silently inserting a Noetherian hypothesis. The SNC statement and the strict henselization statement retain the chosen regular-parameter tuple. No different purity or trace route is introduced.

## Review by Q93

I checked the return against the actual node files, not only their dependency lists. The four assembly steps together contain 2156 characters; none is longer than 2000. The substantial matrix and basis arguments are new unsplit work items rather than hidden long steps.

Step 1 uses the unconditional finite-model clause of the new monodromy statement, which explicitly concerns the actual internal pulled-coefficient quotients F_n. The existing finite-set-monodromy-torsor statement assumes precisely a nonempty connected scheme and a finite locally constant etale set sheaf, both available on S. It produces a connected finite etale torsor trivializing that underlying set. The finite coefficient clause (1) of cor-galois-lisse-representations is an equivalence preserving scalar extension, not merely a fully faithful embedding; its trivial underlying action is trivial as an A_1-linear action. I use no clause (2) about Noetherian l-adic sheaves. These facts give a free residual fibre of rank d; d=0 is valid. H is chosen once before Y,D,g.

Step 2 reads both strict-henselization statements: Noetherianity and regularity are preserved from the original regular local ring. The regular-local factorization statement explicitly supplies a domain and prime parameter elements; it does not merely define normal crossings. Thus the localization is a nonzero domain and its spectrum is connected. The Cartesian-coefficient statement explicitly says the module inverse image is exact with unchanged underlying inverse image. It preserves the scalar cokernels and the finite free local models; the map through H makes the first reduction constant. I have not used the existence of a root tower as a substitute for its parameter hypotheses. Characteristic p survives all these k-algebra localizations and strict henselization.

Step 3 uses the new monodromy lemma with its additional hypothesis F_1 constant, only on the connected puncture U. Its torsor group is the actual image Q_n, with ell-power order. Since p and ell are distinct primes, this is exactly the prime-to-p group hypothesis of the existing strict-local splitting node; that node explicitly covers Noetherian regular strictly henselian R and a subset of regular parameters, including the empty tuple. For each n the root level m_n may differ. A projection from the divisibility limit T to the m_n-root scheme pulls a torsor section back to T; the section then pulls back the actual trivialization of F_n on P_n. This is a composition of the given maps, not an assertion that some arbitrary finite cover is tame. Cartesian exactness supplies precisely N_T/varpi^nN_T.

Step 4 uses the new constant-reductions lemma on T itself. Its hypotheses intentionally impose neither connectedness nor a Noetherian condition on T, and they do not require compatible initial trivializations. Pullback of a lisse module stays lisse by pulling back its finite free local models. The conclusion gives the integral isomorphism and its ordinary rational scalar extension. The tensor comparison statement supplies the actual inverse-image tensor isomorphism and the Cartesian coefficient maps identify the rational pullback with E_T tensor N_T. Thus the final constant object is the specified continuous-coefficient module with fibre E^d. The final assertion applies separately to every allowed point and parameter choice. Empty boundary tuple and rank zero are explicitly retained.

For the monodromy work item I verified each original ingredient against its cited statement: coefficient realization is natural in A to A_n and A to E; the internal-module equivalence keeps underlying sheaves; reduction equivalence gives finite locally free reductions and their quotient transitions; finite-site comparison has no Noetherian restriction; cor-galois clause (1) preserves reduction of scalars. The arithmetic nodes say A is a DVR with finite residue field and A_n finite local with surjective transitions. The residue characteristic is ell because the extended absolute value places ell in the maximal ideal. The filtration K_(n,i) has quotients Mat_d(kappa), with the cancellation carried out in A before reduction; no division inside A_n is asserted. The regular left action of Q_n and commuting right translations give the torsor, and the base-change clause of the Galois correspondence kills exactly this image. The new statement asserts all of these finite-level consequences together and no uniform finite trivializing cover.

For the reconstruction work item I checked the distinction between local compatible bases and global ones. The existing local-bases node only supplies bases after a covering and is insufficient here. The discrepancy is a section of the finite constant GL_d(A_n)-sheaf; the realization statement identifies it with a continuous locally constant function, even if X is disconnected. GL_d(A_(n+1)) to GL_d(A_n) is surjective by entry lifts and the unit determinant criterion (alternatively the existing square-zero matrix-lift statement). A set-theoretic section of this finite surjection is continuous; composing lifts the discrepancy function globally. Correct the next basis by this lift and induct, starting with any chosen b_1. The reduction equivalence is fully faithful on X itself and hence reconstructs the global integral isomorphism. This does not assume that an ordinary constant-sheaf functor commutes with arbitrary inverse limits.

I tested small cases in both new statements: n=1 gives the trivial congruence kernel; d=0 gives the one-element matrix group, identity torsor and zero module. For E=Q_ell, d=1, n=2, the kernel is the additive residue field, so the claimed ell-power order has the expected nontrivial example. A nonconstant residual representation is correctly excluded from the torsor-order conclusion. For the second statement, disconnected X permits different basis discrepancies on its components; lifting the finite-valued function works without requiring them to agree. The empty scheme is vacuous. The integral equivalence is invoked on the possibly non-Noetherian limit scheme, where its statement explicitly allows any scheme. When r=0 the strict-local splitting theorem uses m_n=1 and the tower is the identity, as required.

I checked delivery-errors B–E: all new objects are introduced and notion definitions cited; TeX has single mathematical backslashes after JSON decoding; sources distinguish exact theorems from agent consequences; no proof sketch is hidden in a new statement. Every assembly use has an existing or newly delivered node and a verbatim quotation in citations.json. The new nodes depend only on definitions, not on the item, so no circular inference is introduced. The Mathlib results were read: adic completion of ordinary modules, matrix residue arithmetic, group cohomology, free sheaf constructors and manifold local frames do not give either requested sheaf statement. All ten new queries are the exact recorded tool queries, including two natural-language phrasings for each new node; every service responded successfully. Old item searches are retained without fabricating reruns. No statement dispute was found and no hypotheses were added to the item.

## Not duplicates

lem-sfb-residually-trivial-lattice-monodromy vs def-sbc-affine-torsor-equivariant-algebra: the existing statement concerns Equivariant algebra on the split components; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs det-lem-int-integral-heart-local-model: the existing statement concerns Local models of integral constructible complexes and their cohomology; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs det-pe-finite-local-systems-etale-cover: the existing statement concerns Etale cover retaining finitely presented constant module models; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs det-pe-finite-local-systems-twist: the existing statement concerns Etale models of finitely presented local systems; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs det-pe-uniform-finite-type-model-etale-cover: the existing statement concerns Etale trivializations for a fixed finitely generated module model; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs det-proper-heart-bound-torsion: the existing statement concerns The torsion bound over a weakly contractible base; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs det-uniform-constructible-ext-torsion: the existing statement concerns The torsion stratum bound; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-exc-etale-field-gsets: the existing statement concerns Etale schemes over a field and continuous G-sets; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-exc-etale-open-subgroup-fixed-field: the existing statement concerns Open subgroups of an absolute Galois group; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-exc-finite-galois-algebra-tensor-decomposition: the existing statement concerns Affine fibre-product consequence of a finite Galois tensor decomposition; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-exc-finite-galois-sheaf-sections-coproduct: the existing statement concerns Sections on a finite open-and-closed coproduct in a small etale site; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-exc-finite-galois-tensor-decomposition: the existing statement concerns Tensor decomposition for a finite Galois field extension; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-per-galois-descent-monodromy-tensor: the existing statement concerns Monodromy and tensor of modules descended along a finite Galois cover; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-per-noetherian-constructible-galois-partition: the existing statement concerns Simultaneous Galois partitions for Noetherian constructible module sheaves; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-invariant-basic-open-descent: the existing statement concerns Unique descent of an invariant affine basic-open morphism; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-component-image-orbit: the existing statement concerns Image of one stabilizer component is its label orbit; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-component-image-orbit-backward: the existing statement concerns Backward implication of the affine torsor component image orbit criterion; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-component-image-orbit-forward: the existing statement concerns Forward implication of the affine torsor component image orbit criterion; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-equivariant-descent: the existing statement concerns Descent to the whole equivariant function algebra; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-equivariant-descent-algebra: the existing statement concerns Algebraic reconstruction from orbit data; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-equivariant-orbit-product: the existing statement concerns Equivariant algebra as product of stabilizer fixed rings; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-fixed-orbit-data-of-action: the existing statement concerns Canonical orbit data of a finite action; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-fixed-puncture-compatibility: the existing statement concerns Fixed-orbit projection compatibility; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-fixed-puncture-descent: the existing statement concerns Descent along a connected affine torsor to fixed-ring punctures; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-fixed-puncture-descent-core: the existing statement concerns Fixed-orbit affine torsor descent step; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-fixed-puncture-geometric: the existing statement concerns Geometric fixed-orbit construction; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-fixed-puncture-orbit-data: the existing statement concerns Finite orbit representative data; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-invariant-puncture-etale: the existing statement concerns Etaleness of the invariant principal open of an affine torsor; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-orbit-component-descent: the existing statement concerns Descent of individual fixed-orbit components; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-representative-component-cover: the existing statement concerns Coverage and disjointness of representative components; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-single-stabilizer-component: the existing statement concerns Descent of one stabilizer component; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-single-stabilizer-component-open: the existing statement concerns Existence of the open stabilizer component; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-single-stabilizer-component-section: the existing statement concerns Section equation for the stabilizer component; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-split-label-laws: the existing statement concerns Cocycle laws for labels in a pulled-back splitting; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-split-point-lifting: the existing statement concerns Point lifting to explicit split sections; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-stabilizer-section-mono: the existing statement concerns Monomorphy of a descended section with exact stabilizer; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-affine-torsor-stabilizer-section-open: the existing statement concerns Openness criterion for a descended stabilizer section; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-cartier-stalk-normalization-product: the existing statement concerns Integral-closure product model of a Cartier torsor normalization over the actual DVR stalk; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-equivariant-orbit-model: the existing statement concerns Equivariant orbit model; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-field-torsor-component-galois-group: the existing statement concerns Galois group of a field component of a finite torsor; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-field-torsor-galois-components: the existing statement concerns Galois field components of a finite group torsor; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-fixed-orbit-product-equiv: the existing statement concerns Fixed orbit product comparison; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sbc-fixed-orbit-product-equiv-compatible-model: the existing statement concerns Compatible finite orbit model; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sf-comparison-finite-models-of-etale-finite-values: the existing statement concerns Comparison transports finite etale constant models; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sf-proetale-comparison-counit-localization: the existing statement concerns Comparison counit compatibility with etale restriction; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sf-proetale-finite-models-etale-cover: the existing statement concerns Combine type opens and uniform finite-model descent; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sf-proetale-lisse-finite-models: the existing statement concerns Finite geometric stalks make nonempty local models finite; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sf-proetale-locally-constant-origin: the existing statement concerns Locally constant pro-etale sheaves with finite values are of etale origin; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sf-proetale-model-type-opens: the existing statement concerns Open loci of the types of constant local module models; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sf-proetale-origin-from-finite-models: the existing statement concerns Comparison lower star descends finite local models; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sf-proetale-uniform-finite-model-etale-cover: the existing statement concerns Etale trivializations for one fixed finite constant model; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sp-proetale-finite-underlying-models: the existing statement concerns Objectwise finite underlying set models from locally constant modules and finite stalks; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-comparison-finite-local-constancy-reflection: the existing statement concerns Reflection of finite local constancy by comparison; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-comparison-stratified-counit: the existing statement concerns Invertible comparison counit for finite stratified models; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-comparison-stratified-essential-image: the existing statement concerns Gluing classicality through a finite stratification; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-connected-torsor-subgroup-quotient: the existing statement concerns Connected subgroup quotients of a finite etale torsor with geometric fibre cardinality; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-finite-coefficient-intrinsic-constructibility: the existing statement concerns Intrinsic finite constructibility in the fixed coefficient presentation; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-finite-monodromy-trivializing-torsor: the existing statement concerns A connected finite monodromy torsor trivializing a finite locally constant module sheaf; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-finite-ring-constructible-sheaf-origin: the existing statement concerns Constructible sheaves over a finite ring have etale origin; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-finite-set-monodromy-torsor: the existing statement concerns Connected monodromy torsor trivializing a finite locally constant sheaf of sets; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-fixed-module-constructible-origin: the existing statement concerns Fixed-module constructible sheaves have etale origin; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-proetale-constant-module-constructibility: the existing statement concerns Constructibility is independent of the constant-module encoding; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-proetale-finite-model-local-constancy: the existing statement concerns Finite constant models in localized pro-etale sites; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-proetale-finite-model-stalks: the existing statement concerns Finite geometric stalks from finite constant models; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-weil-pbc-representable-pullback-constant-evaluation: the existing statement concerns Representable pullback is constant from exhaustive evaluation; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs new-lem-pur-a1-pullback-lift: the existing statement concerns Lifting affine-line pullback endomorphisms to the base; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs new-lem-pur-etale-a1-pullback-full: the existing statement concerns Fullness of ordinary etale affine-line pullback; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs new-lem-pur-intrinsic-lisse-fixed: the existing statement concerns Finite lisse condition in intrinsic and fixed-module coordinates; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs sk-lem-int-integral-heart: the existing statement concerns Structure of integral constructible complexes; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs sk-lem-uniform-constructible-ext: the existing statement concerns Uniform Ext bound; the new statement additionally controls the actual finite lattice reductions by the residual congruence kernel and obtains ell-power image torsors, which that statement does not assert.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sfb-prime-to-ell-linear-image-finite: the existing statement starts with a prime-to-ell profinite group and concludes finite rational image; this node starts with trivial residual integral monodromy and concludes ell-group images at each finite level.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sfb-etale-local-monodromy-realization: the existing statement gives etale-local rational representation models, with topological finiteness hypotheses, without the residual congruence restriction or the actual finite ell-group torsors.

lem-sfb-residually-trivial-lattice-monodromy vs lem-sfb-integral-lisse-reduction-equivalence: the existing equivalence supplies compatible finite reductions and reconstruction; it does not bound the finite monodromy image or construct ell-group torsors.

lem-sfb-lisse-lattice-constant-reductions vs lem-sfb-integral-lisse-reduction-equivalence: the existing equivalence requires a compatible tower morphism to reconstruct an isomorphism; the new assertion makes the individually given global trivializations compatible first.

lem-sfb-lisse-lattice-constant-reductions vs lem-sfb-integral-lisse-tower-local-bases: the existing statement gives compatible bases after a pro-etale covering; the new assertion gives global bases on X itself from individually global finite-level bases.

lem-sfb-lisse-lattice-constant-reductions vs lem-sfb-integral-lisse-tower-effective: the existing statement gives a lisse limit, not a global free module or compatible global bases.

lem-sfb-lisse-lattice-constant-reductions vs lem-sfb-integral-lisse-module-complete: the existing statement gives completeness of a lisse module, not compatible global bases from separately constant reductions.

lem-sfb-lisse-lattice-constant-reductions vs lem-sfb-integral-square-zero-matrix-lift: the existing statement lifts an invertible matrix in an ordinary quotient ring; the new statement globalizes finite-valued discrepancy lifts and reconstructs a sheaf isomorphism.

lem-sfb-lisse-lattice-constant-reductions vs lem-sfb-constant-reductions-finite-projective-model: the existing statement concerns derived perfect models on weakly contractible affine schemes; the new one concerns degree-zero lisse lattices, globally on any scheme, with compatible global bases.

lem-sfb-lisse-lattice-constant-reductions vs lem-sfb-wcontractible-constant-reductions-ml: the existing statement proves a Mittag-Leffler property on weakly contractible affines, not a globally free lattice on any scheme.

lem-sfb-lisse-lattice-constant-reductions vs lem-weil-pbc-compatible-finite-derived-trivializations: the existing statement produces a pro-etale cover with compatible derived trivializations, not compatible bases on the original X.

lem-sfb-lisse-lattice-constant-reductions vs lem-poincare-compatible-integral-root-bases: the existing statement compares particular root-of-unity and residue diagrams after a cover, not arbitrary globally trivial finite reductions on X.

Whole-DAG searches included the source tags 03SF and 099Y, Proposition 6.8.4, congruence kernels, residual monodromy, constant reductions, and compatible bases/trivializations. Whole-blueprint searches used congruence, residual, finite monodromy, compatible bases, constant reductions, reduction tower, and parameter-root. No imported statement states either new assertion. blueprint_refs.py ancestor reports no imported ancestor for this added-input chain, so the inherited null from.node is retained, with the exact tame-boundary paragraph and via chain extended by this item. same_as is empty.

## Full retained argument and assignment

This is the complete returned proof in its original wording. It is supporting handoff material in this report, not proof steps in the new unsplit nodes.

### Original step 1 → lem-sfb-residually-trivial-lattice-monodromy

Write $A=\mathcal O_E$, $A_n=A/\varpi^n$ and $F_n=M_0/\varpi^nM_0$. First identify the pulled condensed coefficient rings with the continuous-function coefficient sheaves, naturally for $A\to A_n$ and $A\to E$, by lem-weil-pbc-continuous-coefficient-realizations. Pass between internal modules and sheaf modules using def-weil-pbc-internal-abelian-sheaf-module-equivalence; its underlying sheaf is unchanged, so finite free local trivializations are unchanged. By lem-sfb-integral-lisse-reduction-equivalence, $(F_n)$ is a tower of finite locally free $A_n$-sheaves with $F_{n+1}/\varpi^nF_{n+1}\cong F_n$. By det-pe-finite-local-systems-twist every $F_n$ comes from an etale finite locally constant module sheaf. Thus the finite-coefficient correspondence may be applied to these actual reductions, rather than to a different coefficient model.

Cited nodes: lem-weil-pbc-continuous-coefficient-realizations, def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-sfb-integral-lisse-reduction-equivalence, det-pe-finite-local-systems-twist.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definitions 6.8.1, 6.8.3, Lemma 6.8.2(1), Proposition 6.8.4(1); Stacks 099Y (proetale.tex, lemma-compare-locally-constant).

### Original step 2 → Assembly step 1 (the two existing residual-cover inputs)

Apply lem-weil-pbc-finite-set-monodromy-torsor to the underlying finite locally constant set sheaf of $F_1$ on the nonempty connected scheme $S$. It gives a connected finite etale surjection $c:H\to S$ on which that set sheaf is constant. In cor-galois-lisse-representations(1), a trivial action on the underlying set is exactly a trivial action on the module; hence $c^*F_1$ is a constant $A_1$-module sheaf. Its fibre is finite free of some rank $d\geq0$, because $F_1$ is locally free. This is the sole choice of $H$; it depends only on $M_0$, and no later boundary pair enters its construction.

Cited nodes: lem-weil-pbc-finite-set-monodromy-torsor, cor-galois-lisse-representations.

Source: literature/stacks-project/pione.tex, Section Tag 03SF (section-finite-etale-under-galois); finite module structures by the fibre equivalence, with Stacks 0DV5 and 0DV6 for the finite-set torsor.

### Original step 3 → Assembly step 2 (the existing strict-local algebra and Cartesian inputs)

Fix any pair $(Y,D)$, any factorization $W\to H\to S$ of $g$, any geometric point of $Y$, and any of the parameter choices in the statement. Write $R$ for the strict henselization, $f=\prod_i t_i$, and $U=\operatorname{Spec}R[1/f]$. The original local ring is Noetherian regular; lem-sc-strict-henselization-noetherian and lem-sc-strict-henselization-regular show the same for $R$. Its characteristic is $p$. The parameters $t_i$ in the statement are part of a regular system of parameters in $R$. By lem-trf-regular-local-ufd-boundary-factorization they are nonzero prime elements in a domain; thus $U$ is a nonempty integral, hence connected, affine scheme (also when $r=0$, $f=1$). Let $N$ be the pullback of $M_0$ to $U$. Exact Cartesian coefficient pullback, sk-prop-sfb-cartesian-coefficients(1), preserves its finite free local models and identifies $N/\varpi^nN$ with $F_n|_U$. In particular $N/\varpi N\cong(A_1)_U^d$, since the map factors through $H$.

Cited nodes: lem-sc-strict-henselization-noetherian, lem-sc-strict-henselization-regular, lem-trf-regular-local-ufd-boundary-factorization, sk-prop-sfb-cartesian-coefficients.

Source: literature/stacks-project/more-algebra.tex, Tags 06LJ (lemma-henselization-noetherian), 06LN (lemma-henselization-regular); ILO IX 2.1 strict-local setup, p.133.

### Original step 4 → lem-sfb-residually-trivial-lattice-monodromy

For each $n\geq1$ consider $K_n=\ker(\operatorname{GL}_d(A_n)\to\operatorname{GL}_d(A_1))$. The finite local rings and surjective transition maps are those of lem-weil-valued-dvr-finite-quotients, and the residue field $\kappa=A_1$ is finite by lem-weil-l-adic-extension-integers-dvr. It has characteristic $\ell$: $|\ell|_E<1$ puts $\ell$ in the maximal ideal, so the field characteristic divides the prime $\ell$. Filter $K_n$ by $K_{n,i}=1+\varpi^i\operatorname{Mat}_d(A_n)$ for $1\leq i\leq n$, with $K_{n,n}=1$. The map $1+\varpi^i B\mapsto B\bmod\varpi$ identifies $K_{n,i}/K_{n,i+1}$ with the additive group $\operatorname{Mat}_d(\kappa)$: multiplication is addition modulo $\varpi^{i+1}$, and cancellation of $\varpi^i$ is valid in the DVR before taking the quotient. These groups have order $|\kappa|^{d^2}$, a power of $\ell$. Multiplying the successive orders shows $K_n$ is an $\ell$-group. This includes $n=1$ and $d=0$, when it is trivial.

Cited nodes: lem-weil-valued-dvr-finite-quotients, lem-weil-l-adic-extension-integers-dvr.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Agent matrix-filtration calculation for the finite reductions of Proposition 6.8.4(1); uses the DVR and finite residue-field facts explicitly cited.

### Original step 5 → lem-sfb-residually-trivial-lattice-monodromy

Choose a geometric point of $U$. For each $n$, $N/\varpi^nN$ is a pro-etale local system of finite $A_n$-modules on $U$, so det-pe-finite-local-systems-twist on $U$ writes it as $\nu_U^*$ of an etale local system of finite $A_n$-modules, with $\nu_U^*,\nu_{U,*}$ quasi-inverse; constancy may therefore be tested on this etale model and transported back, also after pullback to the covers below. cor-galois-lisse-representations(1) associates to this etale model its finite free $A_n$-fibre $B_n$ and its continuous monodromy action. The rank of $B_n$ is $d$, since reduction to $A_1$ is the free rank-$d$ fibre in step 3; scalar compatibility in that correspondence identifies its residual action with the trivial action. After a choice of basis, the image $Q_n$ is therefore a subgroup of $K_n$, so its order is a power of $\ell$ and is prime to $p$. Apply thm-galois-fundamental to the finite continuous $\pi_1(U)$-set $Q_n$ with left translation via the image quotient. Right translations $g\cdot q=qg^{-1}$ commute with this action and make the corresponding finite etale cover $P_n\to U$ a $Q_n$-torsor. Base change to it restricts monodromy to the kernel of the image map, so $N/\varpi^nN$ becomes the constant free $A_n$-module on $P_n$. Only this actual monodromy group is used; the order of an arbitrary trivializing cover would not suffice.

Cited nodes: det-pe-finite-local-systems-twist, cor-galois-lisse-representations, thm-galois-fundamental.

Source: literature/stacks-project/pione.tex, Tag 03SF (section-finite-etale-under-galois), image quotient and its regular finite action; theorem-fundamental-group and its base-change clause.

### Original step 6 → Assembly step 3 (the existing strict-local splitting input)

Apply lem-sfb-strict-local-prime-to-p-kummer-splitting to $R$, the chosen $t_i$, and the torsor $P_n$ with group $Q_n$. Its hypotheses hold by steps 3 and 5. Obtain a positive integer $m_n$ prime to $p$ such that $P_n$ is trivial over the punctured $m_n$-root scheme. The full prime-to-$p$ parameter-root tower $T$ in the item has a projection to this scheme. A section of the trivialized torsor therefore pulls back to a section over $T$; pullback of the trivialization on $P_n$ along this section gives $(N/\varpi^nN)|_T\cong(A_n)_T^d$. Exact Cartesian coefficient pullback identifies this sheaf with $N_T/\varpi^nN_T$, where $N_T=N|_T$. No common finite root order for all $n$ is required.

Cited nodes: lem-sfb-strict-local-prime-to-p-kummer-splitting, sk-prop-sfb-cartesian-coefficients.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose IX Proposition 2.1 and its finite simultaneous parameter-root normal form, printed pp.133-134; application at each finite monodromy quotient.

### Original step 7 → lem-sfb-lisse-lattice-constant-reductions

Choose these finite-level trivializations compatibly, as follows. Fix one at level $1$. Suppose one is fixed at level $n$ and choose any at level $n+1$. Its reduction differs from the fixed one by an automorphism of $(A_n)_T^d$, hence by an invertible matrix of sections. By lem-sfb-totally-disconnected-coefficient-realization for finite discrete sets, it is a continuous locally constant function $|T|\to\operatorname{GL}_d(A_n)$. Every invertible matrix over $A_n$ lifts to one over $A_{n+1}$: lift its entries, and the determinant remains a unit because its reduction modulo the maximal ideal is nonzero. Choose a lift for each element of the finite set $\operatorname{GL}_d(A_n)$; this set map is continuous between discrete sets. Composing with the matrix function gives a lifted automorphism on $T$. Adjusting the level-$n+1$ trivialization by this lift makes its reduction the chosen level-$n$ one. Induction gives an isomorphism of the whole reduction tower with $((A_n)_T^d)_n$. This argument does not assume that taking a constant sheaf commutes with inverse limits, or that $T$ is connected.

Cited nodes: lem-sfb-totally-disconnected-coefficient-realization, lem-weil-valued-dvr-finite-quotients.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Agent compatible-basis construction for Proposition 6.8.4(1); finite constant coefficient sections as in Lemma 4.2.12.

### Original step 8 → lem-sfb-lisse-lattice-constant-reductions and assembly step 4 for pullback/scalar identification

The pullback $N_T$ is lisse and its reductions are the actual tower in step 7, by exact Cartesian pullback. Apply lem-sfb-integral-lisse-reduction-equivalence on the scheme $T$ itself. Full faithfulness of reduction takes the compatible tower isomorphism of step 7 to $N_T\cong(A_T)^d$, since the latter has reduction tower $((A_n)_T^d)_n$. Rationalizing this isomorphism, using the inverse-image tensor comparison $t$ of def-sfb-condensed-pullback-tensor-comparison for $g^*M=g^*(A_{E,S}\otimes_{A_{\mathcal O_E,S}}M_0)$ and the Cartesian coefficient isomorphisms of sk-prop-sfb-cartesian-coefficients(1) for $A_E$ and $A_{\mathcal O_E}$, gives
$$ (g^*M)|_T\cong E_T\otimes_{A_T}N_T\cong(E_T)^d. $$
Returning through the coefficient realization and the internal-module equivalence of step 1 yields exactly the constant $A_E$-module associated to $E^d$ in the statement. The argument applied to an arbitrary point and parameter tuple, so proves the assertion for every such choice. If $r=0$, the geometric splitting lemma uses $m_n=1$ and the same proof runs on $\operatorname{Spec}R$; if $d=0$, all bases and matrices are empty and the result is the zero module.

Cited nodes: lem-sfb-integral-lisse-reduction-equivalence, sk-prop-sfb-cartesian-coefficients, lem-weil-pbc-continuous-coefficient-realizations, def-weil-pbc-internal-abelian-sheaf-module-equivalence, def-sfb-condensed-pullback-tensor-comparison.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.2 and Proposition 6.8.4(1); equivalence used on the tower scheme, followed by scalar extension.

## Unfinished work

No part of the assigned stage-1 repair is omitted. The two new nodes intentionally have statements only; their proofs are work for subsequent workers. The item's existing stage-2 Lean statement and sorry were read but not edited. The required remote dry run and direct delivery are the remaining validation/publication actions after writing this report.
