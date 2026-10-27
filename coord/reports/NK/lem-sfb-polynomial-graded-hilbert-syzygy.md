# NK stage-1 delivery: lem-sfb-polynomial-graded-hilbert-syzygy

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-graded-hilbert-syzygy.json: item split in five steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-projective-dimension-bound.json: new statement-only node, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-connected-graded-projective-free.json: new statement-only node, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every step/node pair.
- searches.jsonl: actual Mathlib searches recorded by msearch.py.
- report.md: this report.

## Attachments

None. I searched the whole project WeilConjectures/ tree for the item tag, Hilbert syzygy, graded projectivity, and global/projective dimension. The actual graded-resolution declarations in RingTheory/GradedSyzygy.lean and the minimal-presentation and graded-Nakayama modules concern k[x_0,x_1]. They do not give the arbitrary-number-of-variables item. A geometric projective-space resolution or a merely ungraded resolution does not attach this statement either. No Lean was written or compiled.

## Wanted literature

None. The sources used are present in literature/stacks-project/algebra.tex. The newest blueprint was read under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, including the unit statement and direct-images proof (3). The inherited DAG unit record has an older six-functors statement, rather than the current basics-unit wording; this item's role remains the supporting algebraic prerequisite before the finite twist resolution, not a replacement of the unit's route.

## Problems found and changes

The seeded item is mathematically correct but has no proof. Tag 00OQ literally gives an ungraded global dimension bound, not graded freeness or a finite shifted-free resolution. Tag 0EKB literally gives graded Nakayama, not a free resolution. I separated those issues: the ungraded dimension bound is one new input, and finite ungraded projectives over an arbitrary connected nonnegative graded algebra having homogeneous bases is the other. Finite covers and their kernels are constructed in the item's steps. This does not move the item into a renamed copy: neither new statement constructs a resolution by finite graded free modules. In particular the dimension-bound node allows arbitrary modules and possibly infinite projectives and contains no grading, and the basis node has a projectivity hypothesis and no resolution bound or polynomial-ring hypothesis.

The item statement has not changed. No statement dispute arose. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor returns None on the item's created.item chain. I kept that result, retained the full inherited via list, and gave the new nodes the prescribed additional via entry and precise supporting place. The source field and proof_origin explicitly distinguish agent-extracted consequences from literal Stacks statements. No SGA source is used.

## Search and duplicate audit

Before creating the nodes I searched the whole DAG by tags 00OQ and 0EKB, key phrases, titles and statements, and projective dimension/syzygy, and checked the actual statements of the relevant candidates. I also searched blueprint_refs.py for syzygy, graded, global dimension, projective module, Hilbert and homogeneous basis. The blueprint candidate lem-sc-p1-graded-resolution is a statement about coherent sheaves on P^1, and its algebraic child lem-sc-p1-graded-syzygy concerns two variables only. The minimal-presentation and graded-Nakayama children are also restricted to two variables. None supplies the proposed general connected-graded-algebra basis theorem or the ungraded bound for m arbitrary.

Every new node has its own statement-specific leanfinder, leansearch, loogle and grep records, with two semantic phrasings. The item has another actual leanfinder/loogle/grep search added while its prior recorded searches are preserved. All searches in this attempt succeeded. I read the returned types: HasProjectiveDimensionLE/LT and projectiveDimension_le_iff define/reformulate a bound, and ModuleCat.projectiveResolution supplies an unbounded resolution; they do not prove a polynomial global dimension bound. The polynomial hits in LeanSearch concern Krull dimension and Noetherianity. GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous concerns generators of an algebra, not a module basis; its source in GradedAlgebra/FiniteType.lean was read. Module.finitePresentation_of_projective gives finite presentation, not freeness or homogeneous bases. The graded-module hits define structures; the Loogle projective polynomial hits are Weierstrass polynomials. No exact match or one-line specialization was found.

## Arguments reserved for the statement-only children

For lem-sfb-polynomial-projective-dimension-bound the source is exactly the second sentence of Stacks 00OQ, proposition-finite-gl-dim-polynomial-ring: global dimension m means every module admits a projective resolution of length at most m. This is intentionally the upper bound only; no finite rank and no grading are asserted.

For lem-sfb-connected-graded-projective-free, put A_+=sum_{a>0} A_a. A finite module P has finite-dimensional quotient P/A_+P over k; it is graded. Choose a homogeneous k-basis of this quotient with homogeneous lifts p_r of degrees e_r. The degree-zero map q from the finite sum of A(-e_r) onto P is surjective by 0EKB(4). Let L=ker q. Since P is ungraded projective, 05CF gives an ungraded section s of q. Then L is the image of the idempotent 1-sq on the finite free source, hence is finitely generated even when A is not Noetherian. The kernel is a graded submodule because q preserves degree. The split direct-sum decomposition F=L plus s(P) remains a direct-sum decomposition modulo A_+, so L/A_+L injects into F/A_+F and its image is the kernel of the induced q. That induced q sends a basis to the selected quotient basis, so its kernel is zero. Apply 0EKB(1) to the finite graded L to get L=0. Thus q is a degree-zero isomorphism. Its inverse preserves degree because a homogeneous preimage can be obtained by taking the appropriate homogeneous component and injectivity annihilates the other components. This is a genuine homogeneous-basis theorem for general connected graded algebras, not the whole syzygy result. The argument is recorded here rather than inside the unsplit node's statement or proof field.

## Review by NK

I read Stacks Algebra Tag 00OQ (proposition-finite-gl-dim-polynomial-ring) and its proof, Tag 0EKB (lemma-graded-NAK), all four parts and its proof, Tag 00O5 (lemma-independent-resolution) and its projective-kernel assertion, Tag 00IK (lemma-Noetherian-basic), and Tag 05CF (lemma-characterize-projective), with their tags confirmed against tags/tags. For the new bound node, 00OQ gives all modules, so it applies to the given M without requiring an extra finiteness hypothesis. For the new basis node, 0EKB and 05CF give the preceding quotient-basis argument; crucially projectivity is ungraded, the splitting need not preserve degrees, and L is finite because it is a summand of finite free F, not because A is assumed Noetherian.

In step 1 the only citation is def-weil-finitely-generated-module. I opened it and checked that it supplies a finite generating family. The finite homogeneous-component replacement and the formula defining the map are written out; this uses the item's given internal grading. Its shift convention puts a basis vector of S(-e) in degree e, which I checked explicitly. This is an elementary construction, not an uncited graded-cover theorem.

In step 2 I opened lem-weil-pbc-polynomial-ring-field-regular-ring: its statement explicitly says the finite-variable polynomial ring is Noetherian, and I use just that clause. I opened lem-weil-pbc-noetherian-submodule-finite: it says every submodule of a finite module over a Noetherian ring is finite; this applies to ker(q_j) inside F_j. The kernel grading follows component by component as written. I opened def-weil-pbc-projective-module and checked that it includes the direct-summand characterization, so the identity splitting proves that the underlying free F_j is projective. The induction starts with K_0=M and builds only m covers; it assumes none of the kernels is already free. Exactness comes directly from K_{j+1}=ker(q_j), surjectivity of q_j, and the kernel inclusions.

In step 3 I checked the new bound node supplies exactly the required length-m ungraded projective resolution. I opened lem-weil-pbc-projective-resolution-kernel-projective: its explicit 'In particular' clause concerns an exact partial resolution with m projective terms and gives projectivity of K_m. Its d=0 clause says M itself is projective. This is a declared generic tool use from another unit; no local unit node supplies the terminal-syzygy theorem. This avoids treating the definition of projectivity or of dimension as a dimension-shifting theorem.

In step 4 the only cited input is the new homogeneous-basis node. Its full hypotheses are checked: S is a nonnegative graded commutative k-algebra with degree-zero part k, K_m is graded and finite by the induction (K_0=M when m=0), and K_m is projective by step 3. The conclusion is a degree-preserving isomorphism, sufficient for the stated composition with the kernel inclusion. The text verifies injectivity, image=kernel, lower exactness and augmentation separately. Thus there is no hidden ungraded-to-graded comparison or appeal to Quillen-Suslin.

In step 5 I checked M=0 and a vanishing intermediate kernel using empty bases and zero maps, and m=0 by the isomorphism in step 4. Negative and positive generator degrees are handled by d=-e. As sanity examples, M=S shifted in either direction allows an identity resolution with zero higher terms; k over k[x] requires one nonzero kernel, and k over k[x_1,...,x_m] is consistent with length m. For the general basis child I checked A=k, P=0, and A=k[t]/(t^2) graded with degree t=1: projectivity is essential, since the quotient k over that ring has no A-basis. The child makes no false claim about arbitrary finite graded modules or about nonconnected degree-zero rings.

Against delivery-errors B: both children introduce every object and notion, have statement-only empty proofs and proof-dependencies, honest tagged sources, complete searches, and blueprint provenance. Against C: every non-elementary input has a cited statement; citations.json quotes those statements verbatim, no quote comes from a cited proof. Against D: the steps construct the resolution, and the new nodes supply independent algebraic inputs rather than its final clause; the induction, base case and zero-variable case are explicit. Against E: finite generation, grading, ungraded projectivity, number of terms and sign of shifts are checked where needed. No step is longer than 2000 characters, and no standard comparison is hidden inside a long step. The only elementary steps are the written-out cover construction and the zero/empty-family checks.

## Not duplicates

lem-sfb-polynomial-projective-dimension-bound vs lem-sc-p1-polynomial-dimension-one: the existing statement is Krull dimension one for k[t], not a bound on module projective dimension.

lem-sfb-polynomial-projective-dimension-bound vs lem-sc-p1-polynomial-regular: the existing statement is regularity of k[t], not projective-resolution lengths over arbitrary m-variable rings.

lem-sfb-polynomial-projective-dimension-bound vs lem-sfb-compatible-regular-local-field-presentations: the existing statement constructs compatible regular local presentations and flat maps, not a projective-resolution bound.

lem-sfb-polynomial-projective-dimension-bound vs lem-sfb-polynomial-graded-hilbert-syzygy: the existing item asserts a finite graded free resolution; the new bound is entirely ungraded and gives no finite ranks, while the new basis theorem assumes projectivity and has no resolution conclusion.

lem-sfb-polynomial-projective-dimension-bound vs lem-sfb-projective-coherent-finite-twist-resolution: the existing statement resolves coherent sheaves on projective space; neither of its algebraic inputs is stated as a theorem about modules there.

lem-sfb-polynomial-projective-dimension-bound vs lem-trf-polynomial-strict-local-coordinate-dimension: the existing statement gives regularity and Krull dimensions of localized and strictly henselian coordinate rings, not a projective-resolution bound.

lem-sfb-polynomial-projective-dimension-bound vs lem-weil-pbc-field-regular-ring: the existing statement is regularity of the field, not the all-modules projective-dimension bound over m-variable polynomial rings.

lem-sfb-polynomial-projective-dimension-bound vs lem-weil-pbc-finite-type-domain-dimension-local-ring: the existing statement compares local and global Krull dimensions and prime chains, not projective dimensions of modules.

lem-sfb-polynomial-projective-dimension-bound vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: the existing statement detects localized regular sequences from a quotient dimension, not projective resolutions.

lem-sfb-polynomial-projective-dimension-bound vs lem-weil-pbc-polynomial-ring-field-regular-ring: the existing statement gives Noetherianity and regularity at primes, which step 2 reuses; it does not state global dimension or bounded projective resolutions.

lem-sfb-polynomial-projective-dimension-bound vs lem-weil-pbc-polynomial-ring-maximal-chain-height-difference: the existing statement concerns heights and lengths of prime chains, not projective resolutions.

lem-sfb-connected-graded-projective-free vs def-weil-pbc-projective-module: the existing node defines projectivity by exactness, a free summand or lifting; none of these definitions asserts a homogeneous basis.

lem-sfb-connected-graded-projective-free vs lem-sfb-dvr-projective-complex-matrix-model: the existing statement gives ungraded free matrix models over a DVR, not homogeneous bases over connected graded algebras.

lem-sfb-connected-graded-projective-free vs lem-sfb-polynomial-graded-hilbert-syzygy: the existing item asserts a finite graded free resolution; the new bound is entirely ungraded and gives no finite ranks, while the new basis theorem assumes projectivity and has no resolution conclusion.

lem-sfb-connected-graded-projective-free vs lem-sfb-scalar-dual-evaluation-inverse: the existing statement constructs the inverse to scalar-dual evaluation on sheaves from a finite-projective splitting; it has no grading or homogeneous-basis conclusion.

lem-sfb-connected-graded-projective-free vs lem-weil-pbc-free-module-projective: the existing statement is free implies projective; the new theorem proves the converse with a homogeneous basis under connected graded hypotheses.

lem-sfb-connected-graded-projective-free vs lem-weil-pbc-projective-direct-summand: the existing statement preserves projectivity under retracts and isomorphisms; it gives no homogeneous basis.

lem-sfb-connected-graded-projective-free vs lem-weil-pbc-projective-ext-criterion: the existing statement characterizes projectivity by Ext vanishing; it gives no homogeneous basis.

lem-sfb-connected-graded-projective-free vs lem-weil-pbc-ses-projective-quotient-splits: the existing statement splits short exact sequences with projective quotient; it does not assert freeness or homogeneous bases.

Additional conceptual checks: lem-sfb-connected-graded-projective-free vs lem-sc-p1-graded-nakayama-free: the latter treats k[x_0,x_1] with Tor_1(N,k)=0; the new theorem treats arbitrary nonnegative connected commutative graded algebras with an ungraded projectivity hypothesis. Neither is a one-line specialization giving the general new statement. The two-variable graded free-cover and minimal-presentation nodes are likewise insufficient for m arbitrary; their elementary construction is written in step 1 instead of creating another cover node.

## Unfinished work

The two children remain unsplit statement-only nodes, as required by one-level stage 1. Their arguments and source distinctions are recorded above for the next worker. The item itself is completely split. Required server dry run and delivery are recorded by deliver.py; no local DAG check or compiler was run.
