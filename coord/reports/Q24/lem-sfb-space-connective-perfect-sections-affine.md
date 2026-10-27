# Stage-1 report: lem-sfb-space-connective-perfect-sections-affine

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-connective-perfect-sections-affine.json: split statement, six proof steps, preserving all mathematical hypotheses and conclusions.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-connective-nonnegative-free-model.json: statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-connective-hypercohomology.json: statement-only lemma, unsplit; no Mathlib match.
- citations.json: one verbatim statement quote for every step/dependency pair.

Two new statement nodes, zero new Mathlib leaves. New nodes have empty proofs and proof dependencies. All source and helper writes are inside this item's sandbox. No Lean was written or compiled, and no repository git command was run.

## Attachments

None. Searched the project library by the exact blueprint tag and by connective/perfect/sections/cohomology-representability terminology. The existing affine flat connective truncation theorem supplies a related scheme-level truncation input, not this algebraic-space representation. A sorry-free proof of a strict subclaim would not attach the whole item.

## WANTED

None. All sources used are available locally.

## Corrections and route

No mathematical statement dispute. I normalized the imported doubled TeX backslashes in the item's statement; its objects, all scheme tests, arbitrary base, perfection, universal negative vanishing, natural representation and affine finite-presentation conclusions are unchanged. The word affine in the conclusion does not assert that the representing object is a vector bundle or an affine n-space: the local model can have linear equations, with changing rank.

The inherited node had no proof. I read GOAL.md, the chapter and unit records, the three SETUP levels, and the newest blueprint's sk-thm-sf-ctf-stability and direct-images proof (3). This item is a deeply nested algebraic-moduli prerequisite of the recorded alteration route. Its existing blueprint ancestor is null (confirmed by blueprint_refs.py ancestor); I preserved that and the full via chain and gave both children the item prepended to that chain. No chapter/unit text, target, or route above this node is changed.

The proof follows Stacks 08JX's local construction. For descent, I use coordinate algebras and the already existing 081V relative-Spec correspondence instead of adding a second generic local-representability theorem. This is the same etale-local gluing argument and does not change the unit route. Off-unit generic tools are declared in split_report.tool_uses, in particular K-flatness, affine-target morphisms, etale restriction, and scheme separated-implies-quasi-separated.

## Searches and reuse

Before creating nodes I searched all DAG statements and sources, including 08JX, 068U, 0653, nonnegative perfect complexes, connective hypercohomology, local representation, affine locality, and quasi-coherent descent. I ran blueprint_refs.py searches for cohomology perfect, connective, affine locality, 068U, hypercohomology, 08JX, 071J and nonnegative. No blueprint statement supplies either proposed new statement. The imported truncation and spectral-sequence nodes are not representations or the required small-etale-site connective comparison.

Every new node has the actual output from msearch.py recorded in mathlib_searches, including leanfinder, loogle, grep, leansearch, and a second semantic phrasing. searches.jsonl is retained. I read all returned signatures. In particular, DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE (TStructure.lean:180) constructs a bounded representative without finite free terms, and isKProjective_of_projective assumes projective terms without producing the nonnegative finite model. CategoryTheory.Functor.rightDerivedZeroIsoSelf (RightDerived.lean:376, source read at 354–376) concerns a sheaf in degree zero; it does not give the connective-complex statement or its localized-site and pullback normalization. The cohomologyPresheaf/Sheaf.H hits concern higher cohomology of a sheaf. No one-line specialization gives either new node. All successful searches are recorded as no match, and none was unavailable. The existing search history on the item was kept and new Q24 searches appended.

## Not duplicates

lem-sfb-space-connective-nonnegative-free-model vs lem-sfb-space-connective-perfect-sections-affine: the new statement only supplies etale local nonnegative finite free representatives in the derived category; it says nothing about representing sections, affine morphisms or finite presentation. The item's proof constructs the coordinate ring and descends it explicitly, rather than applying a new copy of its conclusion.

lem-sfb-space-connective-nonnegative-free-model vs lem-pc-affine-flat-connective-truncation: the old lemma starts with a supplied bounded complex of flat quasi-coherent finitely presented Zariski modules on an affine scheme and gives homology of its truncation; the new statement supplies a finite free model in the small-etale derived category from an abstract perfect object on an arbitrary algebraic space. Neither the input model nor the topology comparison is supplied by the old statement.

lem-sfb-ringed-site-connective-hypercohomology vs lem-trf-connective-hypercohomology-sheaf: the old statement is for the site of opens of a ringed topological space; the new statement is for any small ringed site and includes normalization for derived tensor pullback between ringed topoi. The small etale site is not the site of opens, and I did not apply the old statement to it.

lem-sfb-ringed-site-connective-hypercohomology vs lem-sfb-space-connective-perfect-sections-affine: the new lemma is a general computation of connective derived evaluation, with no perfection or representability claim; the item additionally builds and descends the finite polynomial-algebra representation.

lem-sfb-ringed-site-connective-hypercohomology vs lem-sc-bounded-below-injective-resolution: the existing node supplies a K-injective replacement, not the zeroth hypercohomology comparison and its normalization under restriction and derived pullback.

lem-sfb-ringed-site-connective-hypercohomology vs def-pur-kinjective-complex: the existing definition defines K-injectivity and homotopy, not a connective derived-section theorem.

lem-sfb-ringed-site-connective-hypercohomology vs lem-pur-ringed-site-grothendieck-abelian: Grothendieck abelianness and generators of module sheaves do not state the zeroth derived-section calculation.

lem-sfb-ringed-site-connective-hypercohomology vs prop-pur-kinjective-resolutions-exist: functorial resolution existence does not state the degree-zero computation for a connective object or its pullback comparison.

lem-sfb-ringed-site-connective-hypercohomology vs lem-pur-site-derived-sections-unit-pasting: that lemma proves composition/pasting of derived pullback maps for constant-ring modules and exact inverse images; this lemma computes H0 of an arbitrary connective structure-module complex, including nonflat tensor pullback when its result is connective.

lem-sfb-ringed-site-connective-hypercohomology vs def-sp-constant-scalar-pullback-comparison: the old definition supplies a coefficient-change comparison on constant pro-etale coefficients, not a connective derived-section isomorphism for variable structure rings.

lem-sfb-ringed-site-connective-hypercohomology vs def-pur-ringed-site-zeroth-hypercohomology: the old node defines H0 RΓ on K-injectives; it does not assert H0 RΓ(E) = Γ(H0 E) under connective vanishing.

lem-sfb-ringed-site-connective-hypercohomology vs def-pur-derived-internal-hom: derived internal Hom is defined there; no connective-sections computation is stated.

lem-sfb-ringed-site-connective-hypercohomology vs def-sp-et-proet-coefficient-transport: that node defines transport of scalar/support comparisons across realizations, not the ringed-site connective-sections calculation.

lem-sfb-ringed-site-connective-hypercohomology vs lem-weil-pbc-module-direct-image-left-exact: the old node proves ordinary constant-coefficient direct image is additive and left exact; the new node is a derived theorem about connective complexes with arbitrary structure-ring sheaves.

## Review by Q24

I read quot.tex Tag 08JX (lemma-cohomology-perfect-complex), statement and whole proof, including the distinction between the sheaf H0 and hypercohomology H0. Our item is exactly the perfect-input case of (2), with the same universal quantification on scheme maps and no Noetherian hypothesis. In the local algebra paragraph I checked the two ranks and wrote the matrix with row j and column i consistently; the source's printed index conventions are inconsistent in its last display, so the formulas here explicitly use j=1,...,m and i=1,...,n.

For the new local-model node, I read the last two paragraphs of 08JX, more-algebra.tex Tag 0653 (lemma-last-one-flat), and algebra.tex Tag 00NX (lemma-finite-projective). The intended later proof first takes an etale local strict model, passes on an affine chart to its finite-projective module complex, and uses universal negative vanishing to form its flat degree-zero cokernel. Cokernels of finite presentations are finitely presented, so 00NX makes that cokernel finite locally free. Refining an affine cover trivializes it and all finitely many remaining terms. This gives an isomorphism of derived objects, as the new node states, rather than a per-degree comparison. The affine etale/Zariski derived comparison and preservation of perfection in spaces-perfect.tex (071Q and 08HG) and sites-cohomology.tex (08H6) were also read; no abstract derived equivalence was silently used in an assembly step.

For the new site-sections node, I read sites-cohomology.tex 071J and its resolution-functor construction, the unbounded construction in 07A5, and derived.tex Tag 070J (bounded below injective complexes are K-injective). A connective object has an injective representative in degrees >=0. Its derived evaluation has no negative terms and its H0 is the kernel of the first evaluated differential; left exactness identifies that kernel with sections of H0. Comparing these identifications on localized sites and via the adjunction unit gives the stated restrictions and pullback compatibility. This is needed on small etale sites, not just Zariski opens. No arbitrary inverse image is asserted to be exact: the general pullback clause explicitly assumes the pulled-back object remains connective, and Lf* uses K-flat resolutions.

Step 1 uses the new ringed-site comparison and the final etale-restriction clause of lem-trf-space-etale-module-pushforward-restriction. I opened that statement: it really identifies etale tensor pullback with localized restriction, rather than merely commuting a pushforward square. Exact restriction commutes with kernels and images. The comparison's naturality makes the transition maps the ordinary restrictions, so the module-sheaf matching condition proves the etale sheaf assertion for F on every scheme test.

Step 2 uses the new model, lem-pc-bounded-above-flat-kflat-site (a theorem on any ringed site, not only a ringed space), and the new site comparison. All finite free terms are flat, the degree interval is bounded above, and ordinary pullback of this K-flat model computes Lh*. The universal vanishing assumption is precisely the one required in the model lemma, and remains true after restricting to any chart. No global bound over non-quasi-compact B is used.

Step 3 uses lem-weil-pbc-morphism-into-affine-scheme, whose statement allows an arbitrary source scheme X. It therefore supplies the affine-target morphism bijection even for nonaffine T. Polynomial evaluation and factoring through the finitely generated relation ideal are written out. The finite-presentation and locally-finite-presentation definitions cited really use a finite polynomial presentation. The result is a natural isomorphism on all tests, not just affine test points. No flatness or constant rank of the matrix is needed.

Step 4 uses the fully faithful Yoneda node, not just a definition of h_X, to get unique overlap isomorphisms and their cocycle. I opened the relative-Spec correspondence and read its 081V source: it includes the algebra anti-equivalence and arbitrary base change. Thus the underlying algebras on overlaps are quasi-coherent with the correct tensor-pullback comparisons. I opened the full statement of lem-sfb-space-fppf-qcoh-descent and read spaces-descent.tex 04W8: the node supplies effectiveness and full faithfulness for small covers without Noetherian assumptions. Etale covers are special cases. Ring operations are glued on matching sections, so this does not assume an unrecorded theorem on descent of algebras or that every module equivalence is monoidal. Triple-overlap identities are checked by uniqueness, not asserted without explanation.

Step 5 uses the existence and base-change clauses of the relative-Spec correspondence to produce an algebraic space affine over B. Its comparison with F is glued on each arbitrary T using the etale sheaf condition proved in step 1 and that in the algebraic-space definition. I spelled out the two inverse maps and why naturality after arbitrary test change follows from the explicit local polynomial bijections. This avoids an uncited general representability descent theorem and avoids imposing a finite-type size condition on the entire atlas.

Step 6 uses the chart test for local finite presentation and the affine-locality theorem for quasi-compactness, separation, and scheme representability after scheme base change. I caught that separated-implies-quasi-separated must also be cited: I added the existing scheme lemma, applying it only after that scheme base change. Thus no scheme-only statement is applied directly to a nonschematic space. Together with the item's definition this gives finite presentation, not just local finite presentation.

Small cases: zero K gives a singleton section functor and V=B. For O^n in degree zero the matrix has m=0 and yields A[x_1,...,x_n]; for a positive-degree complex with P0=0 it yields A and the zero section only. For the two-term example [A --a--> A] in degrees 0,1 it gives Spec(A[x]/(ax)), with no assumption that a has constant rank. Over a field the new model reduces to a finite-dimensional complex with negative cohomology removed, while a free summand in degree -1 violates the premise on the identity test. The ringed-site statement correctly excludes complexes with negative cohomology, where degree-zero hypercohomology may receive higher-cohomology contributions. Empty base and empty test give the unique zero section. The constructions and descent work componentwise and never require B or T to be quasi-compact.

I checked B1–B10: new nodes are self-contained statements only, all notions have inline meanings or definition dependencies, JSON TeX is singly escaped after decoding, sources give tags and labels, actual searches are retained, and blueprint provenance is complete relative to the inherited null ancestor. For C1–C8 I read every cited statement, recorded a verbatim quote, reused existing generic tools, and declared the off-unit ones; no proof-only clause of another node is used. For D1–D5 the item itself constructs the representing ring and glues it; neither new node states its representability or finite-presentation conclusion. All six non-elementary steps are below 2000 characters. The matrix-index correction, TeX normalization and additional quasi-separated citation were made during this self-review.

## Unfinished work

The two new nodes are deliberately unsplit stage-1 children and will be queued for their own proofs. No unfinished assembly step remains in this item. Required dry-run and delivery results are reported by deliver.py; no compiler or local check_dag/review_split/preflight was invoked.

The first dry run rejected the wording “the item's” in step 6 as a self-containedness check. I replaced it with the explicit three properties defining finite presentation; no mathematical content changed.
