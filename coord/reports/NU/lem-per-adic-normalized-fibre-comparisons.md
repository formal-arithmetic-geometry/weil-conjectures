# Worker report

1. Files written: the item, split with unchanged statement and statement dependencies; four new statement-only nodes:
- lem-per-adic-normalized-fibre-pullback: statement, unsplit; Mathlib no match.
- lem-per-adic-normalized-fibre-scalar: statement, unsplit; Mathlib no match.
- lem-per-adic-normalized-fibre-common-stage: statement, unsplit; Mathlib no match.
- lem-per-adic-normalized-fibre-rank-loci: statement, unsplit; Mathlib no match.

2. Attachments: none. The project search by exact blueprint tag and by normalized adic fibre, common-stage fibre and rank terminology found no finished WeilConjectures declaration stating the item. The recorded Sheaf.Paper.PerAdicNormalizedFibreComparisons theorem at lines 464–469 ends in sorry.

3. WANTED: none.

4. The released repair order of 2026-10-22 overrides the prior passing split and explicitly requires at least three new nodes, all old arguments retained, and an assembly of at most 3000 characters. This is that authorized re-split, not an ordinary attempt to replace one clause by a renamed clause. Statement and stmt_deps are unchanged.

5. Nothing unfinished within stage 1; new nodes intentionally await their own workers. No Lean was written or compiled.

## Review by NU

I read Bhatt–Scholze 6.8.3–6.8.7, 6.8.14 and Remark 6.8.15 in the local PDF text, Stacks 03Q1 (etale-cohomology.tex lemma-stalk-pullback and its proof), the chapter and unit records, and both current and master blueprint smooth-pullback text. The current blueprint supplies its proof in a separate .proof.md file. The route is its first paragraph's ordinary pullback and constructible-support input; none of the perverse or purity route is changed. I opened all twenty statements cited by the old proof and the three fibre data definitions. The new nodes require those notions in their statements without claiming those definitions prove existence.

Assembly step 1 uses the pullback node's actual-pullback normalization, quotient tower, fractional naturality, chart independence and identity/composition assertions. Step 2 uses that same alpha and the scalar node's ramified completion formula, beta and mixed/coefficient coherence; neither source is used for an assertion only in its proof. Step 3 uses the first two nodes as the coherent comparison hypotheses of the common-stage node, whose statement explicitly gives the arrow formula, exactness, all detection tests and descended actual pullback. Step 4 uses the scalar comparison and common-stage fibre already established, together with the rank node's explicit fibre-dimension equality, finite clopen rank loci, point-independence and constructible positive-rank refinement. citations.json contains literal relevant paragraphs from each cited statement for every citation.

For the pullback node I verified that J's statement compares the actual completed pullback, that the stratified pullback statement supplies the degree-zero finite-free local model, and that the lisse-system statement supplies its pullback compatibility and full faithfulness. The inverse-image germ lemma gives naturality only as abelian groups; coefficient linearity and composition are precisely the finite germ calculations retained below, not assumptions silently taken from that node. The pulled etale chart need not be an affine scheme: an affine neighbourhood of its chosen lift suffices, as retained in the new statement.

For the scalar node the lisse-system scalar definition supplies n(m)=ceil(m/e), so t^{n(m)} belongs to v^mD, including ramification. Finite-module completeness applies to the finite free D-module M tensor_A D, not an arbitrary inverse limit. The realization and scalar-functor statements pin the lattice to the actual T, retaining the balancing bridge added by the former reviewer. The mixed square holds for non-flat quotient maps because it is checked on tensor generators, with no flatness assumption.

For the common-stage node the heart cone lemma really states kernel H^{-1} and cokernel H^0 with their maps; common-stage truncations identify those cohomology objects. The pair-category equality criterion kills a zero object's identity at a finite stage. It therefore suffices to enlarge once for the finitely many homology obstructions of a short sequence. Faithfulness of scalar extension is the basis injection, and detection uses the finite-stage normalized-fibre statement, which explicitly includes zero maps and short exactness.

For the rank node the rank theorem is formulated for pulled condensed coefficients, so the continuous coefficient ring comparison is essential and retained. Each stratum is noetherian and quasi-compact, giving finite rank range; finite-free normalized reduction fibres give E^r. The same-point vector-space isomorphism is only an existence assertion, with no selected path. Stacks 005L applies because X is noetherian; the analogous claim on an arbitrary non-noetherian space was not used.

Small cases checked: empty X and empty inverse-image strata, rank zero, disconnected strata with varying ranks, identity scheme maps and coefficient extensions, a closed non-flat map, ramified extensions (including m<e), and two geometric points with the same underlying point. Zero fibres have rank zero; no false canonical same-point isomorphism is asserted. New nodes have no proof steps or proof dependencies, and no proof sketch was put in their statements: all preceding arguments are retained below in the report. The short assembly has no step over 2000 characters. No statement dispute was found.

## Search review

Each new node has its own semantic query, Loogle query, source grep, and second semantic phrasing with LeanSearch, all actually run with msearch.py and recorded in searches.jsonl. The grep found no lisse adic stalk/rank/scalar declarations in AlgebraicGeometry. The pullback hits concern ordinary topological stalks or open-immersion module stalks, not normalized completed fibres. The scalar hits concern finite-module adic completion and ordinary extension associators. The common-stage hits concern exact functors, pre-Galois fibres, or ordinary module adjunctions, without this pair-category descent. The rank hits concern prime-spectrum rankAtStalk of a finitely presented flat module, not continuous pro-etale coefficient sheaves. I read the relevant candidate source files (FreeLocus, AsTensorProduct, ChangeOfRings, ExactFunctor, Stalks and Modules/Sheaf). None is an exact match or one-line specialization. Loogle reported zero hits; its common-stage and rank queries report unknown identifiers as preserved in the results. Successful semantic and grep searches supply the independent absence check.

## Not duplicates

The whole DAG was searched for normalized pullback/scalar fibres, common-stage fibres and normalized ranks, and the whole imported blueprint was searched with blueprint_refs for fibre, rank, normalized fibre, common-stage and lisse rank. No exact independent node states these complete arguments. The parent and this item are intentionally larger statements, and the released order explicitly requires allocating these arguments. The normalized-fibre-exactness node constructs the fibres and their exactness, not the natural actual-pullback/scalar comparisons. The lisse-completed-system node concerns reconstruction of lisse coefficient modules, not the normalized constructible-heart fibre comparisons. The two comparison/coherence data nodes only define assertion packages. The existing lisse-rank node uses condensed coefficients and does not identify its rank with the normalized lattice-limit fibre or give common-stage rank descent.

lem-per-adic-normalized-fibre-pullback vs def-wf-lisse-adic-automorphism-pullback: the existing node states Pullback of lisse adic sheaves by a scheme automorphism; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-sbc-strict-henselization-module-fibre-factorization: the existing node states Module stalk comparison and geometric-fibre restriction factorization; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-sbc-geometric-point-module-constant: the existing node states A module sheaf pulled back from an algebraically closed point is constant; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-sf-etale-derived-pullback-stalk: the existing node states Derived etale module pullback has the stalk at the image point; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-strict-local-section-pullback: the existing node states Strict-local representative section pullback; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-finite-etale-unit-stalk-inclusion: the existing node states Finite etale reverse-adjunction unit includes a geometric stalk summand; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-etale-fpqc-units-jointly-injective: the existing node states Joint injectivity of fpqc units at every etale object; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-constructible-module-finite-stalks: the existing node states The geometric stalks of a constructible sheaf of modules are finite; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-etale-constant-trivialization-pullback: the existing node states Coherent inverse-image extension of a constant trivialization; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-derived-global-germ-exchange: the existing node states Derived global germ compatibility with exchange; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-etale-cover-detects-iso: the existing node states A morphism of etale sheaves is an isomorphism iff it is one on an etale covering; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-qcqs-strict-local-module-comparison: the existing node states Canonical qcqs strict-local comparison for module coefficients; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-affine-etale-cartesian-sheaf-adjunction: the existing node states Left exact sheaf adjunction for cartesian affine étale functors; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-scheme-torsor-pullback-compatible: the existing node states scheme torsor pullback compatible; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs prop-weil-pbc-inverse-image-exact: the existing node states Exactness of inverse image; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-counit-stalk-germ-restriction: the existing node states The stalk of the counit $f^{-1}f_*F\to F$ is the restriction of germs; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-etale-unit-zero-neighbourhood: the existing node states Zero neighbourhood of a section killed on the whole base change; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-constant-pullback-unit-continuous-map: the existing node states Constant pullback unit on continuous maps; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-etale-sections-equality-subterminal: the existing node states Subterminal agreement sheaf and its geometric stalks; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-strict-local-fibre-unit-stalks: the existing node states Pointwise strict-local derived-unit fibre comparison; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-etale-abelian-unit-equal-open: the existing node states Agreement open for abelian etale inverse-image unit sections; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-strict-local-exchange-compatibility: the existing node states Exchange compatibility for a strict-local representative map; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-zero-dimensional-pullback-global-sections: the existing node states Pullback on global sections in dimension zero; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-sets-etale-inverse-image-stalk-germ: the existing node states Stalk of the etale inverse image of a sheaf of sets, with germs; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-scheme-torsor-pullback-equivariant-hom: the existing node states SchemeTorsorPullbackEquivariantHom; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs new-constructible-module-support-general: the existing node states Constructible support for arbitrary coefficient modules; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-geometric-point-sections-stalk-natural: the existing node states Natural comparison of geometric-point inverse-image global sections with the stalk; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-inverse-image-stalk-germ: the existing node states Stalk of an inverse image, compatible with germs of pulled-back sections; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-strict-local-global-germ-iso: the existing node states Strict-local global germs are invertible; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-etale-inverse-image-small-universe: the existing node states Ordinary étale inverse image preserves the scheme coefficient universe; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-inverse-image-torsion: the existing node states Inverse image of a torsion etale sheaf is torsion; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-exchange-pointed-representative: the existing node states Exchange on a pointed representative; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-exchange-forget-coefficients: the existing node states The derived exchange morphism commutes with forgetting the coefficient ring; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-sets-etale-inverse-image-exact: the existing node states Inverse image of set-valued sheaves on small etale sites is exact; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs def-weil-pbc-derived-global-germ: the existing node states Canonical derived global germs; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-qcqs-geometric-exchange-factorization: the existing node states Qcqs geometric exchange factors through strict-local sections; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-global-sections-stalk-comparison: the existing node states Global-sections pullback and one geometric stalk; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-etale-section-zero-neighbourhood: the existing node states A zero neighbourhood for an etale section killed by inverse image; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-scheme-torsor-pullback-equivariant-hom-is-iso: the existing node states SchemeTorsorPullbackEquivariantHomIsIso; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-geometric-point-pullback-stalk: the existing node states Inverse image to a geometric point is the stalk; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-etale-torsor-unit-action-unique: the existing node states étale torsor unit action uniqueness; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-pur-support-quotient-pair-pullback: the existing node states Functorial support-quotient pullback maps and site comparison; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-asd-etale-representable-pullback-normalization: the existing node states Normalization of the small-etale representable pullback comparison; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-asd-supported-kummer-scalar-source: the existing node states Derived scalar extension of a closed supported constant sheaf; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-asd-etale-finite-twist-pullback: the existing node states Finite Tate lines on the small etale site and their pullback; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-pur-etale-closed-constant-tensor: the existing node states Closed constant coefficient tensors and pullback on the etale site; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-refinement-preserves-finite-lisse: the existing node states Finite local constancy passes to refinements; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-asd-supported-kummer-scalar-derived-units: the existing node states Derived universal properties of supported scalar maps; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-asd-supported-kummer-scalar-maps: the existing node states Normalized supported scalar maps; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-pur-etale-projection-stalk-normalization: the existing node states Section formula implies the normalized geometric-stalk square; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-weil-pbc-pullback-finite-locally-constant: the existing node states Pullback of a finite locally constant etale sheaf; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-sc-pullback-stalk-germ-action: the existing node states Pullback stalk comparison commutes with changes of geometric lifts; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-galois-flc-set-stalk-finite: the existing node states Geometric stalks of finite locally constant sheaves of sets are finite; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-galois-flc-set-is-finite-sheaf: the existing node states Finite locally constant set sheaves are finite sheaves; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-pullback vs lem-galois-inverse-image-representable: the existing node states Inverse image of a representable etale sheaf; the new node requires normalized inverse-limit and localized constructible-heart pullback, fractional chart independence and actual completed-pullback identification, not merely a finite-level or unnormalized stalk comparison.

lem-per-adic-normalized-fibre-rank-loci vs def-weil-constructible-subset: the existing node states Constructible subset; the new node additionally identifies normalized adic fibre dimensions with continuous lisse rank and carries those ranks through finite and common coefficient stages, rather than only the general topological constructibility criterion.

lem-per-adic-normalized-fibre-rank-loci vs lem-sfb-noetherian-global-constructibility: the existing node states Global constructibility from affine-local constructibility; the new node additionally identifies normalized adic fibre dimensions with continuous lisse rank and carries those ranks through finite and common coefficient stages, rather than only the general topological constructibility criterion.

## Allocation and retained original arguments

lem-per-adic-normalized-fibre-pullback: old steps 1, 2, 3, 6.

lem-per-adic-normalized-fibre-scalar: old steps 4, 5, 6.

lem-per-adic-normalized-fibre-common-stage: old steps 7, 8, 9, 10.

lem-per-adic-normalized-fibre-rank-loci: old steps 11, 12.

The following is the original proof verbatim, retained as work instructions for the future splitters. The new statements specify its conclusions and normalization obligations; these arguments are not discarded or shortened.

### Old step 1

Identify the finite-stage heart with constructible continuous $E_X$-modules using the t-exact equivalence $J_X$. Choose a lisse stratum through $\bar x$ and an affine etale lattice chart there. Write $N_\bullet$ for its normalized finite-free etale reduction system and $M_{\bar x}=\varprojlim_n(N_n)_{\bar x}$. The normalized fibre is $M_{\bar x}[1/\varpi_E]$, and an integral system map divided by $\varpi_E^a$ acts as $\varpi_E^{-a}\varprojlim u_n$. The reduction equivalence reconstructs the chosen lisse lattice from $N_\bullet$. All subsequent local computations use precisely these quotient and localization maps; they make no claim about arbitrary pro-etale stalks commuting with inverse limits.

Cited statements: lem-per-continuous-rational-derived-realization, lem-per-adic-normalized-fibre-exactness, lem-per-lisse-completed-system-comparison.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definitions 6.8.3, 6.8.6; Proposition 6.8.4(1),(4),(6).

### Old step 2

For a finite-level etale module sheaf $H$, let $c_{g,H}:(g^{-1}H)_{\bar y}\to H_{\bar x}$ be the inverse-image stalk isomorphism. It is linear: naturality applied to multiplication by any coefficient gives $c_{g,H}(as)=a c_{g,H}(s)$. Its germ formula sends the germ of a pulled section back to its original germ. Hence it commutes with every quotient transition; the identity and composite-pullback comparisons agree because both send each pulled germ to that same original germ. For any finite coefficient homomorphism $R\to R'$, the stalk scalar comparison sends $a\otimes s_{\bar x}$ to $(a\otimes s)_{\bar x}$. Pulling back this germ and then applying $c_g$ gives $a\otimes s_{\bar x}$ as well. Since these tensors generate stalk scalar extension, this proves the finite-level pullback/scalar square, including non-flat quotient homomorphisms.

Cited statements: lem-weil-pbc-inverse-image-stalk-germ, lem-pod-etale-stalk-tensor-scalar.

Source: literature/stacks-project/etale-cohomology.tex, Stacks Tag 03Q1, etale-cohomology.tex, lemma-stalk-pullback (3), germ formula; sheaf scalar stalk formula.

### Old step 3

Apply the previous step to every $N_n$. The maps $c_{g,N_n}$ form an isomorphism of inverse systems, so their inverse limit is an isomorphism $\varprojlim_n(g^{-1}N_n)_{\bar y}\cong M_{\bar x}$. Invert $\varpi_E$ to define $\alpha_{g,F}:\omega_{\bar y,E}(g^*F)\xrightarrow{\sim}\omega_{\bar x,E}(F)$. This computes the specified completed rational pullback: the lisse reduction comparison commutes with module pullback, $J$ identifies completed rational pullback with derived module inverse image, and stratified pullback t-exactness identifies its local finite-free degree-zero model on $Y\times_X S$. The pulled chart $U\times_X(Y\times_XS)$ is etale and affine over the stratum $Y\times_XS$ but need not be an affine scheme; replace it by an affine open neighbourhood of the lift $(\bar u,\bar y)$, which leaves the stalks at that point unchanged, so it is an affine etale lattice chart of the pulled stratum as the normalization requires. Thus the calculation is made on the actual pullback of the chosen lattice chart, even when $g$ is not flat and that inverse-image stratum is empty away from $\bar y$. For a map $u/\varpi_E^a$, the two routes are $\varpi_E^{-a}\varprojlim c_g u_n$ and $\varpi_E^{-a}\varprojlim u_n c_g$, equal by naturality. This proves naturality in the whole finite-stage heart.

Cited statements: lem-per-lisse-completed-system-comparison, lem-per-continuous-rational-derived-realization, lem-per-adic-stratified-pullback-texact, lem-per-adic-normalized-fibre-exactness.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.4; Remark 6.8.15, explicit module inverse image.

### Old step 4

Put $A=A_E$, $D=A_L$, $t=\varpi_E$, $v=\varpi_L$. Use the scalar system prescribed for lisse sheaves: at level $m$ it is $N_{n(m)}\otimes_{A/t^{n(m)}}D/v^m$, where $n(m)=\lceil m/e\rceil$ and $e$ is the ramification index. Finite scalar stalk comparison and adic reconstruction identify its stalk with $M_{\bar x}\otimes_A D/v^m$. Since $M_{\bar x}$ is finite free, $M_{\bar x}\otimes_A D$ is finite free over $D$; reconstruction over $D$ therefore makes the canonical map
$$M_{\bar x}\otimes_A D\longrightarrow\varprojlim_m(M_{\bar x}\otimes_A D/v^m)$$
an isomorphism. This is a statement about finite modules, not tensor commuting with an arbitrary inverse limit. This system is that of the actual $T_{L/E}F$: $T_{L/E}$ is completed integral coefficient change followed by localization, and on representatives $J_L(T_{L/E}QK)=L_X\otimes^L_{B_{L,X}}(K\otimes^L_{B_{E,X}}B_{L,X})\cong L_X\otimes_{E_X}J_E(QK)$ by balancing, the comparison of $J$ with finite coefficient extension; on the chart the lattice $N$ is locally free, so $N\otimes_{B_{E,X}}B_{L,X}$ is a lisse lattice of $T_{L/E}F$, and the lisse system comparison identifies its reduction modulo $v^m$ with the displayed level-$m$ term ($t^{n(m)}\in v^mD$). Its inverse followed by localization gives
$$\beta_{L/E,F}:\omega_{\bar x,L}(T_{L/E}F)\xrightarrow{\sim}M_{\bar x}[1/t]\otimes_E L.$$
Indeed both localized modules are canonically $M_{\bar x}\otimes_A L$. The scalar stalk maps and the reconstruction maps are natural, so the formula also commutes with every fractional lattice map.

Cited statements: def-pod-lisse-l-adic-sheaves, lem-pod-etale-stalk-tensor-scalar, lem-pod-adic-limit-finite-modules, lem-per-lisse-completed-system-comparison, lem-per-adic-normalized-fibre-exactness, lem-per-continuous-rational-derived-realization, prop-weil-pbc-scalar-extension.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.4(1),(4); finite integral scalar comparison, Stacks Tags 09B8, 031D, 00MA.

### Old step 5

The comparisons have the required coherence with the specified functor comparisons. On a quotient, scalar extension maps a pure tensor $(s\otimes a)\otimes b$ to $s\otimes ab$; pulling back changes only the germ of $s$, and the map of step 2 sends that pulled germ back to $s$. Consequently both routes through the mixed pullback/scalar square agree on every pure tensor. In a tower $E\subset L\subset P$ both scalar routes send $(s\otimes a)\otimes b$ to $s\otimes ab$; identity extension sends $s\otimes1$ to $s$. These are the balancing associators used by $T$, not arbitrary chosen isomorphisms. Quotient projections commute with all of these formulas. Equality after every finite quotient implies equality of maps into the inverse limit, and localization preserves the equations. The composite-pullback equation similarly follows from the germ equation in step 2. This proves the quotient, identity, scheme-composition, coefficient-composition and mixed-square equations for $\alpha$ and $\beta$.

Cited statements: prop-weil-pbc-scalar-extension, lem-per-lisse-completed-system-comparison, lem-pod-etale-stalk-tensor-scalar, lem-weil-pbc-inverse-image-stalk-germ.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.4, quotient-normalized comparisons; Remark 6.8.15, balancing maps.

### Old step 6

The formulas descend from the chosen charts. On a common etale refinement, a change of lisse lattice is an isomorphism of rational lisse realizations; full faithfulness of raw lattice rationalization represents it by a fractional integral map. Naturality just proved says that conjugating $\alpha$ or $\beta$ by that map gives the comparison computed from the other lattice. The same argument applies to changes of chart and adapted stratification using the normalized fibre identifications. Explicitly, after clearing the finitely many denominators of a comparison, the equality is the equality of the finite-level diagrams, multiplied by the same inverse power of $\varpi_E$. If another fractional representative is chosen, equality in the localized Hom group means some power of $\varpi_E$ kills their difference; its rational fibre map is therefore zero. Thus no lattice, chart, stratification or denominator choice survives.

Cited statements: lem-per-adic-normalized-fibre-exactness, lem-per-lisse-completed-system-comparison.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.4(4),(6); affine-local fractional maps.

### Old step 7

For a heart pair $(E,F)$ set $V_{\bar x}(E,F)=\omega_{\bar x,E}(F)\otimes_E\overline{\mathbf Q}_\ell$. If $[M,u]:(E,F)\to(L,G)$ is represented at a common field $M$, use $\beta_{M/E}$ and $\beta_{M/L}$ to identify the two sides with $\omega_{\bar x,M}(T_{M/E}F)\otimes_M\overline{\mathbf Q}_\ell$ and $\omega_{\bar x,M}(T_{M/L}G)\otimes_M\overline{\mathbf Q}_\ell$, and apply $\omega_{\bar x,M}(u)\otimes_M\overline{\mathbf Q}_\ell$ between them. Step 5 says exactly that replacing $u$ by $a\,T(u)\,a^{-1}$ at a larger field leaves this map unchanged. The pair-category equivalence relation and common-stage calculus therefore give a well-defined additive functor, with identities and composition computed at one common stage. Common-stage truncations say every object of the heart is isomorphic to such a finite-stage heart pair. Transport along these isomorphisms extends the construction to that heart; the functorial equations make this independent up to its natural comparison isomorphism.

Cited statements: def-weil-pbc-finite-stage-pair-category, prop-weil-pbc-common-stage-calculus, lem-per-adic-common-stage-truncations.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.14, finite coefficient descent; pair-category and truncation formulas.

### Old step 8

Finite-stage inclusions into the pair category preserve kernels and cokernels of heart maps: complete a map at that stage to a cone triangle, compute its kernel and cokernel as $H^{-1}$ and $H^0$ of the cone, and use the common-stage cone definition and truncation comparisons. Thus kernels, images, cokernels and homology of any finite heart complex are represented by the corresponding finite-stage objects after a common enlargement. A zero object represented at a finite stage becomes zero at a further stage: apply the equality criterion of common-stage calculus to its identity being zero. Hence any short exact sequence in the common heart is short exact at some finite enlargement (kill its endpoint and middle homology obstructions there). At that stage $\omega_{\bar x,M}$ is exact, and extension $-\otimes_M\overline{\mathbf Q}_\ell$ is exact. Applying these to that short exact sequence proves exactness of $V_{\bar x}$. This also verifies exactness for heart objects originally given only up to isomorphism.

Cited statements: lem-weil-heart-short-exact-triangles, def-weil-pbc-common-stage-cones, lem-per-adic-common-stage-truncations, prop-weil-pbc-common-stage-calculus, lem-per-adic-normalized-fibre-exactness, lem-weil-field-scalar-extension-exact.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.14 and common-stage cones/truncations; heart cone kernel and cokernel formulas.

### Old step 9

Extension of vector-space scalars to a field is faithful and reflects zero: choose a basis, so $W\otimes_M\overline{\mathbf Q}_\ell\cong\overline{\mathbf Q}_\ell^{(B)}$, and $w\mapsto w\otimes1$ is injective. Naturality of this injection also detects zero linear maps; exactness identifies the scalar-extended homology with the homology after scalar extension. Represent an object, a morphism, or a short complex over a common heart stage. If all its common-stage fibres vanish, are zero maps, or are short exact, respectively, these elementary scalar tests imply the same finite-stage fibre assertions. Finite-stage normalized fibres detect zero objects, zero maps and short exactness. Passing the resulting assertions through the common-stage inclusion gives the claimed detection. Applied to the kernel and cokernel of a map, zero-object detection and exactness show joint conservativity as well.

Cited statements: lem-per-adic-normalized-fibre-exactness, prop-weil-pbc-common-stage-calculus, lem-weil-field-scalar-extension-exact.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Finite-stage normalized fibre detection; finite-diagram descent and elementary basis argument.

### Old step 10

For a common-stage heart object represented by $(E,F)$, tensor $\alpha_{g,F}$ with $\overline{\mathbf Q}_\ell$. The mixed-square equation of step 5 makes this independent of enlarging $E$ and compatible with the action on $[M,u]$ in step 7. Consequently it defines the displayed pullback comparison on common-stage fibres, natural in all common-stage maps. Identity and composite-pullback equations descend as well, since each finite diagram is represented over one field and the equations already hold there. The descended pullback is the actual common-stage pullback supplied by stratified pullback t-exactness.

Cited statements: lem-per-adic-stratified-pullback-texact, prop-weil-pbc-common-stage-calculus.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Remark 6.8.15; common-stage morphism formulas.

### Old step 11

By the heart realization, choose a finite locally closed stratification with lisse continuous realization on each stratum $S$. To apply the existing lisse-rank theorem, identify its pulled condensed coefficient ring with the continuous coefficient ring, and hence with $E_S=B_{E,S}[1/\varpi_E]$. Transport of a module along this ring isomorphism preserves its finite-free trivializations. The rank theorem supplies clopen rank loci in $S$ and a finite range because $S$ is noetherian, hence quasi-compact. Its rank equals the normalized fibre dimension: on an etale lattice chart the normalized reduction equivalence gives finite locally free $N_n$ of the same local rank $r$, the reconstructed lattice has that rank, and its inverse-limit fibre is free of rank $r$. After inversion it is $E^r$. This uses only the finite-level stalk of a constant module, which is that module. Thus every geometric point over $x\in S$ has dimension $r(x)$, independent of chart and geometric point. Two such fibres are isomorphic as $E$-vector spaces by choosing bases of their equal dimension; this asserts no canonical choice of path or isomorphism.

Cited statements: lem-per-continuous-rational-derived-realization, lem-weil-pbc-continuous-coefficient-realizations, det-lem-stratified-lattice-rank, lem-per-lisse-completed-system-comparison, lem-per-adic-normalized-fibre-exactness, lem-pod-lisse-tensor-and-scalar-extension.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definitions 6.8.3, 6.8.6; Proposition 6.8.4(1),(6); lisse-rank theorem.

### Old step 12

For each of the finitely many $S$, intersect it with its finitely many nonempty clopen rank loci. These subsets are locally closed in $X$, pairwise disjoint and cover $X$, so they are a finite stratification. A fibre is nonzero exactly when its rank is positive, since it is finite-dimensional. Thus the nonzero-fibre locus is the union of the positive-rank strata; a finite union of locally closed subsets in this noetherian space is constructible. For a finite field extension, an $E$-basis of a fibre becomes an $L$-basis of its scalar extension, so step 4 proves rank and nonzero-locus invariance. For any common-stage heart object, choose a finite-stage representative as in step 7; the same basis argument gives equal rank after extension to $\overline{\mathbf Q}_\ell$. The resulting strata and nonzero locus therefore have all the asserted properties, independent of the representative, since the functor sends isomorphisms to fibre isomorphisms.

Cited statements: def-constructible-stratification, def-weil-constructible-subset, lem-per-adic-common-stage-truncations.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definition 6.8.6; Stacks Tags 09XZ and 005L; finite-field representative and basis argument.


## Verification

The first dry run exited successfully at e463ec3d7d8. During the source check I corrected the new rank node's Stacks 005L label to topology.tex lemma-constructible-Noetherian-space. This changes source precision only. The final dry run checks that correction and the expanded verbatim citation excerpts. The item statement and statement-dependency list remain exactly those of the repository; the four new nodes are statement-only and all twelve original steps remain verbatim above.
