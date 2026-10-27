# Q148 repair report

## Files written

- `dag/nodes/sec-six-functors/lem-sf-constructible-exceptional-coefficient-coherence.json`: existing statement, statement dependencies, normalizations, source/search history, Lean attachment metadata and prior review retained; proof replaced by a 2637-character assembly.
- `dag/nodes/sec-six-functors/lem-sf-integral-refinement-diagram-admissibility.json`: statement; Mathlib verdict no match; status unsplit; no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-sf-common-transition-coefficient-mates.json`: statement; Mathlib verdict no match; status unsplit; no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-sf-integral-normalized-refinement-pasting.json`: statement; Mathlib verdict no match; status unsplit; no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-sf-rational-left-coefficient-localization.json`: statement; Mathlib verdict no match; status unsplit; no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-sf-normalized-ring-compact-scalar-cocycle.json`: statement; Mathlib verdict no match; status unsplit; no proof or proof dependencies.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id and coefficient/coherence concepts. The project declaration `WeilConjectures.ConstructibleExceptionalCoefficients.coefficient_construction_coherence` in `lean/Sheaf/Paper/ConstructibleExceptionalCoefficientCoherence.lean:208` ends in `sorry` at line 216, so it is not an attachment. No compiler or Lake command was run and no Lean was written.

## WANTED

None. The blueprint, current Lean record/docstring, all cited DAG statements and relevant Stacks source files are present locally. The detailed normalized argument is agent-written; the blueprint only specifies the coefficient/refinement route. No prohibited SGA source is used.

## What was wrong and what changed

The released stage-1 repair record requires spreading the former 12624-character proof over at least four real obligations. The sandbox contained only dispatcher marker files, not the purported retained delivery. I therefore copied the current live node read-only as the baseline and saved its complete original 13 steps in `original-proof.json`. There was no retained split or report to dry-run first, and no prior running deliver invocation. The unchanged statement includes BOTH historical repairs: the rational functor's normalization on every localized Hom representative and the common-stage functor's normalization on arbitrary common-stage representatives. Neither is dropped or replaced by an object-only assertion. I do not reopen those already accepted statement corrections in this repair.

Five independent statement-only obligations now carry old steps 1–3, 5, 6–7, 9 and 10. The parent retains the generic counit transpose calculation (old 4), the finite refinement application (old 8), and elementary localization/pair cancellation (old 11–13). The work is distributed, rather than moved to one replacement theorem. The new nodes have comparable statement sizes, roughly 2200–2800 characters, and carry no proof sketch in their statements. Their statements specify all data and relevant normalization hypotheses without depending on the parent. No node asserts the whole CoefficientCoherence record.

The local `blueprint_refs.py ancestor` output is `None`, because this maintenance-created item's `created.item` is a Lean module, not a DAG node. The existing explicit blueprint reference unambiguously names the imported `sk-thm-sf-tensor-hom`, which I read. The first dry run rejected that explicit ancestor because the computed created.item chain is broken. I read tools/blueprint_refs.py: its documented schema explicitly allows null when that chain is broken. Each new node therefore has from.node=null, exactly as the required ancestor command computes, while its nonempty from.place explicitly records sk-thm-sf-tensor-hom and the source clause. The item's existing blueprint field is retained, and each new via list contains the item. This uses the documented broken-chain representation without changing maintainer-owned created metadata or any tool. The whole-blueprint searches for `coefficient coherence`, `scalar cocycle`, `rational normalization`, `common-stage transition`, and `integral compactification` found no matches; the broader refinement search was also read. DAG concept searches and searches for tags 0GL6, 0E8I, 0F7B and 0F7C were used to inspect existing comparison/pasting nodes, not to create duplicate Stacks lemmas.

## Unfinished work

The five extracted nodes are deliberately statement-only, for other workers to split in parallel. This delivery does not claim any new Lean proof. Stage-1 delivery checks are run on the server by the authorized wrapper.

## Not duplicates

lem-sf-normalized-ring-compact-scalar-cocycle vs lem-pur-ringed-coefficient-projection-cocycle: the existing node is the ordinary direct-image coefficient mate for one topoi morphism; the new statement also pastes open extension and proves transport to the prescribed restricted compact-support comparisons through full inclusions.
lem-sf-normalized-ring-compact-scalar-cocycle vs lem-sf-compact-coefficient-composition: the existing statement compares geometric composition f then g at two finite quotient stages on separated schemes; the new statement compares a chain of coefficient maps for one compactification, including completed rings, mixed chains and nonflat maps without absolute separatedness.
lem-sf-normalized-ring-compact-scalar-cocycle vs lem-sf-proper-open-coefficient-refinement: the existing result is compatibility of a geometric refinement with one finite coefficient change; the new result is scalar identity/composition, including integral ring sheaves.
lem-sf-rational-left-coefficient-localization vs lem-sbc-raw-operation-coherence: the existing result constructs ambient push/pull data for ordinary direct and inverse image in the smooth-base-change coefficient system; the new result transfers given constructible compact-support comparisons and their specified scalar associators/unitors using the rational arrow normalization.
lem-sf-rational-left-coefficient-localization vs lem-sbc-finite-stage-rational-exchange-coherence: the existing result extends a fixed Cartesian push/pull exchange and its ambient complete/Karoubi system; the new statement is a conditional raw-localization lemma for a given compact-support functor and its already supplied normalized comparisons. No Karoubi extension is made.
lem-sf-rational-left-coefficient-localization vs lem-sf-rational-comparison-normalization: the existing statement is about an explicitly constructed tensor comparison datum with its eight tensor/phi equations; the new statement controls actual compact-support functor images of scalar associators and unitors.
lem-sf-common-transition-coefficient-mates vs lem-weil-pbc-mate-pasting: the existing result transfers equations between specified squares to equations of mates; the new lemma first derives the required common left square from the identity representative and actual common-stage morphism normalization, then derives its right equation. This representative calculation is absent from the generic mate statement.
lem-sf-common-transition-coefficient-mates vs lem-coef-closed-transpose-cocycles: closed in the existing title means closed IMMERSIONS at finite coefficients, and its morphisms are shriek mates for immersions; the new lemma concerns algebraically closed COEFFICIENTS and literal field-pair transitions.
lem-sf-integral-refinement-diagram-admissibility vs lem-sf-integral-compactification-system-realization: the existing theorem explicitly assumes admissibility of every intermediate object; the new statement establishes those hypotheses for finite identity/binary refinement diagrams.
lem-sf-integral-refinement-diagram-admissibility vs lem-coef-integral-compact-support: the existing theorem treats one compact-support image with canonical reduction comparisons; the new statement supplies uniform bounds, actual normalized transitions and compatible etale witnesses for all proper/open intermediates in a diagram, including hidden open intermediates.
lem-sf-integral-refinement-diagram-admissibility vs def-sf-integral-system-expression-domain: the existing node defines a predicate with intermediate conditions; the new node proves this predicate holds for the specified refinement diagrams.
lem-sf-integral-normalized-refinement-pasting vs lem-sf-ambient-proper-open-pasting: the existing theorem proves intrinsic pasting in finite or semilinear SYSTEM derived categories; the new theorem identifies the specified completed INTEGRAL maps by their open-transpose normalization and obtains the corresponding integral equations.
lem-sf-integral-normalized-refinement-pasting vs lem-sf-integral-compactification-system-realization: the existing theorem provides the realization comparisons for structural generators and whiskering, but does not state identity/transitivity for an independently supplied family rho characterized by its ringed-site open transpose. The new theorem supplies exactly that identification and its laws.
lem-sf-integral-normalized-refinement-pasting vs lem-pur-compact-support-limit-equation-realization: the existing theorem imposes separated schemes and uses the constant-tower word comparisons of fix-lem-exchanges; the new statement permits nonseparated finite-type schemes and uses the actual semilinear realization and the normalized integral rho maps.
lem-sf-integral-normalized-refinement-pasting vs lem-sf-integral-compactification-comparison-bridge: the existing result compares two geometric COMPOSITION normalizations for f followed by g, on absolutely separated schemes; the new result concerns refinements of one morphism's compactifications and open-transpose uniqueness.

## Review by Q148

I read the stage-1 brief, stage-1 contract, worker role, GOAL.md, the SETUP three-level route rules, the current chapter and compatibility unit, all of delivery-errors B–E in both retained copies, and the released repair order. This is a below-unit decomposition of the existing coefficient-compatibility route. No unit or chapter is edited. I read the exceptional inverse-image blueprint's derived-limit, rationalization, common-stage and refinement-compatible adjunction paragraphs and the tensor–Hom unit statement. I also read the complete live coefficient-coherence Lean record and its proof docstring. The source blueprint does not itself prove the additional normalization details, so the assembly remains explicitly agent-origin.

For the ring node I read the ring coefficient-data definition, arbitrary-ring projection-cocycle statement, open-tensor normalization statement and successive-derived-quotient normalization statement, together with Stacks 0E8I (`sites-modules.tex`, `lemma-j-shriek-and-tensor`) and 0GL6 (`more-etale.tex`, `remark-Rf-lower-shriek-change-of-rings`). The Stacks statements are finite/open models, not claims about completed coefficients; the arbitrary-ring DAG statement provides the actual generality. The new lemma includes both the ordinary target-ring equation and the faithful-full-inclusion conclusion needed by assembly step 1. In particular nonflat ring changes require no invalid restriction-of-scalars detection.

For the rational node I read the raw-localization definition, the integral residue-Tor statement, the actual finite-free ordinary-to-completed scalar comparison, and scalar-extension composition. Its hypotheses explicitly fix the actual rational functor on arrows, including linear sums of integral arrows. The conclusion includes the functor-image associator and unitor terms, so assembly step 3 can use the node statement itself rather than its prospective proof. Every raw object is an integral representative, and residue Tor puts that representative in the required domain. Embeddings are handled through their images. I retained both composition and identity, which was the thin point of the previous returned proof.

For the common-transition node I read the literal-pair/colimit-Hom definition, the adjunction-mate definition and every clause of mate pasting. Its formula is typed from I_i F_i K to I_j F_j L, with delta from I_i F_i K to I_m F_m T_im K. Applying it to the inverse transition represented by identity at j produces exactly the left equation; canonical identity-transition unitors are kept. The counit equations and injectivity of the closed Hom bijection give the right equation. Assembly step 4 cites a statement that contains BOTH equations, not mere naturality within one finite field. No inclusion I_i is presumed faithful.

For integral admissibility I read the complete system-realization theorem, the intermediate expression-domain definition, derived-complete and finite-Tor definitions, open finite-Tor preservation, finite-type dimension bounds, the direct-image finite-Tor bound, etale-origin equivalence, and integral compact-support reduction theorem. The result only considers finite words in proper direct image and quasi-compact open extension in an identity/binary refinement diagram. It does not extend the claim to arbitrary pullbacks or tensor expressions. The finite number of proper maps gives one level-independent bound; empty sources use bound zero. Canonical reduction comparisons establish normalized TRANSITIONS as well as bounded levels. The origin equivalence is full on the bounded constructible categories, so transition arrows as well as objects can be transported, and their identities/composites follow by faithfulness. This checks the compatibility demanded by the system theorem, not just separate origin witnesses.

For integral refinement pasting I read the intrinsic semilinear proper/open pasting statement and the total-limit system realization, including their clauses that intertwine units, counits, compositors, interchange and whiskering. I checked the open transpose determines e_u uniquely and the same normalization selects the actual integral rho. The statement makes the comparison of actual maps explicit; neither finite evaluation nor restriction of scalars detects equality. Assembly step 6 first cites the admissibility statement, then applies the pasting statement, matching every one of its hypotheses.

Assembly step 2 uses exactly the counit normalization in the unchanged item and clauses (1), (3), (4) of mate pasting. It transposes the compared composites and invokes only already established left laws, also for the later rational application. Assembly step 5 uses the origin node's bounded-category equivalence and the finite compactification theorem's canonical refinement cocycle, with full inclusions and the input's open normalization identifying the same maps. I read Stacks 0F7B (`more-etale.tex`, `lemma-shriek-proper-and-open`) and 0F7C (`lemma-shriek-proper-and-open-compose`) as its finite model, including their torsion/bounded-below scope. It does not apply that finite theorem at integral stages. Assembly step 7 is only localization preserving identity/composition, literal-pair conjugation and cancellation; its only nontrivial domain input is the cited residue-Tor theorem. Every cited node has a verbatim full statement quote in citations.json, so the hypotheses used remain visible to the reviewer.

I tested identity scalar maps, identity and binary refinements, empty source schemes, n=1, nonflat successive quotient maps, ramified en coefficient maps, integral-to-finite mixed composites, identity field embeddings and equal common fields. None is excluded by a new hypothesis. I checked that the rational and common arrow normalizations remain necessary and present. The proof never reflects equality through localization or finite evaluation. All extracted derived comparisons are in actual derived categories, not replacements by per-degree cohomology isomorphisms. The new nodes have no proof steps and no proof dependencies; they carry precise hypotheses rather than a proof disguised in their statement. There are five obligations, and none asks again for the full four-part CoefficientCoherence result. The parent is below 3000 characters and has no step above 2000 characters.

All five new nodes were searched using the authorized msearch.py with two semantic phrasings, Loogle, grep and LeanSearch. Queries/results are retained unmodified in searches.jsonl and per-node search-result files. General mate lemmas (`mateEquiv_counit`, `mateEquiv_vcomp`, `mateEquiv_hcomp`) were inspected in Mathlib/CategoryTheory/Adjunction/Mates.lean; they do not state the common-stage representative action or the proper/open/integral comparisons. Other hits concerned ordinary module-sheaf pushforward composition, abstract localization, topological constructible sets or scheme normalization. None is an exact match or a one-line specialization for a new node. Loogle's unknown-identifier answers are recorded as such rather than fabricated matches; the semantic and source searches independently ran. No source was unavailable.

## Original argument preservation map

This section preserves the complete returned argument, including its old citations and source places, as worker handoff material. It is not a proof attached to a new unsplit node. New-node statements state the corresponding intermediate result; later workers retain this exact argument when splitting them. Thus the re-split distributes work without deleting or blurring it.

### Original step 1 → ring scalar node

Fix $c$ and use the statement's notation. All domains and exact adjunctions are data of $P$, so no existence or preservation theorem for an exceptional adjoint is used here. At ring stages $I_{s,T}$ is a full subcategory inclusion, hence reflects equality of arrows. Expanding the $q$, scalar-composition and scalar-identity normalizations reduces the left ring equations to the corresponding equations for $Q_a$ on ordinary derived categories: substitute the displayed equations, use naturality to move each $r$ and $\sigma$ to the outside, and cancel the inverse pairs. This also shows that different proofs of Allowed or of a ring-map equality cannot introduce a freely chosen comparison.

Cited statements: def-sf-categories, def-pur-integral-compact-support-coefficient-data.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Construction of finite/integral functors; normalization fields in the live construction record.

### Original step 2 → ring scalar node

For the proper factor $p_c$, apply [lem-pur-ringed-coefficient-projection-cocycle] to $R_s\to R_t\to R_r$, identified with inverse-image coefficient sheaves by their specified pull isomorphisms. It gives $\chi_d\tau_Y=Rp_{c,*,r}(\tau_{\bar X})\,\chi_b(S_a)\,S_b(\chi_a)$, with the argument/whiskering conventions of that node, and the identity law. This node allows arbitrary ring maps and unbounded derived inputs. For the open factor, the inverse of the scalar comparison is the open adjunct of the scalar extension of the open unit, by [lem-sf-open-tensor-normalization]. The two successive scalar units are the composite unit by [lem-sfb-successive-derived-quotient-normalization]. Transpose the two proposed open composites: each is that same composite unit followed by the same pullback/scalar identification. The adjunction bijection makes the open composites equal. For the identity map the same transpose is the open unit itself, so the comparison is identity under the scalar unitor.

Cited statements: lem-pur-ringed-coefficient-projection-cocycle, lem-sf-open-tensor-normalization, lem-sfb-successive-derived-quotient-normalization.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Ringed-site proper and open coefficient comparisons; Stacks 0GL6 and 0E8I as finite/open models.

### Original step 3 → ring scalar node

The actual compact-support comparison $Q_a$ is proper comparison followed by the proper image of the open comparison. Paste the two equations of Step 2. Naturality of the proper comparison moves the intermediate open arrow across it; the middle tensor associators cancel with their inverses. The result is
$$H_r(\tau_X)\,Q_b(S_a^X)\,S_b^Y(Q_a)=Q_d\,\tau_Y(H_s).$$
Pasting the two identity equations gives $H_s(u_X)Q_1=u_YH_s$. These are equations in the TARGET ring's derived category, not equations inferred from restriction of scalars. Substitute them into the normalizations expanded in Step 1. The outside $r$ and $\sigma$ are isomorphisms and $I_r$ is faithful. Cancel them to obtain exactly the ring left cocycle and ring left identity law for the specified $q$, $\alpha$ and $u$. Nonflat finite quotients and mixed integral/finite chains are covered by the same arbitrary-ring statement.

Cited statements: def-pur-integral-compact-support-coefficient-data, def-sf-categories.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Proper/open composite coefficient map and its normalized scalar associators.

### Original step 4 → assembly step 2 (also invoked at rational stages)

The defining counit equation says that $b_{a,L}$ is the $F_t\dashv G_t$ transpose of $T_a^Y(\varepsilon_{s,L})q_{a,G_sL}^{-1}$. Thus it is uniquely determined. For two changes, transpose the two sides of the desired right cocycle under $F_r\dashv G_r$. First move the scalar associator across the counit by naturality. Next move the inner $b_a$ through $q_b$ by naturality. Apply the counit equations for $b_b$ and $b_a$ in that order. The transpose becomes the old counit extended along the composite scalar functor, preceded by the inverse of the composite $q$. Step 3 identifies this $q$ composite with $q_d$ with $\alpha_X,\alpha_Y$ inserted. It is therefore also the transpose of $b_d\alpha_X$. Injectivity of transposition proves the right cocycle. For an identity change use the same calculation with the scalar unitor and Step 3's identity equation; both transposes are the old counit with the scalar unit identifications. This is precisely the pasting and identity rule for mates in the cited statements, not a presupposed cocycle for $b$.

Cited statements: def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Coefficient counit-transpose argument; constructible adjunction coefficient Step 6.

### Original step 5 → rational localization node; right mate calculation in assembly step 2

Every rational object is an integral representative by raw scalar localization, and [lem-coef-integral-residue-tor] puts it in the integral finite-Tor domain. The ordinary/completed scalar comparison and scalar-composition statements identify rational extension, its associator $\alpha^{\rm rat}$ and unitor $u^{\rm rat}$ with localized integral extension and its balanced maps. Fix $E\to L\to M$ and such a representative $K$. Localize the integral left cocycle from Step 3. Rational $q$ normalization identifies the localized $q$ components with $q^{\rm rat}$; the actual localized scalar functors identify their whiskered components. The NEW rational morphism normalization at the target field $M$ gives
$$F_{c,M,\rm rat}(\alpha^{\rm rat}_{X,K})=R_M^Y(F_{c,M,\rm int}(\alpha^{\rm int}_{X,K})).$$
After the specified scalar object identifications, every term of the localized Step 3 equation is therefore the corresponding term of the rational left cocycle. For the identity field change the same normalization at $E$ gives $F_{c,E,\rm rat}(u^{\rm rat}_{X,K})=R_E^Y(F_{c,E,\rm int}(u^{\rm int}_{X,K}))$; localizing Step 3's identity equation now proves the rational left identity. Merely localizing the $q$ components would give neither displayed functor-image identification. Equality is pushed forward, never reflected through localization. Apply the counit-transpose calculation of Step 4 to these repaired rational left laws and the supplied rational adjunctions to obtain the rational right cocycle and right identity. Embeddings are handled by identifying the source field with its image, as in the scalar-composition node.

Cited statements: def-weil-rationalization-karoubi, lem-coef-integral-residue-tor, lem-weil-finite-free-completed-scalar-comparison, lem-weil-scalar-extension-composition, def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Rationalization and common-stage paragraph; live coefficient argument Step 12.

### Original step 6 → common-transition node

Use the additional MORPHISM normalization from the corrected statement. The arrow $(\tau_{ij,K}^X)^{-1}:I_i^XK\to I_j^XT_{ij}^XK$ has at the common stage $j$ the identity representative, with the canonical identity-transition unitor inserted. Substitute this representative in the normalization formula. Step 5's rational left identity law, now proved using the added rational morphism normalization, cancels the $j\to j$ scalar comparison with that unitor, giving
$$F_\Omega((\tau_{ij,K}^X)^{-1})=q_{j,T_{ij}^XK}\,I_j^Y(q_{j/i,K})\,(\tau_{ij,F_iK}^Y)^{-1}\,q_{i,K}^{-1}.$$
Right-compose with $q_{i,K}\tau_{ij,F_iK}^Y$ and cancel inverse pairs. This is the displayed common left cocycle, including exactly its heterogeneous endpoint identifications. The existence of the identity representative and its composition rule is part of the pair-category definition; no faithfulness of inclusion of a finite field is asserted.

Cited statements: def-weil-algebraically-closed-coefficients.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Common-stage construction, now explicitly including its action on transition arrows.

### Original step 7 → common-transition node

For the common right cocycle, compare the counit transposes under the CLOSED adjunction. The left path is the pasted mate of the rational $q_{j/i}$ and the common $q_j$; the right path is the mate of $q_i$ conjugated by the two transition isomorphisms. Step 6 says that these left squares agree; its cancellation uses the repaired rational left identity of Step 5. The rational right identity likewise follows by the counit-transpose calculation in Step 5, rather than by an unnormalized functor image of the scalar unitor. Each recorded $b$ is the mate of its inverse $q$ square by its counit equation, as in Step 4. The pasting and change-of-adjunction rules of [lem-weil-pbc-mate-pasting] therefore identify their right squares, giving
$$b_{j,T_{ij}^YL}\,I_j^X(b_{j/i,L})=G_\Omega((\tau_{ij,L}^Y)^{-1})\,b_{i,L}\,\tau_{ij,G_iL}^X.$$
In more explicit terms, naturality moves each transition across the counit, the two individual counit equations remove $b_j,b_{j/i}$, and Step 6 replaces the remaining inverse-$q$ composite by the inverse of $q_i$. Injectivity of the closed Hom bijection finishes. Stagewise equality alone would not have supplied Step 6; that is the missing input in the old statement.

Cited statements: def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Closed coefficient counit-transpose and transition pasting.

### Original step 8 → assembly step 5

At a finite stage, a constructible finite-Tor input has a bounded etale-origin witness by [lem-sf-proetale-constructible-origin]. All compactification ambient schemes are finite type over $k$ because they are proper over $Y$, so the hypotheses of [prop-compactification-coherence-detailed] hold. Its actual finite proper/open refinement arrows are identity and transitive on this domain. The ring refinement normalization in $P$ picks these SAME maps: the open adjunction bijection and the invertible restriction map determine $e_u$ uniquely from the equation that its transpose followed by restriction is the open unit. Substituting this $e_u$ in the proper-composition formula determines $I_s(\rho_{u,s})$. The finite coefficient realizations therefore conjugate the canonical maps of the proposition to the recorded $\rho$. Cancelling $r_d^{-1}r_d$ proves $\rho_{vu}=\rho_v\rho_u$ and cancelling $r_c^{-1}r_c$ proves $\rho_1=1$.

Cited statements: lem-sf-proetale-constructible-origin, prop-compactification-coherence-detailed, def-sf-categories.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Compactification refinements, finite coefficients; Stacks 0F7B, 0F7C.

### Original step 9 → integral diagram admissibility node

For integral refinements, verify the domains of the system realization, rather than try to detect equality by finite evaluations. An integral finite-Tor input has normalized reduction systems with one common Tor interval by its defining conditions. At each level $j_!$ preserves this interval and constructibility by [lem-trf-open-ctf]. Each intervening proper map has finite-type source and a finite dimension bound by [lem-kun-dimension-finite-type]; choose bound zero for the empty source. Apply [cor-sf-direct-image-ctf-proetale] to enlarge the upper endpoint by $2d$ for that proper map. There are only finitely many maps in an identity or binary refinement diagram, so take the maximum of these finitely many bounds, independently of the coefficient level. For normalization apply [lem-coef-integral-compact-support] successively to each open map (compactification with proper factor identity) and each proper map (open factor identity). Its canonical reduction comparisons, compatible with successive reductions, identify their outputs with reductions of complete integral constructible objects. Thus the intermediate systems have normalized transitions, rather than merely bounded levels. Their levels have etale-origin witnesses by [lem-sf-proetale-constructible-origin]. The system realization theorem now applies with every intermediate-domain hypothesis verified.

Cited statements: def-weil-derived-complete-integral-detailed, def-weil-finite-tor-amplitude, lem-trf-open-ctf, lem-kun-dimension-finite-type, cor-sf-direct-image-ctf-proetale, lem-sf-proetale-constructible-origin, lem-coef-integral-compact-support, def-weil-integral-rational-qbar-compact-support, lem-sf-integral-compactification-system-realization.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Integral realization of a finite refinement diagram; uniform-level domain check.

### Original step 10 → integral normalized refinement pasting node

On the ordinary derived categories of strict quotient systems the normalized proper/open maps satisfy the actual identity and refinement pasting equations by [lem-sf-ambient-proper-open-pasting]. Apply the total-limit functor to these equalities. The realizations $c_V$ of [lem-sf-integral-compactification-system-realization] intertwine the system open maps, units, counits, direct-image compositors and proper/open interchange with the actual integral maps, including whiskering. Consequently they send this equation to the integral proper/open refinement equation with its specified ringed-site normalization. The ring normalization of $P$ selects precisely that integral map, by the same uniqueness of the open transpose used in Step 8. Conjugating by the integral left realizations and cancelling the middle inverse pairs proves both integral refinement laws. This uses equality BEFORE evaluation followed by a functor, and never the invalid inference that equal evaluated arrows must have been equal system or integral arrows.

Cited statements: lem-sf-ambient-proper-open-pasting, lem-sf-integral-compactification-system-realization, def-sf-categories.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Integral refinement cocycle from intrinsic system pasting and its normalized total-limit realization.

### Original step 11 → assembly step 7

For a rational refinement evaluate on an integral representative. Its component is by the refinementRational normalization the localization of the integral component. Apply the localization functor to the two equations in Step 10 and use preservation of identities and composition. Every rational object has such a representative by raw localization, and the residue-Tor result puts it in the domain of Step 10. Thus the two natural transformations have equal components on every object, which proves both rational refinement laws.

Cited statements: def-weil-rationalization-karoubi, lem-coef-integral-residue-tor.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; RefinementRational and raw localization of the integral identities.

### Original step 12 → assembly step 7

A closed object is a literal pair $(i,K)$ and hence is in the image of $I_i^X$. On this object the refinementCommon normalization is
$$\rho_{u,\Omega}=q_{d,i}\,I_i^Y(\rho_{u,i})\,q_{c,i}^{-1}.$$
For successive refinements substitute this formula twice; the middle $q_{d,i}^{-1}q_{d,i}$ cancels, functoriality of $I_i^Y$ combines the remaining two arrows, and Step 11 replaces their composite by $\rho_{vu,i}$. This is the formula for $\rho_{vu,\Omega}$. For the identity refinement the same cancellation gives identity. Every object is covered, so both are equalities of natural isomorphisms. This componentwise check needs no fully faithful finite-field inclusion and does not add a Karoubi completion.

Cited statements: def-weil-algebraically-closed-coefficients.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; RefinementCommon on the literal finite-stage pairs.

### Original step 13 → assembly step 7 and record assembly

Steps 3--4 supply all three fields of CoefficientRingCoherence; Step 5 supplies rationalCocycle and its two identity fields; Steps 6--7 supply the two common fields; Steps 8, 10, 11 and 12 supply the two refinement fields at every stage. Assemble these four records into CoefficientCoherence. No new choice of any comparison is made. The empty scheme uses the same equations in the zero categories; positive levels, identity coefficient maps, ramified $en$ transitions, mixed reduction chains and nonflat quotients were all retained. All assertions concern the already supplied constructible adjunctions; no ambient pro-etale right adjoint or purity theorem was assumed.

Cited statements: .

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md; Assembly of the four coherence subrecords.
