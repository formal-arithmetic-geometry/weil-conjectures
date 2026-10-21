# Stage-1 repair: lem-sf-semilinear-proper-open-mate-pasting

## Files written

The item and six new statement nodes are under dag/nodes/sec-six-functors/. No Lean, repository files, compiler or launcher files were changed. The previous attempt initially found only dispatcher markers and copied the live item. This retry started from its retained six-node split, report, citations and search log. I preserved that work, compared its item with the current live file, and repaired it in the sandbox. The delivery tool supplies the rebase on the current meeting-point branch.

- lem-sf-semilinear-alpha-pullback: statement; new, searched in Mathlib: no full match; statement-only, status unsplit.
- lem-sf-semilinear-scalar-ordinary-comparison: statement; new, searched in Mathlib: no full match; statement-only, status unsplit.
- lem-sf-semilinear-proper-open-mate-pasting: statement; item assembly; proof under 3000 characters.
- lem-sf-semilinear-clopen-unit-projector: statement; new, searched in Mathlib: no full match; statement-only, status unsplit.
- lem-sf-semilinear-compositor-coherence: statement; new, searched in Mathlib: no full match; statement-only, status unsplit.
- lem-sf-adjunct-conjugate-open-factor: statement; new, searched in Mathlib: no full match; statement-only, status unsplit.
- lem-sf-semilinear-scalar-derived-comparison: statement; new, searched in Mathlib: no full match; statement-only, status unsplit.

## Attachments

None. Searching lean/WeilConjectures for the blueprint tag and semilinear proper/open mate terminology found no exact completed declaration. The recorded Sheaf.SixFunctors.SemilinearProperOpenMatePasting module was read, including its private adjunct_transport helper, gamma_adjunct, coefficient comparisons and compositor_associativity. Its aggregate pasting theorem and coefficient comparisons still contain sorry, so the attachment criterion fails. This is a finer stage-1 split, not a Lean proof delivery.

## WANTED

None. All documents used are available in literature/.

## What was wrong and what changed

The return required the 11946-character proof to be split finely, keeping its statement unchanged. The live proof mixed the mathematical argument with appended S4, C8, V2 and T3 implementation accounts. I extracted their reusable arguments into six statement-only nodes with self-contained statements and exact source locations; the previous attempt's supporting arguments are retained below in the report. The parent now assembles those arguments with the already existing varying-ring pasting and finite-normalization statements. This is a substantive replacement, not an unchanged re-push. The old argument remains in the read-only repository and the historical Lean/proof review fields are preserved.

The latest explicit route note resolves the earlier wording: the NEW nodes must be statement-only, status unsplit, with no proof steps; later stage-1 workers split them. All six new nodes now have empty proof and proof_deps and null proof_origin. Their earlier arguments (1085–2152 characters each) are retained in this report. The parent assembly is under 3000 characters and every step is below 2000 characters. The parent statement is unchanged; no coefficient flatness or finiteness was added. No statement dispute was found.

## Review by Q49

I read GOAL.md, the three-level rule in SETUP.md, roles/worker.md, the stage-1 contract, delivery-errors B–E (including its duplicate copy), the chapter sec-six-functors and unit sk-thm-sf-compatibility. The route remains the unit's composition, base-change and coefficient-compatibility route. I read fix-prop-coherence.proof.md in main-20261015: its units/counits/evaluation argument is the blueprint ancestor of this item. All six new nodes record that exact ancestor through the two intervening created nodes. Whole-blueprint searches for clopen projection, scalar restriction, conjugate, compositor, base-change cube and fully faithful found no equivalent blueprint node. Whole-DAG statement/title searches and the same-tag statements were compared; relevant overlapping results are distinguished below.

For the item, I read Stacks more-etale.tex at 0F7B (lemma-shriek-proper-and-open), 0F7C/0F7D (the two composition lemmas) and 0F7F (lemma-shriek-proper-and-open-base-change). Those sources concern fixed-ring etale comparisons. I do not claim that they state the arbitrary semilinear extension; the additional system arguments are expressly agent-written and rely on the existing system-section theorem. No SGA source is used.

Parent step 1 uses the full construction assertion of lem-sp-varying-ring-proper-open-pasting: it states the clopen lift, alpha, its actual system mate and the semilinear transition compatibility. Parent step 2 uses the new generic conjugate/open-factor transport theorem and the new clopen unit-projector theorem; the open-normalization theorem supplies the invertible open unit, and mate pasting identifies the composite-adjunction word. Expanding alpha cancels beta inverse, so its transport hypothesis is satisfied. The remaining unit/counit cancellation is a triangle identity and gives the inverse direct-image compositor. Parent step 3 uses the varying-ring theorem's actual vertical/horizontal/identity clauses, not its proof. Parent step 4 uses the new alpha cube and the existing exchange-mate cube plus mate-pasting laws: these give the two E_p/E_r words with the endpoint betas. Parent step 5 uses the derived scalar comparison theorem's actual preservation-of-alpha equality and the abstract pasting theorem; equality is established on systems. Parent step 6 uses the varying-ring evaluation clause and the constant-tower finite clause. Apply the latter to the constant tower of the single evaluated input so its every level has the same finite etale-origin witness; there is no unsupported use of a theorem requiring witnesses at other coefficient levels. Parent step 7 uses the new compositor theorem, which states all three coherence equations and equality transport. citations.json quotes the full verbatim statement of each dependency of every parent step, so all the clauses just described are present in the quotes.

The following six paragraphs review the retained supporting arguments, not completed splits of the new nodes. For lem-sf-semilinear-clopen-unit-projector I read sites-modules 03DI, label lemma-extension-by-zero, and the neighboring localization construction, and compared the actual varying-ring arrows. Its first step proves the product decomposition by the disjoint-cover equalizer with zero intersection and constructs the inverse by gluing; its system/derived hypotheses are exactly those of lem-coef-semilinear-derived-sections. Its second step uses the named exact-derived factorization theorem for the exact insertion functor and computes the specified adjunction units in those coordinates. Thus J_s to S_s is the transpose of the given inverse open unit, rather than any chosen equivalence. The identity and zero restrictions are computed on the two factors. This is more than the already existing definition of pi and includes its required normalization.

For lem-sf-adjunct-conjugate-open-factor I read Stacks 07A7, label remark-base-change, the existing conjugate-unit statement and mate/composite-adjunction definitions, and the private adjunct_transport argument in the recorded Lean module. Its first step derives transport of the Hom bijection by naturality and the conjugate-unit equation, applied to the two composite adjunctions. Its second step expands the inner J_b adjunct, cancels d followed by its inverse, uses naturality of u_b, and cancels u_b. All five categories, each adjunction, both comparison isomorphisms, the object M, the map f and its factorization hypothesis are introduced in its statement. In particular the invertibility of u_b is an explicit hypothesis. This general five-category cancellation is not the geometric lambda clause of the parent and applies independently of coefficient systems.

For lem-sf-semilinear-alpha-pullback I read the 0F7F diagram and its proof. Step 1 uses the open-normalization theorem's formula for beta inverse and injectivity of the open Hom bijection, with compositor coherence and mate pasting. Step 2 uses fibre-product universality for both the selected component and its complement, the existing varying-ring geometric clopen assertion, and the new unit-projector formula; the pullback preserves the split pair and its identity/zero map. Step 3 substitutes those equalities in the actual alpha formula and uses the localization universal property to descend the equality. The conclusion is an equality of exact alpha transformations before proper mating; the parent's derived Gamma base-change equation still requires the generic mate-cube theorem. Arbitrary h is allowed, and the square itself is not assumed cartesian: only the base-change cube is cartesian.

For lem-sf-semilinear-scalar-ordinary-comparison I read sites-modules 03D7 (lemma-adjoint-pullback-pushforward-modules), 03DI, and 03CY (lemma-sheafification-presheaf-modules), and read the full ring-sheaf-change adjunction statement. Step 1 constructs rho from the compatible B actions and verifies B-linearity of every transition by tau_n phi_(n+1)=phi_n; exactness is componentwise, and the pushforward comparison is the identity on M_n(H times_Y X). Step 2 obtains the single-level inverse-image comparison from the ring-change theorem on degree-zero objects; identified constant coefficients and exact geometric inverse image ensure this is an ordinary comparison. Its unchanged underlying maps commute with all transitions, so ordinary componentwise extensionality assembles the comparison and its unit/counit equations. This argument uses ordinary maps, where component extensionality is valid. Step 3 uses the explicit direct-sum extension and the sheafification statement: its underlying abelian sheaf is unchanged by restricting actions, and uniqueness of its extended module action gives the scalar comparison. The open unit fixes that map. The beta formula and the clopen product projector then show preservation of alpha. I added the explicit sheafification citation during this review to avoid silently assuming a coefficient/sheafification interchange.

For lem-sf-semilinear-scalar-derived-comparison I read the ring-change node's precise adjunct clause, along with 0D6D/0D6E (derived pullback/direct-image composition) and 07A6 (lemma-adjoint), the places it cites. Step 1 localizes the ordinary comparison equations, using the localization theorem and the explicit localized-adjunction theorem for the open unit. The direction is explicit: a_j inverse is the left open mate of b_j. Step 2 defines d_f by the full unit–b_f inverse–counit word. Evaluation of its adjunction word agrees with the level word by the system-section theorem; the ring-change adjunct formula with t=counit and t-sharp=identity identifies it with the specified level d. Isomorphism detection for constant-B systems proves the system comparison invertible. No equality of arbitrary derived morphisms is deduced from evaluation. I corrected the displayed word to show its middle b_f inverse factor, avoiding an implicit typing convention.

For lem-sf-semilinear-compositor-coherence I read 0D6D (lemma-derived-pullback-composition), 07A7 and the section-normalized composition definition in def-sp-varying-ring-operations. Step 1 proves the ordinary section coherence by the universal property of the same iterated fibre product and presheaf composition, including identity maps and scalar structural maps. Step 2 uses conjugation/mate pasting to obtain the inverse-image equation, then the localization universal property (its statement explicitly preserves identities and composition) descends it on exact functors. Step 3 uses mate pasting under the specified adjunctions for direct image and open extension. Equality elimination handles supplied arrow equalities; no different chosen adjunctions are identified. The former constant-B direct-image coherence citation was insufficient alone for varying coefficients and has been replaced by this proof.

Small cases were checked on each new statement. For the clopen lemma, s=id makes t and pi identities, while s empty gives the zero projection; neither needs finite coefficients. In the transport lemma, taking all comparison isomorphisms and u_b to identities reduces to the composite Hom-bijection formula; without invertible u_b its cancellation would fail, which is why that hypothesis is retained. For the alpha cube, h=id gives reflexivity, a cartesian Q gives pi=id, and the identity-left refinement gives the pulled-back clopen section. For scalar restriction, B=C_n with identity maps gives the normalized constant-ring identity, while arbitrary nonflat maps (for example Z to Z/2) require no tensor exactness: this is restriction and identified geometric inverse image. The zero ring and empty scheme give zero-module formulas throughout. For coherence, identity arrows reduce to the specified identity comparisons and all three triple-composition equations have matching domains. None requires scheme properness except the proper/open alpha square, where both vertical maps are proper exactly as in the item.

Mathlib searches were run only through msearch.py, with the new node id in mind, using leanfinder, loogle, grep and leansearch, plus a second semantic phrasing for every node. All searches are recorded in searches.jsonl and their full output is retained under search-results/. I read the hits, including Adjunction.leftAdjointCompIso_assoc, unit_conjugateEquiv, conjugateEquiv_mateEquiv_vcomp, comp_homEquiv, the sheaf-module pullback API and restrictScalars. I read Mates.lean around unit_conjugateEquiv (line 300) and CompositionIso.lean around leftAdjointCompIso_assoc (line 170). These are tools already represented by the existing mate/conjugation nodes; none states a whole new node in one specialization. In particular the coherence node must still prove its ordinary section equation and descend it, and the transport node also cancels a fully faithful factor in a five-category diagram. No Mathlib leaf was falsely declared from one partial hit. support-citations.json retains the previous attempt's verbatim statement catalog for the supporting arguments now in this report.

The B–E checks therefore include complete self-contained statements, definitions with the right scope, no proof hidden in an unsplit statement, all six children statement-only and their retained arguments short, literal TeX once, actual tag/label source locations, logged searches, no duplicate statement, no substitution of a definition for an unproved comparison, explicit hypotheses for every mate, and the small cases above. The parent has a stage-1 proof in words; the six children are unproved statements, and no Lean proof completion is claimed.

## Unfinished work

The requested finer stage-1 split is complete. The six new statements intentionally remain unsplit for later stage-1 workers; their retained arguments are report material. Existing Lean sorry declarations are outside this task. The repaired format has passed server preflight; a final dry run and push follow the notation clarification described below.

## Not duplicates

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pd-ringed-tensor-adjunction-mate: the existing statement identifies the oplax tensor and unit maps of a single ringed pullback as adjunction mates of a lax pushforward structure. The new statement constructs exact restriction from varying-ring systems to constant-B towers and its normalized ordinary pullback, pushforward and open-extension comparisons, including preservation of alpha; it asserts no tensor/oplax structure. Neither statement specializes to the other.

lem-sf-semilinear-scalar-derived-comparison vs lem-pd-ringed-tensor-adjunction-mate: the existing statement concerns a single ordinary ringed adjunction and its tensor/oplax mate, not the localization of a tower restriction functor or invertibility of its derived direct-image mate. The new statement asserts these tower-level comparisons, their level normalization and preservation of alpha. The coefficient-system localization and isomorphism-detection argument is absent from the existing statement.

The repair explicitly asks to extract the supporting arguments rather than duplicate the parent's assertions. The following comparisons include every live nonmerged node sharing a source tag; merely sharing a tag is not an equality of statements. The full same-tag statement catalog is retained as duplicate-statements.json.

lem-sf-semilinear-alpha-pullback vs lem-sf-semilinear-proper-open-mate-pasting: the existing item asserts the proper Gamma mate and its derived base-change/pasting/finite-normalization package; the new lemma proves the earlier exact alpha cube, an input to that mate calculation.

lem-sf-semilinear-alpha-pullback vs lem-asd-compact-support-graph-sheaf-normalization: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Graph comparison agrees with the canonical map into direct image and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-cbc-normalized-proper-open-pasting: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Horizontal pasting for fixed normalized proper/open comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-cbc-complete-proetale-composition-pasting-coherence: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Composition Pasting Coherence and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-amb-unbounded-proper-open-interchange: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Unbounded torsion-coefficient proper/open interchange with its canonical maps and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-asd-compact-support-graph-geometric-base-change: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns The specified forward graph comparison at a geometric base change and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs def-cbc-strict-tower-composition-maps: the existing node defines Canonical strict-tower composition comparison maps; the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating, rather than introducing that definition again.

lem-sf-semilinear-alpha-pullback vs lem-cbc-normalized-proper-open-geometric-normalization: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Refinement and base change for fixed normalized proper/open comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs def-cbc-finite-constant-coefficient-transport: the existing node defines Normalized finite scalar and etale-origin transport to constant coefficient modules; the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating, rather than introducing that definition again.

lem-sf-semilinear-alpha-pullback vs lem-asd-compact-support-finite-graph-isomorphism: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns The specified graph comparison for finite etale morphisms and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-amb-unbounded-proper-open-base-change: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Base change of unbounded proper/open interchange and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-cbc-complete-proetale-refinement-exchange-coherence: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Refinement Exchange Coherence and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-pur-compact-support-site-coherence: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Compact-support site comparison respects compactification calculus and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs def-asd-compact-support-graph-comparison: the existing node defines The specified sheaf and unbounded derived graph comparison; the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating, rather than introducing that definition again.

lem-sf-semilinear-alpha-pullback vs lem-sp-proper-open-comparison-normalization: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Structural normalization of explicit proper/open comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-asd-compact-support-graph-derived-isomorphism: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Invertibility of the specified graph map on unbounded complexes and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-asd-etale-compact-support-normalization: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Normalization of compactified etale support and its exchange and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-sp-proper-open-tower-comparison: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Open-adjunction normalization of proper/open interchange on strict coefficient towers and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs def-cbc-strict-tower-open-extension: the existing node defines Normalized exact open extension on strict constant-coefficient towers; the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating, rather than introducing that definition again.

lem-sf-semilinear-alpha-pullback vs lem-cbc-strict-tower-proper-open-calculus: the existing calculus has one constant B at every tower level; the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating with arbitrary varying C_n.

lem-sf-semilinear-alpha-pullback vs lem-pur-etale-horizontal-support-tower: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Etale compact-support composition on a pullback compactification tower and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-asd-compact-support-graph-sheaf-normalization-transpose: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Transpose of graph comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs lem-asd-compact-support-graph-coherence: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Base-change, proper-refinement and identity equations for the graph map and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-alpha-pullback vs def-cbc-strict-constant-tower-operations: the existing node defines Strict constant-coefficient towers and normalized inverse/direct-image operations; the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating, rather than introducing that definition again.

lem-sf-semilinear-alpha-pullback vs def-cbc-strict-tower-proper-open-arrows: the existing node defines Unit-normalized proper and open arrows on strict towers; the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating, rather than introducing that definition again.

lem-sf-semilinear-alpha-pullback vs lem-cbc-proper-open-interchange-coherence: the new node proves the exact alpha-level pullback cube for arbitrary ring systems before proper mating; the existing statement concerns Proper/open interchange and its base-change and composition equations and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sfb-internal-module-operations-transport: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Internal and sectionwise module operations agree and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-module-abelian-hom-target-formula: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Abelian expansion of the scalar raw class and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-scalar-sheaf-composition: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Scalar forgetting commutes with inverse-image composition on sheaves and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-module-scalar-source-class-formula: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Scalar source and class coherence before coefficients and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-scalar-coefficient-square-shift-transport: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Shift transport for the coefficient square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-sbc-raw-module-scalar-source-prefix: the existing node defines Concrete common source prefix; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-scalar-derived-pullback-shift: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Derived scalar pullback comparison commutes with shifts and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-module-abelian-hom-map-naturality: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns The fixed raw scalar comparison intertwines pullback and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-sbc-raw-module-abelian-hom-map: the existing node defines The explicit scalar-forgetting map of raw derived Hom; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-scalar-coefficient-unshifted: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Unshifted coefficient-factor square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-module-abelian-hom-source-formula: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Module source and class factors after scalar forgetting and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-scalar-coefficient-square: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns The shifted coefficient factors of scalar forgetting commute with pullback and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-module-free-source-hom-bijective: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Explicit underived free-source comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-sbc-raw-module-scalar-pullback-comparison: the existing node defines Canonical scalar forgetting and inverse-image comparison; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sbc-raw-scalar-source-square: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns The source factors of scalar forgetting commute with pullback and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sf-finite-comparisons-existence: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Section preserving finite comparisons exist and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sf-finite-compatibility-transport: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Pinned finite comparisons preserve canonical open arrows and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sf-finite-operation-comparisons: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Prescribed finite realizations admit pinned operation comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-sf-open-normalization-data: the existing node defines Geometric and operation data for open tensor normalization; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs def-trf-space-etale-module-functors: the existing node defines Canonical etale module functors of algebraic spaces; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sfb-ringed-derived-two-iso-comparison: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Specified geometric 2-isomorphism comparison on derived modules and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sfb-ringed-derived-adjoint-lift: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Normalized ordinary and derived adjoint lifts of ringed-topos morphisms and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sfb-supplied-tensor-adjunction-normalization: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Scalar-extension adjunction with normalized underlying Hom bijection and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-ring-restriction-pullback-square: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Restriction respects the ordinary ringed pullback square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-weil-pbc-strict-local-module-sections-set-equiv: the existing node defines Canonical module/set equivalence of strict-local terminal sections; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-continuous-module-encoding-scalar-extension: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Scalar extension under the continuous integral and rational module encodings and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-inverse-image-composition-module-linear-core: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Existence of the module composition comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-etale-module-ring-iso-adjunction: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Transport a linearity criterion across a ring-sheaf isomorphism and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-derived-module-underlying-comparison: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Derived coefficient-forgetting comparisons respect restriction and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-weil-pbc-ringed-tensor-section-calculus: the existing node defines Section calculus for the actual sheaf tensor and scalar extension; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-geometric-module-transport: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Restriction of the underlying adjunction to linear maps and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-etale-module-pullback-forget-naturality: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Naturality of etale module pullback under forgetting coefficients and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lemma-weil-pbc-etale-pullback-forget-modules: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Étale pullback commutes with forgetting constant-ring module coefficients and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-etale-module-inverse-image-transport: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Transport of the module lift along a constant-ring comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-etale-mayer-vietoris-module-exact-segment: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Exact Mayer--Vietoris segment for module-sheaf pullbacks and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Tensor pullback adjoint to a supplied ringed-topos module direct image and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-ringed-ideal-quotient-comparison: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Quotient criterion for the scalar-extension unit of an ideal subsheaf and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-strict-local-module-sections-set-transport: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Representative compatibility of strict-local coefficient and symmetry transport and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-inverse-image-composition-module-linear: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns The composition isomorphisms of inverse and direct images are linear on sheaves of modules and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-ringed-topos-pullback-filtered-colimits: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns The specified ringed-topos module pullback preserves filtered colimits and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-etale-module-ring-iso-tensor: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Tensor comparison for an invertible change of ring sheaf and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-geometric-module-construction: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Module structures and functors transported by finite products and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-continuous-module-encoding-lattices: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Local freeness and lattice compatibility of the explicit continuous encodings and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-ringed-topoi-module-adjunction: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Module pullback and pushforward adjunction on arbitrary ringed topoi and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-algebraic-inverse-image-of-module-transport: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Recover algebraic inverse-image compatibility from module-operation transport and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-pbc-ringed-equivalence-module-hom: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Module and closed Hom transport under a ringed equivalence and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pur-coefficient-level-ordinary-images: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Ordinary geometric images at the constant quotient levels and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pur-ringed-coefficient-derived-presentation-exists: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Existence of a normalized derived coefficient presentation and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-fix-ordinary-restriction-pullback-square: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Ordinary restriction of scalars respects the inverse-image square compositor and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-sp-semilinear-constant-ring-operations: the existing node defines Constant-ring semilinear system operations and normalized evaluation mates; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pur-independent-module-adjunction: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Module adjunction for an independently sized algebraic inverse image and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-pur-cochain-coefficient-arrows: the existing node defines Canonical scalar-association and transition arrows on cochain sheaves; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sp-constant-pullback-scalar: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Module pullback transports scalar multiplication and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pur-sheaf-ring-coefficient-ordinary-adjunction: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Exact restriction and normalized ordinary scalar-extension adjunction on a general ringed site and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-pur-ringed-module-derived-operations: the existing node defines Canonical module and derived operations for an exact ringed-site pullback; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs def-pur-cochain-tensor-coherence-data: the existing node defines Canonical cochain ringed-pullback and coherence data; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-sp-constant-inverse-image-section: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Transported global sections and constant quotient kernels and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pur-ringed-coefficient-restriction-counit: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Derived ringed-topos counit under coefficient restriction and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pur-ringed-site-module-pullback-exists-universes: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Module pullback exists in a universe containing both sites and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pur-independent-ringed-tensorator-existence: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Existence of the tensorator for fixed scalar insertion at independent site sizes and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-weil-proetale-module-direct-image: the existing node defines Direct image of pro-etale module sheaves; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-weil-proetale-module-direct-image-left-exact: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Pro-etale direct image is left exact and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-pur-cochain-coefficient-universe-transport: the existing node defines Canonical common-universe transport of ring and module sheaves; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs def-pur-ringed-coefficient-change-presentations: the existing node defines Normalized coefficient changes between counit presentations; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pur-ringed-coefficient-change-normalization: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Normalized coefficient changes and their naturality and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-pur-ringed-coefficient-counit-presentations: the existing node defines Normalized ringed coefficient counit presentations; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pur-independent-composite-algebraic-image: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns Algebraic inverse image and coefficient map for a composite and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-pd-proetale-section-module-functors: the existing node defines Normalized tensor structures on existing pro-etale section-module functors; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-scalar-ordinary-comparison vs lem-pod-canonical-module-adjunction-unit: the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations; the existing statement concerns The canonical pro-etale module adjunction has its prescribed tensor unit and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-ordinary-comparison vs def-pd-section-module-operations-data: the existing node defines Existing section-module operations and pure-tensor data; the new node proves ordinary restriction from varying C_n-module systems to constant-B towers with transition, section, adjunction and alpha normalizations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs def-coef-semilinear-derived-calculus: the existing node defines Ordinary derived semilinear calculus interfaces; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs lem-sf-open-operation-models: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Open operation comparisons with fixed tensor models and right square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs def-sf-semilinear-proper-open-comparisons: the existing node defines Canonical semilinear proper/open compositors and intrinsic clopen comparison; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs def-sf-open-normalization-data: the existing node defines Geometric and operation data for open tensor normalization; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs lem-trf-topos-complement-module-stalks: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Module support, adjunctions and stalks for complementary subtopoi and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-pc-open-inverse-image-injectives: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Open inverse image preserves injective abelian sheaves and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-sc-module-extension-by-zero-unit-epi: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns The chosen open-extension adjunction unit is epic and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-pc-open-restriction-ext-bijective: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Bijectivity of the constructed open-restriction Ext maps and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-pc-open-extension-derived-unit-isiso: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns OpenExtensionDerivedUnitIsIso and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-sc-module-extension-by-zero-unit-isiso: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns The chosen open-extension adjunction unit is invertible and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-pc-scheme-module-free-yoneda-iso: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Free Yoneda sheaves agree with extension by zero of the localized unit and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-pc-open-restriction-data: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Degree-zero restriction data in the cartesian open-subscheme square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs new-open-embedding-sheaf-pullback-adjunction: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Extension by zero adjunction for open embeddings and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs new-open-embedding-sheaf-pullback-preserves-monomorphisms: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Open embedding sheaf pullback preserves monomorphisms and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-sc-module-extension-by-zero-unit-mono: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns The chosen open-extension adjunction unit is monic and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-pc-open-embedding-sheaf-pullback-injectives: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Open embedding sheaf pullback preserves injectives and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-pc-open-free-restriction-hom: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Restriction of morphisms from the image-open free sheaf and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-pc-inverse-image-open-free-sheaf: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Inverse image of a represented open free abelian sheaf and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-sfb-locally-closed-module-extension-coherence: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Normalized locally closed extension on module sheaves and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-sfb-proetale-locally-closed-extension: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Pointwise exact locally closed extension and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-sfb-open-filtration-successor: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Natural quotient for two nested open module pieces and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-sfb-proetale-identified-open-closed: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Exact open and closed extensions with identified inverse-image coefficients and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-sfb-proetale-identified-supported-reconstruction: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Normalized supported reconstruction for actual tensor pullbacks and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-sfb-locally-closed-extension-coherence: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Restriction and composition for locally closed extension by zero and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs def-a1-finite-adic-open-section-data: the existing node defines Finite adic open extension and fibre data; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-ringed-slice-extension-preserves-exact: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Ringed-slice extension preserves exactness and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-sheaf-free-separator: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns The coproduct of the sheafified free presheaves on representables with coefficients in a separator is a separator of the sheaf category and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-free-etale-module-shriek-comparison: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Free representable module sheaves are etale extensions by zero and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-proetale-ringed-open-closed: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Ringed pro-etale open-closed localization and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-affine-free-finite-stalk-generation: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Finite affine free maps generating one module stalk and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-etale-graph-section-extension-map-linear: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns The presheaf map from the etale sum presheaf to direct image is linear over the constant sheaf of rings and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-free-yoneda-presheaf-module: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Morphisms out of the free presheaf of modules on a representable are sections and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-zariski-extension-by-zero-adjunction: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Extension by zero of abelian Zariski sheaves is a left adjoint of restriction to an open and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs def-weil-pbc-local-coefficient-localization: the existing node defines Coefficient localization and local section multiplication on a ringed site; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-free-sheaf-derived-sections: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Free sheaf shifted Hom computes derived module global sections and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-extension-by-zero-adjunction: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Extension by zero is left adjoint to restriction (étale site) and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs def-weil-pbc-extension-by-zero: the existing node defines Extension by zero for open immersions; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-free-sheaf-flat: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns The sheafified free presheaf on a representable with flat coefficients is flat (j_{X!} of a constant flat sheaf is flat) and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs def-weil-extension-by-zero-presheaf: the existing node defines The extension-by-zero presheaf of a module on a localized ringed site; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs def-sp-semilinear-constant-ring-operations: the existing node defines Constant-ring semilinear system operations and normalized evaluation mates; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs lem-cbc-open-extension-zero-etale-adjunction-agreement: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Open-immersion and etale extension by zero have the same adjunction and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-cbc-localized-extension-zero-linear-derived: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Module extension by zero is linear on the unbounded derived category and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs def-sp-varying-ring-proper-open-arrows: the existing node defines Intrinsic varying-ring clopen proper/open arrows; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs def-sp-varying-ring-operations: the existing node defines Canonical geometric operations on varying-ring systems; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs new-localized-restriction-extension-exists-universes: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Exact extension adjoint for localized restriction with independent coefficient universe and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-cbc-finite-open-exchange-scalars: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Finite open exchange commutes with coefficient restriction and tower transitions and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs new-lem-amb-closed-support-hom-sequence: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Underived closed-support Hom sequence on injective sheaves and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-cbc-extension-zero-stratified-perfect: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Extension by zero preserves stratified perfect local models and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs def-pd-proetale-section-module-functors: the existing node defines Normalized tensor structures on existing pro-etale section-module functors; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs def-pd-section-module-operations-data: the existing node defines Existing section-module operations and pure-tensor data; the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations, rather than introducing that definition again.

lem-sf-semilinear-clopen-unit-projector vs new-over-pullback-preserves-injectives: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Restriction to a slice Grothendieck site preserves injective abelian sheaves and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-site-restriction-injectives: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Extension by zero and restriction on a localized site and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs lem-weil-pbc-site-extension-by-zero-presheaf-adjoint: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns The sheafified direct-sum presheaf is left adjoint to restriction to a localized site and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs new-over-pullback-adjunction-mono: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Extension by zero adjunction preserving monomorphisms and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-clopen-unit-projector vs new-lem-sc-nested-slice-extension-stalks: the new node proves the arbitrary-ring-system clopen adjoint-triple isomorphism and its unit/projector and complement equations; the existing statement concerns Nested slice extension stalk maps and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sbc-pullback-comparison-comp: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Composition of coefficient pullback and single-complex comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sf-scalar-pullback-composition: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Composition coherence of normalized scalar/pullback comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-sf-semilinear-proper-open-comparisons: the existing node defines Canonical semilinear proper/open compositors and intrinsic clopen comparison; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs def-zl-pbc-finite-raw-scalar-comparison: the existing node defines Canonical comparison of normalized and embedding finite-field scalar extension; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-trf-derived-pullback-coherence: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Associativity of finite pro-etale derived pullback comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-trf-integral-comparison-realization-models: the existing node defines Normalized realization interfaces for integral quotient systems; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-trf-pullback-coefficient-iterate-coherence: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Canonical pullback comparisons intertwine coefficient-map iterates and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-trf-integral-comparison-sequence-systems: the existing node defines Canonical pullback and scalar change of whole quotient systems; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-trf-integral-pullback-comparison-realization: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Strict-system realization and composition coherence of integral pullback comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-scalar-tensor-tower-comparison: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Simultaneous normalized scalar tensor comparisons with coefficient coherence and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-sfb-scalar-hom-comparison-data: the existing node defines Actual scalar-adjunction and normalized tensor-Hom comparison data; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-sfb-closed-scalar-hom-transport: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Transport of closed-Hom comparison along adjoint isomorphisms and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-ringed-comparison-tensor-adjunction: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Tensor and adjunction compatibility of canonical ringed-topos path comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-constant-realization-derived-scalar-extension: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Derived constant realization commutes with derived scalar extension and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-sfb-ringed-projection-coherence-data: the existing node defines Recorded data for tensor projection coherence; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs def-sfb-proetale-projection-exchange-maps: the existing node defines Canonical projection and exchange maps on internal pro-etale modules; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-sfb-scalar-internal-hom-tower-coherence: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Coefficient-tower and identity coherence for normalized internal Hom and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-sfb-ringed-derived-comparison-data: the existing node defines Data of normalized derived monoidal comparisons of ringed topoi; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-sfb-closed-scalar-hom-composition: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Composition of the five closed-Hom bijections and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-successive-derived-quotient-normalization: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Successive derived scalar extensions agree with direct quotient extension and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-ringed-projection-tensor-structure: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Canonical tensor structure in arbitrary recorded presentations and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-ringed-derived-composition-comparison: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Composition comparison with normalized representative formulas and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-ringed-projection-pullback-comparisons: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Normalized identity, composition and section pullback comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-ringed-projection-tensor-compatibility: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Tensor constraints and compatibility of normalized comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-scalar-hom-tensor-coherence: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Tensor coherence of the normalized scalar extension maps and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-ringed-derived-identity-comparison: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Identity comparison with normalized representative formulas and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sfb-ringed-derived-monoidal-comparisons: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Monoidal and adjunction normalization of derived ringed-topos comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-a1-proper-sections-germ-and-moving-point: the existing node defines Canonical proper compact rational germs and semilinear moving points; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs def-per-derived-hom-pullback: the existing node defines Canonical pullback on shifted etale derived Hom; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-completed-reduction-pullback-square: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Completed reduction respects the strict inverse-image square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-ringed-square-tensor-compatibility: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Tensor compatibility of a ringed square on flat K-flat representatives and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-derived-square-iso-pasting: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Identity and pasting laws of the derived square isomorphism and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-derived-inverse-image-composition: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Composition isomorphisms of derived inverse images and their coherence and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing result compares two ring sheaves on each scheme site at one coefficient level; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, including the simultaneous tower assertions.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-ringed-square-localization: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Ambient ringed square is exact localization of its ordinary square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-weil-pbc-derived-direct-image-composition: the existing node defines Composition isomorphisms of derived direct images (conjugates of those of inverse images); the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-finite-reduction-pullback-coherence: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Finite reduction and the canonical pullback square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-finite-reduction-pullback-square: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Finite reduction respects the inverse-image square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-weil-pbc-derived-square-iso: the existing node defines Square isomorphism on bounded below derived categories; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-frobenius-exchange-restriction: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Finite-level exchange is the restricted ambient exchange and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-proetale-derived-pullback-composition: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Composition of derived pro-etale module pullbacks and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-weil-pbc-ringed-tensor-square-presentation: the existing node defines Representative presentation of a commutative ringed tensor square; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs def-weil-pbc-strict-tower-operations: the existing node defines Specified derived operations and mate on strict pro-etale module towers; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-weil-pbc-derived-scalar-extension-local-systems: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Coherent localized derived scalar extension and comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pur-coefficient-pullback-coherence: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Balanced coherence of canonical coefficient pullback comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pur-module-tensor-composition-equation: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Ordinary tensor square for composite module pullback and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sp-canonical-derived-pullback-normalization: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Canonical derived composition is localized normalized ordinary composition and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-pur-cochain-coefficient-arrows: the existing node defines Canonical scalar-association and transition arrows on cochain sheaves; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-cbc-strict-tower-direct-image-coherence: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Coherence of canonical strict-tower direct image and its square mates and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-pur-ringed-coefficient-projection-data: the existing node defines Normalized coefficient projection interfaces; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs def-pur-cochain-tensor-coherence-data: the existing node defines Canonical cochain ringed-pullback and coherence data; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-sp-constant-scalar-pullback-cube: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns The canonical constant-ring scalar and geometric pullback cube and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pur-coefficient-pullback-shifts: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Shift compatibility of normalized inverse-image coefficient comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-sp-constant-scalar-pullback-comparison: the existing node defines Canonical constant-coefficient scalar extension, direct image and pullback comparison; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-pur-cochain-comparison-monoidal-equations: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Monoidal equations for the canonical cochain pullback comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pur-independent-normalized-scalar-composition: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Normalized composition of module scalar extensions and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs def-pur-cochain-coefficient-universe-transport: the existing node defines Canonical common-universe transport of ring and module sheaves; the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences, rather than introducing that definition again.

lem-sf-semilinear-compositor-coherence vs lem-sp-finite-free-direct-image-shift: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Shift compatibility of the actual coefficient/direct-image mate and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pur-coefficient-scalar-units: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Multiplication units for derived scalar extension and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pur-coefficient-associator-shifts: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Shift compatibility of balanced derived scalar associators and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pur-module-tensor-coefficient-equations: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Ordinary module tensor equations for coefficient change and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sp-scalar-tensor-pullback-square: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Scalar tensor comparisons respect arbitrary pullback squares and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-sp-finite-free-balancing-coherence: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Scalar units and associators commute with the canonical balanced pullback comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pur-independent-composite-algebraic-image: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Algebraic inverse image and coefficient map for a composite and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pur-coefficient-pullback-comparison: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Canonical inverse-image coefficient comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pod-integral-pullback-composition: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Composition isomorphism for integral derived pullbacks and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pod-constant-comparison-module-localization: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Canonical finite-coefficient derived composition is ordinary module composition localized and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-compositor-coherence vs lem-pod-finite-system-pullback-coherence: the new node proves section-normalized associativity and units of all three compositors for arbitrary inverse ring sequences; the existing statement concerns Coherent composition of finite-coefficient pullback on strict systems and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-sbc-derived-localization-comparison-data: the existing node defines Canonical derived étale-localization comparisons; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-sbc-restrict-scalars-pullback-square-comparison: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Canonical coefficient comparisons preserve inverse-image square transport and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-sbc-base-change-restrict-scalars-arrow: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Étale base-change arrows commute with restriction of coefficients and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-sbc-restrict-scalars-derived-adjunction-identities: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Canonical coefficient comparisons preserve the derived adjunction and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-sbc-restrict-scalars-derived-exchange: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Canonical coefficient comparisons commute with derived exchange and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-sbc-base-change-restrict-scalars-comparison: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Coefficient comparison isomorphisms for the base-change source and target and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-coef-semilinear-proper-open-mate: the existing node defines Canonical semilinear proper/open adjunction mate; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-coef-cartesian-section-adjoint-mates: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Adjoint mates on cartesian derived sections and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-sf-semilinear-proper-open-comparisons: the existing node defines Canonical semilinear proper/open compositors and intrinsic clopen comparison; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-trf-bounded-below-derived-mate-model: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Bounded-below derived mates are computed by underived mates and comparison units and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-trf-topos-derived-base-change-map: the existing node defines Derived base-change map for a commutative square of ringed topoi; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs def-pc-derived-base-change-map: the existing node defines Canonical derived base-change morphism; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs def-sfb-proetale-projection-exchange-maps: the existing node defines Canonical projection and exchange maps on internal pro-etale modules; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-sfb-ringed-kunneth-factorizations: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Two factorizations of the ringed-topos external product comparison and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-a1-lisse-section-evaluation: the existing node defines Canonical evaluation of ordinary common-stage sections at a geometric point; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs def-a1-proper-sections-germ-and-moving-point: the existing node defines Canonical proper compact rational germs and semilinear moving points; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs def-weil-pbc-adjunction-mate: the existing node defines Mate of a transformation under two adjunctions; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-exchange-mate-cube: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Naturality of the adjunction mate across a cube and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-derived-exchange-module-termwise: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns K-injective representative of the module derived exchange mate and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-strict-tower-exchange-mate-normalization: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Strict tower exchange agrees with the canonical mate and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-weil-pbc-four-arrows: the existing node defines Four finite-level arrows; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs prop-weil-pbc-derived-inverse-image-adjunction: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Derived adjunction of inverse and direct image on D^+ and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-module-abelian-underived-exchange: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Coefficient forgetting respects underived exchange and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-finite-level-rectangle: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Finite-level exchange rectangle and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-module-abelian-stalk-exchange: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Forgetting module coefficients in the stalk of derived exchange and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-exchange-forget-coefficients: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns The derived exchange morphism commutes with forgetting the coefficient ring and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-weil-pbc-derived-square-iso: the existing node defines Square isomorphism on bounded below derived categories; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-derived-exchange-unbounded-transport: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Transport of the exchange equation to arbitrary K-injective representatives and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-frobenius-exchange-restriction: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Finite-level exchange is the restricted ambient exchange and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-module-abelian-derived-exchange-compatibility: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Canonical coefficient comparisons intertwine derived exchange and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-etale-underived-exchange-restriction: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Underived exchange along an etale morphism is the restriction identification and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-derived-exchange-bounded-comparison: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns The bounded below exchange comparison equation and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-weil-pbc-strict-tower-operations: the existing node defines Specified derived operations and mate on strict pro-etale module towers; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Finite exchange rectangle for intrinsic coefficient reduction and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-pur-ringed-coefficient-projection-cocycle: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Coefficient projection cocycle for ordinary derived ringed diagrams and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-pur-scalar-pullback-representative-data: the existing node defines Canonical scalar/pullback representative data; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-cbc-strict-tower-pullback-square-pasting: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Pasting of normalized strict-tower inverse-image squares and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-kun-commutative-exchange-evaluation-compatibility: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Raw class evaluation commutes with geometric chart pullback and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-kun-commutative-exchange-raw-pullback: the existing node defines Canonical transport of represented raw classes through a commutative square; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-cbc-strict-tower-direct-image-coherence: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Coherence of canonical strict-tower direct image and its square mates and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-pur-ringed-coefficient-projection-data: the existing node defines Normalized coefficient projection interfaces; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-cbc-strict-tower-gamma-single-evaluation: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Evaluation of the intrinsic proper mate and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-pur-etale-scalar-pullback-existence: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Existence of normalized derived scalar/pullback comparison and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-cbc-finite-constant-coefficient-transport: the existing node defines Normalized finite scalar and etale-origin transport to constant coefficient modules; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs def-pur-etale-scalar-pullback-iso: the existing node defines Canonical derived scalar and pullback isomorphism; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-kun-derived-exchange-cube: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Derived exchange commutes around a commutative cube and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-pur-scalar-tensor-pullback-normalization: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Scalar/tensor pullback normalization on a K-flat representative and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-kun-commutative-derived-exchange: the existing node defines Derived exchange for an arbitrary commutative square of schemes; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-sp-proper-open-comparison-normalization: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Structural normalization of explicit proper/open comparison and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-kun-commutative-exchange-class-compatibility: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns The exchange mate transports higher-image raw classes and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-pur-etale-scalar-pullback-uniqueness: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Uniqueness of normalized derived scalar/pullback comparison and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-cbc-strict-tower-open-extension: the existing node defines Normalized exact open extension on strict constant-coefficient towers; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-cbc-strict-tower-proper-open-calculus: the existing calculus has one constant B at every tower level; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit with arbitrary varying C_n.

lem-sf-adjunct-conjugate-open-factor vs lem-exc-support-scalar-projection-normalization: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Normalization of support scalar mate as a projection arrow and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs lem-kun-unbounded-abelian-exchange-comparison: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Unbounded coefficient forgetting identifies canonical etale exchange and does not assert this normalized varying-system/five-category result.

lem-sf-adjunct-conjugate-open-factor vs def-cbc-strict-constant-tower-operations: the existing node defines Strict constant-coefficient towers and normalized inverse/direct-image operations; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs def-cbc-strict-tower-proper-open-arrows: the existing node defines Unit-normalized proper and open arrows on strict towers; the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit, rather than introducing that definition again.

lem-sf-adjunct-conjugate-open-factor vs lem-pod-frobenius-exchange-degree-zero: the new node proves a generic five-category conjugate-Hom transport with cancellation of an invertible open unit; the existing statement concerns Degree-zero Frobenius exchange is the underived section-pullback mate and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sfb-internal-module-operations-transport: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Internal and sectionwise module operations agree and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-module-abelian-hom-target-formula: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Abelian expansion of the scalar raw class and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-scalar-sheaf-composition: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Scalar forgetting commutes with inverse-image composition on sheaves and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-module-scalar-source-class-formula: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Scalar source and class coherence before coefficients and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-scalar-coefficient-square-shift-transport: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Shift transport for the coefficient square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-sbc-raw-module-scalar-source-prefix: the existing node defines Concrete common source prefix; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-scalar-derived-pullback-shift: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Derived scalar pullback comparison commutes with shifts and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-module-abelian-hom-map-naturality: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns The fixed raw scalar comparison intertwines pullback and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-sbc-raw-module-abelian-hom-map: the existing node defines The explicit scalar-forgetting map of raw derived Hom; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-scalar-coefficient-unshifted: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Unshifted coefficient-factor square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-module-abelian-hom-source-formula: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Module source and class factors after scalar forgetting and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-scalar-coefficient-square: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns The shifted coefficient factors of scalar forgetting commute with pullback and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-module-free-source-hom-bijective: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Explicit underived free-source comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-sbc-raw-module-scalar-pullback-comparison: the existing node defines Canonical scalar forgetting and inverse-image comparison; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-sbc-raw-scalar-source-square: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns The source factors of scalar forgetting commute with pullback and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sf-finite-comparisons-existence: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Section preserving finite comparisons exist and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sf-finite-compatibility-transport: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Pinned finite comparisons preserve canonical open arrows and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sf-finite-operation-comparisons: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Prescribed finite realizations admit pinned operation comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-sf-open-normalization-data: the existing node defines Geometric and operation data for open tensor normalization; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs def-trf-space-etale-module-functors: the existing node defines Canonical etale module functors of algebraic spaces; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-sfb-ringed-derived-two-iso-comparison: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Specified geometric 2-isomorphism comparison on derived modules and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sfb-ringed-derived-adjoint-lift: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Normalized ordinary and derived adjoint lifts of ringed-topos morphisms and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-sfb-supplied-tensor-adjunction-normalization: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Scalar-extension adjunction with normalized underlying Hom bijection and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-ring-restriction-pullback-square: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Restriction respects the ordinary ringed pullback square and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-weil-pbc-strict-local-module-sections-set-equiv: the existing node defines Canonical module/set equivalence of strict-local terminal sections; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-continuous-module-encoding-scalar-extension: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Scalar extension under the continuous integral and rational module encodings and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-inverse-image-composition-module-linear-core: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Existence of the module composition comparisons and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-etale-module-ring-iso-adjunction: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Transport a linearity criterion across a ring-sheaf isomorphism and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-derived-module-underlying-comparison: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Derived coefficient-forgetting comparisons respect restriction and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-weil-pbc-ringed-tensor-section-calculus: the existing node defines Section calculus for the actual sheaf tensor and scalar extension; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-geometric-module-transport: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Restriction of the underlying adjunction to linear maps and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-etale-module-pullback-forget-naturality: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Naturality of etale module pullback under forgetting coefficients and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lemma-weil-pbc-etale-pullback-forget-modules: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Étale pullback commutes with forgetting constant-ring module coefficients and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-etale-module-inverse-image-transport: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Transport of the module lift along a constant-ring comparison and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-etale-mayer-vietoris-module-exact-segment: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Exact Mayer--Vietoris segment for module-sheaf pullbacks and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Tensor pullback adjoint to a supplied ringed-topos module direct image and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-ringed-ideal-quotient-comparison: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Quotient criterion for the scalar-extension unit of an ideal subsheaf and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-strict-local-module-sections-set-transport: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Representative compatibility of strict-local coefficient and symmetry transport and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-inverse-image-composition-module-linear: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns The composition isomorphisms of inverse and direct images are linear on sheaves of modules and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-ringed-topos-pullback-filtered-colimits: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns The specified ringed-topos module pullback preserves filtered colimits and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-etale-module-ring-iso-tensor: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Tensor comparison for an invertible change of ring sheaf and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-geometric-module-construction: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Module structures and functors transported by finite products and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-continuous-module-encoding-lattices: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Local freeness and lattice compatibility of the explicit continuous encodings and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-ringed-topoi-module-adjunction: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Module pullback and pushforward adjunction on arbitrary ringed topoi and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-algebraic-inverse-image-of-module-transport: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Recover algebraic inverse-image compatibility from module-operation transport and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-pbc-ringed-equivalence-module-hom: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Module and closed Hom transport under a ringed equivalence and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-pur-coefficient-level-ordinary-images: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Ordinary geometric images at the constant quotient levels and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-pur-ringed-coefficient-derived-presentation-exists: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Existence of a normalized derived coefficient presentation and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-fix-ordinary-restriction-pullback-square: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Ordinary restriction of scalars respects the inverse-image square compositor and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-sp-semilinear-constant-ring-operations: the existing node defines Constant-ring semilinear system operations and normalized evaluation mates; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-pur-independent-module-adjunction: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Module adjunction for an independently sized algebraic inverse image and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-pur-cochain-coefficient-arrows: the existing node defines Canonical scalar-association and transition arrows on cochain sheaves; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-sp-constant-pullback-scalar: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Module pullback transports scalar multiplication and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-pur-sheaf-ring-coefficient-ordinary-adjunction: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Exact restriction and normalized ordinary scalar-extension adjunction on a general ringed site and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-pur-ringed-module-derived-operations: the existing node defines Canonical module and derived operations for an exact ringed-site pullback; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs def-pur-cochain-tensor-coherence-data: the existing node defines Canonical cochain ringed-pullback and coherence data; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-sp-constant-inverse-image-section: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Transported global sections and constant quotient kernels and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-pur-ringed-coefficient-restriction-counit: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Derived ringed-topos counit under coefficient restriction and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-pur-ringed-site-module-pullback-exists-universes: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Module pullback exists in a universe containing both sites and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs lem-pur-independent-ringed-tensorator-existence: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Existence of the tensorator for fixed scalar insertion at independent site sizes and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-weil-proetale-module-direct-image: the existing node defines Direct image of pro-etale module sheaves; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-weil-proetale-module-direct-image-left-exact: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Pro-etale direct image is left exact and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-pur-cochain-coefficient-universe-transport: the existing node defines Canonical common-universe transport of ring and module sheaves; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs def-pur-ringed-coefficient-change-presentations: the existing node defines Normalized coefficient changes between counit presentations; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-pur-ringed-coefficient-change-normalization: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Normalized coefficient changes and their naturality and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-pur-ringed-coefficient-counit-presentations: the existing node defines Normalized ringed coefficient counit presentations; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-pur-independent-composite-algebraic-image: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns Algebraic inverse image and coefficient map for a composite and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-pd-proetale-section-module-functors: the existing node defines Normalized tensor structures on existing pro-etale section-module functors; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.

lem-sf-semilinear-scalar-derived-comparison vs lem-pod-canonical-module-adjunction-unit: the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha; the existing statement concerns The canonical pro-etale module adjunction has its prescribed tensor unit and does not assert this normalized varying-system/five-category result.

lem-sf-semilinear-scalar-derived-comparison vs def-pd-section-module-operations-data: the existing node defines Existing section-module operations and pure-tensor data; the new node proves localization of that varying-to-constant tower comparison, its specified invertible derived direct-image mate and preserved alpha, rather than introducing that definition again.


## Previous dry-run rejection (resolved by this repair)

The initial dry run exited 1 because the dispatched sandbox held no node files. After copying and refining the live item, the final dry run was run once to completion:

`python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q49 lem-sf-semilinear-proper-open-mate-pasting --no-push`

It exited 1 after server preflight, with six failures, one for every new supporting node:

`new node <id>: status 'split'; a new node is unsplit or mathlib`

The previous attempt interpreted the original repair wording as requiring proof-bearing child nodes. The current route note explicitly requires statement-only new nodes instead. I repaired all six nodes to status unsplit, empty proof and proof_deps, null proof_origin, and no split_report. The rejected proof words are preserved below as report material. No tool was edited or bypassed. The parent statement and all original search logs and citations are retained.

## Repair review on 2026-10-21

I compared every item field with the current read-only live node: only proof, proof_deps, proof_origin and split_report differ; the statement and Lean/review metadata are identical. I reran the required initial dry run to completion; it confirmed exactly the six status-format failures. This repair follows the later route note rather than repeating the earlier blocked delivery.

I read the six statements, their logged Mathlib search results, the chapter and unit route, the blueprint ancestor proof, Stacks 0F7B/0F7C/0F7D/0F7F, 03D7, 03DI, 07A7 and 0D6D, and the live Lean adjunct_transport and compositor declarations without compiling. No exact completed declaration in WeilConjectures states the item. Existing Sheaf declarations do not qualify as an attachment here, and the aggregate mate-pasting statement still has sorry.

I declare lem-sp-varying-ring-proper-open-pasting as an off-unit generic tool in split_report.tool_uses: it supplies the underlying system construction, binary pasting, identities and evaluation, rather than a replacement route. The parent proves its additional adjunct, base-change and scalar-normalization claims using the new smaller nodes. All six new statements introduce their data, keep arbitrary coefficients, and are strictly smaller intermediate assertions rather than the Gamma clauses of the parent. The generic transport lemma has no geometric hypotheses; its invertible open-unit assumption is explicit. The alpha lemma is before proper mating; the scalar lemmas concern ordinary construction and invertibility of the derived comparison before Gamma; the clopen lemma computes a specified unit, and compositor coherence concerns the functor structure independently of Gamma.



## Retained supporting arguments (not node proofs)

The previous attempt supplied the following arguments. They are preserved here for future stage-1 workers; the six new DAG nodes are statement-only and unsplit, as the current route note requires. These sketches are not delivered as completed child splits.
### lem-sf-adjunct-conjugate-open-factor

Source: literature/stacks-project/sites-cohomology.tex, Tag 07A7 (remark-base-change), abstract mate normalization; agent-written categorical transport argument matching adjunct_transport in Sheaf.SixFunctors.SemilinearProperOpenMatePasting
1. For two adjunctions $a:L\dashv R$, $a':L'\dashv R'$ and $e:L\cong L'$, conjugation and the unit equation give $c_Y\circ\operatorname{adj}_a(v)=\operatorname{adj}_{a'}(v\circ e_X^{-1})$. Indeed expand the first adjunct as $R(v)\eta_X$, move $c$ across $R(v)$ by naturality, and substitute the unit equation. Apply this with the composite adjunctions $J_i\dashv P_i$ then $L_p\dashv R_p$, and $L_q\dashv R_q$ then $J_b\dashv P_b$. The mate definition identifies the first composite adjunct of $\alpha_{R_rM}$ followed by $J_k\varepsilon_r$ with the $J_i$-adjunct of $\gamma_M$. The assumed equation therefore changes its conjugate to the composite adjunct of $d_M\circ J_b(f)$.

   Uses: lem-weil-pbc-conjugate-iso-unit-equation, def-weil-pbc-composite-adjunction, def-weil-pbc-adjunction-mate
2. The inner $J_b$-adjunct of $d_M\circ J_b(f)$ is $P_b(d_M\circ J_b(f))\circ u_{b,L_qR_rM}$. Postcompose with $z_M$. Cancel $P_b(d_M^{-1})P_b(d_M)$ and use naturality $P_bJ_b(f)\circ u_{b,L_qR_rM}=u_{b,J_sM}\circ f$. Cancellation of the invertible $u_{b,J_sM}$ leaves $f$. Naturality of the $L_q\dashv R_q$ Hom bijection moves this postcomposition outside it as $R_q(z_M)$, giving exactly the displayed equation.

   Uses: def-weil-pbc-composite-adjunction, def-weil-pbc-adjunction-mate
Prior proof origin: {"by": "agent", "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md", "place": "Sentence on adjunction units and counits; explicit extraction from lem-sf-semilinear-proper-open-mate-pasting; Tag 07A7 (remark-base-change), abstract mate normalization; agent-written categorical transport argument matching adjunct_transport in Sheaf.SixFunctors.SemilinearProperOpenMatePasting"}
### lem-sf-semilinear-alpha-pullback

Source: literature/stacks-project/more-etale.tex, Tag 0F7F (lemma-shriek-proper-and-open-base-change), alpha-level open case; agent-written extension to arbitrary strict semilinear systems
1. First compare the open $\beta$ factors under successive pullbacks. Take their inverse open-adjunction transposes, using the explicit transpose of the open unit. After the specified pullback compositors, both transposes are the same inverse image of that unit. The Hom bijection is injective, so the two composites agree. The same argument, now using two open adjunctions, compares open composition. Compositor coherence supplies the rebracketing in these transposes. This establishes the cube for the cartesian open part of $\alpha$.

   Uses: lem-sf-open-tensor-normalization, lem-sf-semilinear-compositor-coherence, lem-weil-pbc-mate-pasting
2. Put $L=V\times_ZW$ and $L_1=V_1\times_{Z_1}W_1$. Fibre-product universality identifies $L_1$ with the pullback of $L$ and identifies $s_1=(k_1,r_1)$ with the pullback of $s=(k,r)$. The selected component and its complementary open both pull back. By the clopen unit-projector formula, ordinary sections of the projector are $(x,y)\mapsto(x,0)$. Inverse image preserves this finite split diagram, so the pulled-back projector is exactly the selected-component projector for $s_1$, including all coefficient transitions. This is an equality of ordinary sheaf-system maps, not an inference from derived evaluations.

   Uses: def-pc-fibre-product, lem-sp-varying-ring-proper-open-pasting, lem-sf-semilinear-clopen-unit-projector
3. Expand each $\alpha$ as cartesian $\beta$, then the extended clopen projector, then the open and inverse-image compositors. Substitute the equalities of the first two steps. The remaining factors are exactly the same composition comparisons, by coherence, giving the two words in the statement. Exact inverse image and open extension let us perform this calculation on complexes; uniqueness in localization preserves the equality on the whole system derived categories.

   Uses: lem-sf-semilinear-compositor-coherence, def-sp-varying-ring-proper-open-arrows, lem-weil-pbc-localization-universal-property
Prior proof origin: {"by": "agent", "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md", "place": "Sentence on adjunction units and counits; explicit extraction from lem-sf-semilinear-proper-open-mate-pasting; Tag 0F7F (lemma-shriek-proper-and-open-base-change), alpha-level open case; agent-written extension to arbitrary strict semilinear systems"}
### lem-sf-semilinear-clopen-unit-projector

Source: literature/stacks-project/sites-modules.tex, Tag 03DI (lemma-extension-by-zero), specialized to a disjoint clopen decomposition on the ringed sequence site; agent-written extension to arbitrary coefficient systems
1. For a pro-etale test object $H\to X$, its inverse images of $s(U)$ and the complementary open form a disjoint covering. The sheaf equalizer condition gives $M_n(H)=M_n(H_U)\times M_n(H_C)$: the intersection is empty, whose module of sections is zero. Restrictions and coefficient transitions preserve these two factors. Gluing pairs of sheaves conversely constructs a system on $X$, so restriction is an exact equivalence of system categories with the product of the two component categories. Under this equivalence $P_s$ is first projection and both ordinary extension and direct image are insertion $N\mapsto(N,0)$.

   Uses: def-sp-varying-ring-operations, lem-coef-semilinear-derived-sections
2. Apply these formulas degree by degree. The insertion functor is exact, so its ordinary action already represents its total right derived functor; the simultaneous section models retain the induced adjunctions. In product coordinates both the open unit and its transpose $t_s$ are identities on the first factor, whereas $\eta_s$ sends $(x,y)$ to $(x,0)$. Thus $t_s$ is an isomorphism and the specified projector has the asserted unit formula. Restricting to either factor gives respectively identity and zero. These are calculations of actual system transformations before localization and retain their equalities afterwards.

   Uses: lem-coef-semilinear-derived-sections, def-sp-varying-ring-proper-open-arrows, lem-weil-pbc-exact-functor-derived-factorization
Prior proof origin: {"by": "agent", "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md", "place": "Sentence on adjunction units and counits; explicit extraction from lem-sf-semilinear-proper-open-mate-pasting; Tag 03DI (lemma-extension-by-zero), specialized to a disjoint clopen decomposition on the ringed sequence site; agent-written extension to arbitrary coefficient systems"}
### lem-sf-semilinear-compositor-coherence

Source: literature/stacks-project/sites-cohomology.tex, Tag 0D6D (lemma-derived-pullback-composition); agent-written section-normalized coherence for the ringed sequence sites
1. By the section normalization of ordinary direct-image composition, both composites for three scheme maps act at $(n,H)$ by restriction along the canonical isomorphism from the same iterated fibre product to $H\times X$. Both fibre-product maps have the same projection to every factor, so the universal property makes them equal. Presheaf functoriality gives equality on sections, hence equality of ordinary system transformations. The identity case uses the map $H\times_X X\cong H$ in the same calculation. The ring structural maps are the canonical constant-section maps and agree on both routes.

   Uses: def-sp-varying-ring-operations, def-pc-fibre-product
2. Pass to the unit-preserving left-adjoint comparisons using conjugation. Their two composites correspond to the equal right-adjoint composites from the preceding step: mate pasting, applied successively, preserves those compositions and their identity comparisons. This proves the ordinary inverse-image equation. These inverse images are exact, so apply them termwise to complexes and descend their transformations by the localization universal property, which preserves identities and composition. Thus the $d$ equation holds on the ordinary unbounded derived categories, with their specified localization comparisons.

   Uses: lem-weil-pbc-mate-pasting, lem-weil-pbc-localization-universal-property, lem-coef-semilinear-derived-sections
3. Conjugate this $d$ equation under the specified derived adjunctions. The two mate-pasting laws identify the conjugates with the two $c$ words, so their equality gives the direct-image equation. Conjugating the same inverse-image equation under $J_a\dashv P_a$ gives the $e$ equation. The identity equations follow from the identity mate. For an equality of scheme arrows, equality elimination reduces the assertion to the equation already proved; no adjunction is replaced by a newly chosen one.

   Uses: lem-weil-pbc-mate-pasting, def-sp-varying-ring-operations
Prior proof origin: {"by": "agent", "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md", "place": "Sentence on adjunction units and counits; explicit extraction from lem-sf-semilinear-proper-open-mate-pasting; Tag 0D6D (lemma-derived-pullback-composition); agent-written section-normalized coherence for the ringed sequence sites"}
### lem-sf-semilinear-scalar-derived-comparison

Source: literature/stacks-project/sites-modules.tex, Tag 03D7 (lemma-adjoint-pullback-pushforward-modules), derived ring-change adjunction with the simultaneous-section comparison; agent-written system assembly
1. The ordinary restriction, inverse image and open extension in the preceding node are exact additive functors. Localize them and their isomorphisms termwise on complexes. The localization universal property preserves their composition and unit equations, so yields the stated $b_f,a_j$. The unit equation characterizes the open transpose uniquely; consequently $a_j^{-1}$ is exactly the left open mate of $b_j$, rather than an independently chosen isomorphism. The ordinary equality for $\alpha_Q$ similarly descends to the asserted equality of derived system transformations.

   Uses: lem-sf-semilinear-scalar-ordinary-comparison, lem-weil-pbc-localization-universal-property, lem-sfb-adjunction-localization
2. Define $d_f$ by its mate word. Evaluation commutes with the simultaneous system adjunctions and their unit/counit words. Its $n$-th evaluation is therefore the mate of the level inverse-image comparison $b$. In the ring-sheaf change adjunct clause put $t=\varepsilon_f$, whose adjunct is the identity: it identifies that mate with the canonical level direct-image isomorphism $d$. Thus each evaluated $d_f$ is invertible. Evaluation of constant-$B$ towers jointly detects isomorphisms (apply the simultaneous-section theorem to the constant ring sequence), so $d_f$ itself is invertible. Detection is used only for this isomorphism claim; equality of alpha maps was proved before evaluation in the first step.

   Uses: lem-coef-semilinear-derived-sections, lem-weil-pbc-ring-sheaf-change-adjunction
Prior proof origin: {"by": "agent", "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md", "place": "Sentence on adjunction units and counits; explicit extraction from lem-sf-semilinear-proper-open-mate-pasting; Tag 03D7 (lemma-adjoint-pullback-pushforward-modules), derived ring-change adjunction with the simultaneous-section comparison; agent-written system assembly"}
### lem-sf-semilinear-scalar-ordinary-comparison

Source: literature/stacks-project/sites-modules.tex, Tag 03D7 (lemma-adjoint-pullback-pushforward-modules); agent-written assembly for varying rings, compatible constant-B actions and localized opens
1. Restrict each module action along $\phi_n$ and retain the underlying section maps. Compatibility $\tau_n\phi_{n+1}=\phi_n$ makes every transition $B$-linear. Naturality and the functor laws are those of the original maps; all sections and transitions specify the functor uniquely. Componentwise exactness of systems and ordinary scalar restriction gives exactness and additivity. Both direct-image composites at $(n,H)$ are the module $M_n(H\times_YX)$ with the same $B$ action, so identity on sections defines $d_f^0$ and its inverse, natural in $H$, $n$, and $M$.

   Uses: def-coef-semilinear-system-models, lem-coef-semilinear-derived-sections, def-sp-varying-ring-operations
2. At level $n$, take the identified-coefficient inverse-image scalar comparison and its adjunction normalization from the ring-sheaf change theorem, on degree-zero objects. Geometric inverse image with identified constant coefficients is exact, so this is the ordinary inverse-image comparison. Its underlying map is the canonical inverse image of the unchanged additive sheaf; the coefficient action is through $\phi_n$. For each coefficient transition the two routes have this same underlying map and action, so they commute. Assemble these level isomorphisms as $b_f^0$. The level unit equation is an equality of ordinary system maps because ordinary morphisms are componentwise maps; it gives the unit equation for $b_f^0,d_f^0$ and hence the counit equation by adjunction.

   Uses: lem-weil-pbc-ring-sheaf-change-adjunction, lem-coef-semilinear-derived-sections
3. For the open comparison use the localized direct-sum extension and sheafification. Restricting actions keeps the direct-sum additive presheaf. Module sheafification is underlying abelian sheafification with uniquely extended action [def-weil-presheaf-modules-sheafification], so it also keeps the sheaf and gives an invertible comparison, identity on the sections defining the open unit. Transpose under the open Hom bijection to see that it is the specified open mate. The inverse of cartesian $\beta$ is itself defined by that unit and pullback composition, both preserved by these comparisons. The clopen projector is $(x,y)\mapsto(x,0)$ on the disjoint factors, which restricting actions preserves. Substitution into the definition of $\alpha_Q$ proves its compatibility as an ordinary system transformation.

   Uses: lem-pur-site-restriction-module-adjunction-exact, lem-sf-open-tensor-normalization, lem-sf-semilinear-clopen-unit-projector, def-sp-varying-ring-proper-open-arrows, def-weil-presheaf-modules-sheafification
Prior proof origin: {"by": "agent", "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md", "place": "Sentence on adjunction units and counits; explicit extraction from lem-sf-semilinear-proper-open-mate-pasting; Tag 03D7 (lemma-adjoint-pullback-pushforward-modules); agent-written assembly for varying rings, compatible constant-B actions and localized opens"}

## Final notation and citation audit

After the first repaired dry run returned OK at 1f818af67a5, I clarified notation in the alpha-pullback and compositor statements: P is exact derived inverse image, S is total derived direct image, and J is open extension. This matters because def-sp-varying-ring-operations uses G/P instead. I explicitly quantified the commutative ring B, scheme map f, open j, and square Q in the derived scalar statement. These are self-containment repairs of the intended statements, not a changed Mathlib search question; the logged search results remain applicable and were reused. I refreshed the full verbatim citation quotes for those statements. In parent step 2 I made P_s P_q = P_r explicit, and step 7 now states the binary reassociation argument.

The first repaired dry run exited 0 with preflight passed, confirming that the earlier six format rejections are resolved. No push had run at that point. The final dry run after these notation clarifications will be run to completion before the single push.

## Repair of the uncited-child return (2026-10-21)

The returned defect was that lem-sf-semilinear-scalar-ordinary-comparison was not cited by a parent step. A statement dependency of the derived-comparison node did not satisfy the requested direct use. I repaired parent step 5 to invoke the ordinary node for the exact functor rho^0, its unit-preserving ordinary comparisons and preservation of alpha, and only then invoke the derived node for localization and invertibility of the specified direct-image mate. Thus step 5 now uses both new statements for distinct mathematical assertions. I added the ordinary-node citation with its full verbatim statement and recomputed proof_deps from all step uses. No child statement, source, proof sketch or Mathlib search was discarded or abbreviated. Every one of the six new nodes is now cited directly by a parent proof step.

The required initial dry run completed with a duplicate-check failure against a newly present lem-pd-ringed-tensor-adjunction-mate (03D7) for both scalar nodes. I opened that node and added the two precise distinctions above. This is a tensor-mate theorem, not a varying-to-constant tower comparison theorem. Its statement and all retained same-tag comparisons were checked again. The delivery tools and launcher were not changed.

I compared the retained item against the current live item field by field. The only differences were proof, proof_deps, proof_origin and split_report; the statement, blueprint fields, Lean attachments and all review metadata agree. The repaired file starts with the live item and replaces only those four stage-1 fields, preserving current unrelated work. There is no new search question: the six statements and all previously logged queries remain unchanged. I read the 31 search-log entries and retained results; the generic conjugation/compositor hits supply parts of these arguments, not a one-line specialization proving a new node.

The current live proof's arguments are distributed as follows. Its step 1 system construction and beta invertibility are the existing varying-ring construction and open-normalization assertions; its rho construction and uniqueness by compatible ordinary sections are in the new ordinary scalar-comparison statement. Its step 2 separates into the new clopen unit-projector statement (including both component equations) and the five-category conjugate/open-factor transport statement, followed only by the triangle identity in parent step 2. Its step 3 uses the existing varying-ring binary pasting theorem. Its step 4 is the new alpha pullback-cube statement followed by the existing generic mate cube. Its step 5 ordinary scalar section normalizations and transition compatibility are the ordinary scalar node; the localization and evaluated-mate isomorphism argument is the derived scalar node; evaluation compatibility itself is already explicitly asserted by the existing simultaneous-section and varying-ring statements, and the finite comparison remains the existing constant-tower finite-normalization clause. Its step 6 ordinary fibre-product section coherence, exact localization, conjugation and equality transport are precisely the new compositor statement. All implementation accounts S4/C8/V2/T3 are covered by these assertions; they were not treated as additional hypotheses or deleted mathematical work. The previous supporting arguments remain verbatim earlier in this report.

I rechecked the new direct use in step 5 against its hypotheses: B is commutative, the maps B to C_n commute with transitions, the sites and all coefficient categories coincide, and only alpha's square requires the quasi-compact open/proper assumptions. Its exactness is restriction of actions, so the nonflat example Z to Z/2 needs no flatness assumption. The derived node is applied to D(rho^0), exactly its stated functor, and only isomorphism detection is used after evaluation. The other six parent steps retain the source/statement/hypothesis audits under Review by Q49 above. The parent remains below 3000 proof-text characters, no step exceeds 2000, and all six new statements remain unsplit with no proof steps.
