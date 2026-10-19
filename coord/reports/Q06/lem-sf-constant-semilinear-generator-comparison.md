# Stage 1 worker report

1. Files written: `dag/nodes/sec-six-functors/lem-sf-constant-semilinear-generator-comparison.json`, repaired to a thirteen-step split; `citations.json`, with 52 verbatim step/node citations. No new nodes and no Mathlib leaves. The retained sandbox was compared with current shared main: main still has the original unsplit item with no proof; its hypotheses, chapter, unit, ancestry and creation fields are retained. The prior five-step sandbox proof was used as the starting point, but its unsupported proper identifications and mate assertions have been replaced. For this C7 repair, the delivered thirteen-step version at returned head 7ee03c82ec was retained and changed as described below.
2. Attachments: none. Searches of `WeilConjectures/` in the read-only slopmaster2 source, for the item tag and the coefficient/direct-image notions, found no declaration stating the whole item without sorry.
3. WANTED: none. This is an agent expansion of the blueprint coherence obligation, using existing DAG statements, rather than a claim that Stacks 0E48 states scalar-restriction compatibility.
4. What was wrong: the prior Step 1 supplied no justified unbounded scalar/direct-image comparison, Step 2 asserted that restriction preserved transposes without its counit square, and Step 5 repeated that gap for the proper unit/counit clause. The proper argument now works on one ringed diagram topos, applies the generic derived-composition comparison and the reviewed `lem-pur-ringed-coefficient-restriction-counit`, constructs a semilinear lift of the constant projection morphism, and identifies its actual reduction/limit adjunct. The open argument retains its common flat tensor construction and now cites the exact `q_j` formula from `lem-sf-cbc-extension-zero-completion`.
5. What remains unfinished: none in the split. Its cited unsplit nodes remain DAG obligations; none is claimed proved by this delivery.

## Statement corrected

STATEMENT-DISPUTED (typing of the printed display only): the original abbreviated right side was `q_{A,H_VM} ∘ ρ_{A_int M}`. The target of `ρ_{A_int M}` is `R_T^T(H_T A_int M)`, while the source of `q` is `R_T^T(A_c H_V M)`. The surrounding sentence requested an identification between those objects; the repaired display writes it explicitly as `R_T^T(σ_{A,M})`, with `σ_{A,M}:H_T A_int M ≅ A_c H_V M`. This changes no hypothesis or conclusion after the already requested identification. No target statement or definition has been changed. The proper `σ` is normalized by the same integral reduction tower and derived pushforward/limit comparison; the open `σ` is the actual completion unit after exact open scalar restriction.

## Sources and searches

I read the unit `sk-thm-sf-identification`, the chapter record, and blueprint `main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`, lines 9–15: the prescribed coefficient maps use tensor reassociation, evaluation and adjunction units/counits before taking mates. The repair also reads Stacks `sites-cohomology.tex`: 07A4 (`lemma-pullback-tensor-product`, line 3684), 07A6 (`lemma-adjoint`, line 3990), 0D6D (`lemma-derived-pullback-composition`, line 3658), 0D6E (`lemma-derived-pushforward-composition`, line 4011), 0FPI (`lemma-adjoints-push-pull-compatibility`, line 4129), and 0E48 (`remark-compatible-with-diagram`, line 13715). I read `derived.tex` 0FND/0DVC, the representative characterization used for the constant-tower counit. In particular 0E48 is a pullback-base-change/projection compatibility remark and is not used as a restriction-of-scalars theorem.

The old searches and their results were read and retained in `searches.jsonl` and the item's `mathlib_searches`; their underived restriction and ordinary-completion hits do not state this item. Additional searches were run only through `msearch.py` and copied from that log. The first new Loogle pattern had an unknown identifier and is recorded as such; the valid `CategoryTheory.Adjunction, "counit"` query was then run and read. LeanFinder returned ordinary presheaf/sheaf restriction maps, and the second formulation returned ordinary adic-completion formulas. LeanSearch returned ordinary module change-of-ring adjunctions. The grep for derived/direct-image scalar restriction in `Mathlib/Algebra/Category` returned no hits. None is a one-line specialization of this strict varying-ring comparison. No service failure was recorded as an empty successful search, and no unrun query was added.

## October 18 C7 repair and comparison with current main

The return identifies one route fault, with three paths: the item's direct semilinear-sections citation, and the same interface through generator coherence and integral open reduction. I retained the delivered thirteen-step proof and all search records. The first required dry run exited with a stale citation error at Step 1: its quote was from the old enhanced statement of `lem-coef-semilinear-derived-sections`. The sandbox contains no `review.md`; I used the supplied return entry and read the actual current statements and proofs rather than claiming to have that missing review.

Current main still has this item unsplit with no proof. Its id, kind, chapter, unit, created fields, blueprint ancestry and statement dependencies agree with the retained sandbox. Its statement differs only by the already reported explicit typing factor, and now by clarification that the same operations are ordinary derived functors. Main has since merged the ordinary restatement of `lem-coef-semilinear-derived-sections` (reviewer NT-cc-NE-e8ae20921; the node-specific human instruction is `coord/repair-notes/lem-coef-semilinear-derived-sections.json`). I read that entire repaired statement and its 16 steps. The ordinary clauses give all this item uses: exact inverse image, total right derived termwise direct image on all strict systems, exact open extension, and specified ordinary unit/counit words. They require neither an enhanced equivalence nor an adjoint on normalized systems. Its source metadata still contains an old enhanced-description sentence; that stale sentence is not a theorem used here, and I have not edited the other worker's node.

This is a mathematical repair, beyond rebasing the old proof. The item now defines $S_p$ as total right derived termwise direct image on $D(\mathscr S)$, and $J_j$ as exact termwise extension by zero. Rewritten Step 1 identifies strict systems directly with modules on the ringed sequence topos and derives $F_a\dashv Rf_{a*}$ there. It no longer identifies an independently constructed section operation merely by uniqueness of its adjoint. Steps 5, 11 and 13 explicitly keep reduction, exact open extension and all comparisons in these ordinary derived categories. The proof retains the actual proper counit square, whole-tower projection calculation and open completion-unit equation, which the return did not dispute. The statement's hypotheses and conclusion have not been weakened.

I followed both indirect paths as requested. `lem-sf-generator-reduction-coherence` uses the ordinary $S_p,J_j$ operations and the actual $\mathcal R\dashv\mathcal L$ transpose; this proof uses only its displayed formula for $r_A$, not a realization of expression trees. `lem-sf-integral-open-reduction-comparison` uses exact termwise extension, a common K-flat reduction representative, and actual completion unit; this proof uses precisely its $r_j$ and completeness clauses. Their references to the same semilinear interface now land at its repaired ordinary statement. I traversed both `stmt_deps` and `proof_deps` of all 27 cited roots against the 1391 ids in `coord/route-pivot-dropped.txt`; every intersection is empty. In particular the semilinear-sections closure has 407 nodes, generator coherence has 11048, and integral-open comparison has 2322, with zero dropped ids. The reproducible findings are retained in `ordinary-route-audit.json`. No claim that the ordinary route fails is needed: Steps 1–13 implement that route successfully.

The logged Mathlib search question has not changed: it already asked about derived scalar restriction and specified generator maps, so I reused its results. I read the old log, the recorded hit summaries and the underived candidate `PresheafOfModules.pushforward` at `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pushforward.lean:89`; that definition and ordinary module restriction do not state this derived generator comparison. The entire blueprint search for “semilinear generator” again found no duplicate blueprint node. No new node or new Mathlib absence claim was introduced. The source checks for this repair additionally read Stacks 06YS (`lemma-K-flat-resolution`), 0E8I/0GL1 (`lemma-j-shriek-and-tensor`) and 0FND (`lemma-pre-derived-adjoint-functors-general`), as well as 07A4/07A6/0D6D/0D6E/0FPI/0E48 and the blueprint coherence sentence already listed above. The generalized coefficient-restriction counit is cited as its own existing node, not attributed verbatim to 0E48.

## Review by Q06

I checked the returned item against its sources and opened the full statements of all 27 distinct proof dependencies. The decisive additional existing node is `lem-pur-ringed-coefficient-restriction-counit`, already reviewed in the current DAG: it treats arbitrary small ringed topoi, unbounded complexes, nonconstant algebra sheaves and nonflat coefficient maps. It supplies the actual counit identity for precisely the normalized derived-composition comparison, so unlike the bounded-below etale analogues it applies on the ringed diagram topos. There are no new statements to defer or possible new-node duplicates.

For each proof step I checked what the citations provide:

1. I rechecked the rewritten ordinary construction: the diagram-site statement supplies fixed-index covers; the varying ring sheaf then makes its modules exactly strict semilinear systems, including the semilinear transition equations. The scalar adjunction node gives $E_T\dashv U_T$ with its specified unit/counit. The module-adjunction node gives the geometric module adjunction, and the ringed projection-mate statement explicitly supplies its unbounded derived adjunction. The repaired semilinear-sections statement says that its $G$ is the total right derived functor of this same termwise direct image, so $S_f$ is this functor directly. Only ambient categories are used; normalized-input hypotheses are imposed afterwards. I checked this against the ordinary statement, not its stale source description, and regenerated the obsolete quote.
2. The unbounded derived-pushforward-composition statement gives the isomorphism for the two factorizations of the identical ringed morphism. The monoidal/composite-adjunction statement normalizes the pullback comparison and its composite adjunction. I checked the ring maps commute at every quotient and that the diagram sites are small. No finite quotient is assumed flat over the constant ring.
3. The scalar-adjunction statement gives the exact chain formula `b⊗q ↦ bq` for the counit on a flat-term K-flat replacement; the replacement theorem gives that replacement. Tensor-pullback and composite normalization justify its pullback. Since the geometric pullback is exact and the pulled-back quotient ring is the target quotient ring, the mate is the ordinary scalar-unit comparison, with the correct direction.
4. The generic coefficient-restriction-counit statement applies with constant ring `R` on the diagram topoi and the varying quotient ring as algebra. Its `κ` is the Step 2 comparison and its `τ` is the Step 3 map. Its displayed equality is exactly the required geometric counit square. The inverse mate formula and the triangle identity give the unit square as written. This repairs both the proper half of old Step 2 and old Step 5; it is not an appeal to levelwise equality.
5. Constant completion supplies flatness of the completed sheaf over the constant sheaf and equality of its finite quotients. I checked K-flatness after restriction by writing `D⊗_R Q=(D⊗_R R̂)⊗_R̂ Q`; the first tensor preserves acyclicity by flatness, the second by K-flatness. Constant-diagram pullback preserves flat-term K-flat complexes by the cited ringed-pullback theorem. Thus the strict reduction models are really the same quotient complex, with all transitions. The DVR node makes `R` a PID, hence Noetherian; the finite-quotient node supplies finite quotients, and the displayed two-term finite-free resolution supplies perfectness. A finite residue ring has additive torsion. These verify the coefficient hypotheses of the one-letter constant-tower theorems.
6. The evaluation-right-adjoint formula gives `Δ=e_{1*}` because `1` is terminal in the inverse integer category. Exact evaluation and the right-adjoint K-injective lemma imply that a K-injective `J` gives a K-injective tower `ΔJ`. The normalization node states that `χ` is represented by `p_*ΔJ=Δp_*J`. The pre-derived adjunction's representative formula, with identity representatives, identifies the derived counits with the underived counits on these resolved objects. Therefore the constant-tower counit square is a whole-tower chain-map identity, not an inference from evaluated identities.
7. The projection node defines its map as the transpose of counit tensor identity. I computed the transpose of the restricted semilinear lift using the proved counit square; it is exactly that tensor map. Step 6 supplies its normalization under `χ`. Injectivity of the actual geometric adjunction Hom bijection gives equality of the specified projection morphisms. This writes the missing calculation behind the old phrase “taking its scalar restriction preserves that transpose.”
8. The constant-tower normalization statement gives both `h i=G(i)χ` and its clause (3) at the limit. The pushforward-limit theorem supplies the natural comparison `a`. Taking the total limit of the first identity and substituting the second gives the displayed equality (*). I checked this uses identities of maps on the whole diagram and not uniqueness from projections, which would be invalid here.
9. Generator coherence supplies the specified `d_A`. Restricting its common tower and using the pushforward-limit comparison defines the canonical `σ`. The constant completion statement identifies the actual unit; the completion-reflector statement says direct image preserves complete constant-coefficient objects. Thus every inverted factor is invertible for a stated reason. The same pushforward-limit theorem applied to identity-topos coefficient restriction handles arbitrary underlying completed-ring towers, so its application is not limited to finite-reduction towers.
10. The actual reduction/limit adjunction supplies the adjunct of the constructed lift. Naturality of the completion unit and (*) compute this adjunct after constant restriction. The normalized effectivity statement makes `L N` complete, and `d_A` makes `X` complete. Hence the complete-coefficient equivalence is faithful on these objects; this is the legitimate faithfulness used to identify the adjunct with `d_A^{-1}`. Generator coherence then identifies its transpose with `r_A`. This is a proof of the proper comparison, not a new statement restating it.
11. Exact localized open extension/restriction gives the same generators, unit and counit before and after forgetting scalars. I checked these are equalities of exact complex functors and strict transitions. The integral-open statement gives completeness of `j_!M`; constant completion transfers it, making the specified open `σ` its actual completion unit. Ordinary open extension is not asserted to commute with total limits.
12. The integral-open node gives the normalized open-tensor system map; the extension-zero-completion node gives `q_j R(η)=q_j^tens` and its finite-level formula, with transitions. Both open tensor maps have the same adjunct on the open and the same quotient transition formula. Substitution gives the full typed equality, including `R(σ)`. The composition-limit node identifies its one-letter `q` with this `q_j`.
13. The naturality clauses of the cited constructions and the mate formula give naturality and the final mate compatibility. The proper and open unit/counit clauses were already proved in Steps 4 and 11. All finite interval, constructibility, and etale-origin restrictions are retained where the generator-normalization node requires them; none is silently added to a generic ambient theorem.

I checked the edge cases `n=1`, `p=id`, `j=id`, the empty open, and the zero complex. For `p=id` the two common-composite comparisons are identity comparisons and the proper map is the scalar tensor unit. For `j=id`, the open map is the inverse of reduction of the actual completion unit; for a complete input that unit is invertible. For the empty open or zero input all maps have the required zero source or target. The K-flat and K-injective arguments apply to unbounded complexes; the only use of completeness for cancellation is expressly through the complete-subcategory equivalence, never through finite evaluations. All 13 steps are below 2000 characters, and their categorical calculations are written out rather than hidden in “transports” or a new clause node. No SGA source, Lean edit, compiler, Lake command, live-project write or local preflight was used.

For this C7 retry I rechecked every quoted statement against current main and regenerated all 52 verbatim entries in `citations.json`. I also checked the preceding step-by-step review against the retained calculations: the only changed use is the ordinary functor identification in Step 1. Steps 2–4 still prove both proper adjunction equations, Steps 5–10 still identify the specified proper coefficient arrow by its actual adjunct, and Steps 11–12 still identify the specified open arrow on one strict tensor model. The small cases listed above remain valid after the route clarification: in particular $p=\mathrm{id}$ gives the identity comparison and $j=\mathrm{id}$ gives the inverse of reduction of the actual completion unit, while the empty open gives zero. All thirteen steps remain below 2000 characters (maximum 1775); I checked for hidden standalone lemmas rather than just their lengths. B1–B9 and D1–D5 introduce no new-node issue because no new node is created; C1/C4 and E1–E5 are covered by the explicit 13-step review and the verbatim citations. No tool was edited or worked around, no agents were started, and only the sandbox was written.

## C7 repair artifacts: exact route-pivot inputs
The prior return required three immutable inputs in the review snapshot. I include exact copies here so the delivery report itself carries the audit inputs. The manifest is copied byte-for-byte from `coord/route-pivot-dropped.txt`; the applicable repair note is copied byte-for-byte from `coord/repair-notes/lem-coef-semilinear-derived-sections.json`.

### Dropped-node manifest

```text
# Route pivot (decision of the human, 2026-10-18): nodes of the dropped infinity/dg/model-category machinery, the nodes
# only it reached, and the Zariski-gluing branch (lem-cbc-etale-local-compact-support-extension, lem-cbc-global-transport-
# chart-normalization). A reachable node must not cite them (svc.py route_pivot_note, postcheck). Not touched by note
# cleanups; one id per line.
def-cbc-bounded-representable-hypercover
def-cbc-derived-hypersheaf-presentation
def-cbc-enhanced-cartesian-fibration
def-cbc-enhanced-diagrams-cones
def-cbc-enhanced-strong-saturation
def-cbc-local-simplicial-presheaf-maps
def-coef-algebroid-graph
def-coef-algebroid-terminal-space-pairing
def-coef-augmented-vertex-diagrams
def-coef-bounded-filtered-subcategory-system
def-coef-brown-reedy-diagrams
def-coef-categorical-pattern-fibrancy
def-coef-coherent-adjunction-data
def-coef-coherent-bar-word-data
def-coef-coherent-localization-interface
def-coef-coherent-monad-modules
def-coef-coherent-nerve-infrastructure
def-coef-coherent-pullback-comparison
def-coef-colored-operator-systems
def-coef-complete-algebroid
def-coef-continuous-space-presheaf
def-coef-cosimplicial-product-total
def-coef-dg-derived-enrichment
def-coef-dg-quillen-diagram
def-coef-discrete-fibration
def-coef-enriched-coend
def-coef-enriched-interval-strings
def-coef-face-cocone-evaluation
def-coef-finite-limits-square-cones
def-coef-free-category-comonad
def-coef-good-cellular-tree
def-coef-graded-linear-category
def-coef-homotopy-segal-space
def-coef-infinity-category-of-spaces
def-coef-infinity-fibrations
def-coef-infinity-left-anodyne
def-coef-infinity-marked-coanodyne
def-coef-infinity-presheaf-yoneda
def-coef-infinity-relative-cone
def-coef-infinity-relative-join
def-coef-infinity-right-anodyne
def-coef-injective-homotopy-limit
def-coef-inserter
def-coef-integral-derived-coefficients
def-coef-iterated-span-completion-rule
def-coef-join-slice
def-coef-left-module-operadic-encoding
def-coef-lm-pointed-projection
def-coef-mapping-simplex-functor
def-coef-mixed-grothendieck-construction
def-coef-module-operad-lm-zero
def-coef-monoidal-infinity-category
def-coef-nonsymmetric-monoid-axiom
def-coef-operadic-correspondence
def-coef-operadic-typec-incidence-data
def-coef-operadic-weak-approximation
def-coef-ordered-join
def-coef-oriented-tree-subtree-zigzags
def-coef-presentable-infinity-category
def-coef-quillen-derived-diagram
def-coef-rectified-space-limit
def-coef-relative-symmetric-operadic-algebras
def-coef-segal-interval-cover
def-coef-segal-presheaf-localization
def-coef-segal-space
def-coef-simple-presheaf-inner-anodyne
def-coef-simplicial-groupoid
def-coef-simplicial-hammock-pair
def-coef-simplicial-model-realization
def-coef-simplicial-multicategory
def-coef-simplicial-realization-map
def-coef-simplicial-tensor-cotensor
def-coef-space-base-change
def-coef-space-tower-homotopy-limit
def-coef-strict-quillen-sections
def-coef-symmetric-operadic-approximation
def-coef-symmetric-operadic-family
def-coef-tensored-algebroid-presentation
def-coef-universally-localizing-simplicial-map
def-coef-zigzag-homotopy-calculus
lem-cbc-bounded-below-hypersheaf-model
lem-cbc-cartesian-mapping-simplex-comparison
lem-cbc-cocartesian-section-currying
lem-cbc-cocartesian-sections-limit
lem-cbc-cofiltered-coherent-equivalence-diagrams
lem-cbc-coherent-cartesian-postcomposition
lem-cbc-coherent-square-comparison-data
lem-cbc-cosimplicial-complex-holim
lem-cbc-cw-source-homotopy-lift
lem-cbc-dense-hypercover-set
lem-cbc-dense-hypersheaf-comparison
lem-cbc-dg-presheaf-model-localizations
lem-cbc-disk-lifting-surjective
lem-cbc-dold-kan-homology
lem-cbc-dold-kan-hypercover-quillen
lem-cbc-enhanced-equivalence-square-mates
lem-cbc-enhanced-functor-cone-calculus
lem-cbc-enhanced-relative-exponential
lem-cbc-equivalence-outer-horn-filling
lem-cbc-etale-local-compact-support-extension
lem-cbc-filtered-nerve-weak-contractibility
lem-cbc-framed-horn-criterion
lem-cbc-framed-localizing-cofibrations
lem-cbc-general-bousfield-localization
lem-cbc-global-transport-chart-normalization
lem-cbc-grothendieck-coherent-end
lem-cbc-grothendieck-hyperdescent-local-refinement
lem-cbc-grothendieck-hypersheaf-sections
lem-cbc-grothendieck-presheaf-coherent-straightening
lem-cbc-hom-functor-composition-coherence
lem-cbc-homotopy-local-equivalences-accessible
lem-cbc-hypercover-cotensor-local-acyclic-fibration
lem-cbc-hypercover-localization-generation
lem-cbc-hypercover-relative-lifting
lem-cbc-hyperdescent-local-orthogonality
lem-cbc-initial-prism-horn-filtration
lem-cbc-inner-fibration-equivalence-outer-horn-lift
lem-cbc-internal-hom-fibration-corner-map
lem-cbc-internal-hom-quasicategory
lem-cbc-invertible-prism-extension
lem-cbc-kan-contracted-base-section-extension
lem-cbc-kan-fibration-fiber-criterion
lem-cbc-kan-functor-space-kan
lem-cbc-kan-mapping-homotopy-invariance
lem-cbc-kan-realization-mapping-classes
lem-cbc-kan-relative-realization-lift
lem-cbc-kan-whitehead-inverse
lem-cbc-kinjective-derived-mapping-complex
lem-cbc-left-fibration-equivalence-lift
lem-cbc-left-proper-derived-cell-colimits
lem-cbc-local-acyclic-matching-cover-criterion
lem-cbc-local-acyclic-matching-generalized-cover
lem-cbc-local-weak-equivalence-homotopy-lifting
lem-cbc-mapping-simplex-initial-horn-pushout
lem-cbc-mapping-simplex-universal-equivalence
lem-cbc-marked-homotopy-precomposition
lem-cbc-marked-mapping-simplex-descent
lem-cbc-marked-relative-nerve-quillen
lem-cbc-nonfree-chain-completions
lem-cbc-normalized-horn-disk
lem-cbc-normalized-simplex-chain-diagonal
lem-cbc-opposite-interval-internal-hom
lem-cbc-opposite-sset-lifting-properties
lem-cbc-pinched-cube-augmentation-uniqueness
lem-cbc-presheaf-dg-function-complex
lem-cbc-projective-cochain-dg-compatibility
lem-cbc-projective-cochain-suspension
lem-cbc-realization-compact-finite-support
lem-cbc-realization-cw-subcomplex
lem-cbc-realization-singular-unit-weak
lem-cbc-realization-weak-equivalence
lem-cbc-relative-coslice-left-fibration
lem-cbc-relative-nerve-cone-left-comparison
lem-cbc-relative-nerve-projective-cofibrancy
lem-cbc-right-fibration-morphism-space
lem-cbc-right-fibration-space-fiber
lem-cbc-right-resolution-mapping-criterion
lem-cbc-simplexwise-categorical-base-change
lem-cbc-simplicial-composition-spine
lem-cbc-simplicial-groupoid-localization
lem-cbc-simplicial-homotopy-equivalence-weak
lem-cbc-simplicial-hypercover-fibration-test
lem-cbc-simplicial-module-model
lem-cbc-simplicial-module-moore-homotopy
lem-cbc-spine-inner-anodyne
lem-cbc-standard-simplex-mapping-contractible
lem-cbc-strict-presentation-transport-representation
lem-cbc-terminal-boundary-extension
lem-cbc-weak-equivalence-relative-disk-extension
lem-cbc-whitehead-cw-homotopy-inverse
lem-cbc-zariski-enhanced-derived-descent
lem-coef-accessible-arrow-inverse-image
lem-coef-accessible-compact-cocones
lem-coef-accessible-compact-slice-density
lem-coef-accessible-completeness-characterization
lem-coef-accessible-diagram-presentations
lem-coef-accessible-full-inverse-image
lem-coef-accessible-functor-presentability-ranks
lem-coef-accessible-ind-colimit-extension
lem-coef-accessible-infinity-pullback
lem-coef-accessible-infinity-rank-calculus
lem-coef-accessible-intersection-generators
lem-coef-accessible-localization-small-generators
lem-coef-accessible-monad-presentability
lem-coef-accessible-pie-closure
lem-coef-accessible-pullback-filtered-colimit
lem-coef-accessible-small-object-factorization
lem-coef-accessible-subdiagram-criterion
lem-coef-accessible-system-ranks
lem-coef-active-concatenation-block-projections
lem-coef-active-operad-cocartesian-concatenation
lem-coef-active-operad-envelope-cocartesian
lem-coef-adjunction-block-run-collapse
lem-coef-adjunction-fillable-parent-bijection
lem-coef-adjunction-free-simplicial-resolution
lem-coef-adjunction-nondistinguished-face-rank
lem-coef-adjunction-square-lifts
lem-coef-adjunction-squiggle-normal-form
lem-coef-adjunction-two-block-splicing
lem-coef-algebroid-bilinear-colimits
lem-coef-algebroid-categorical-homotopy
lem-coef-algebroid-cocontinuous-base-change
lem-coef-algebroid-completion
lem-coef-algebroid-cotensor-nerve-exchange
lem-coef-algebroid-equivalence-arrow-descent
lem-coef-algebroid-equivalence-nerve
lem-coef-algebroid-external-product
lem-coef-algebroid-ff-simplicial-realization
lem-coef-algebroid-object-space-fibration
lem-coef-algebroid-presentability
lem-coef-algebroid-segal-localization-model
lem-coef-algebroid-universe-embeddings
lem-coef-all-cofibrant-left-proper
lem-coef-all-cofibrant-mapping-detection
lem-coef-all-cofibrant-simplicial-recognition
lem-coef-arrow-endomorphism-planar-operad
lem-coef-arrow-prism-collage-inner-anodyne
lem-coef-arrow-target-cartesian-pullbacks
lem-coef-associative-algebra-diagram-cell-filtration
lem-coef-associative-algebra-model-transfer
lem-coef-associative-algebra-sifted-localization
lem-coef-associative-reflective-localization
lem-coef-associative-word-filtration
lem-coef-augmented-vertex-cone-recognition
lem-coef-bifibrant-comparison-common-replacement
lem-coef-bimodule-word-path-approximation
lem-coef-bipartite-cocartesian-simplex-extension
lem-coef-bisimplicial-diagonal-equivalence
lem-coef-bisimplicial-diagonal-space-colimit
lem-coef-bisimplicial-reedy-division-calculus
lem-coef-boundary-lifting-quasicategory-equivalence
lem-coef-boundary-proper-face-limit
lem-coef-bousfield-kan-comparison-calculus
lem-coef-bousfield-local-fibrations
lem-coef-bousfield-quillen-descent
lem-coef-bousfield-smith-bounded-generation
lem-coef-brown-cocone-equivalence-transport
lem-coef-brown-fibrant-localization-pullbacks
lem-coef-brown-finite-direct-rectification
lem-coef-brown-left-fractions
lem-coef-brown-localization-products
lem-coef-brown-reedy-fibrant-replacement
lem-coef-brown-right-exact-extension
lem-coef-brown-slice-fraction-calculus
lem-coef-brown-span-coherent-rectification
lem-coef-canonical-hocolim-degree-reduction
lem-coef-cardinal-small-object-factorization
lem-coef-cartesian-associative-segal-comparison
lem-coef-cartesian-base-equivalence-invariance
lem-coef-cartesian-colimit-descent-criterion
lem-coef-cartesian-colimit-localization
lem-coef-cartesian-comma-normalization
lem-coef-cartesian-cone-fiber-comparison
lem-coef-cartesian-core-right-fibration
lem-coef-cartesian-envelope-cocartesian-criterion
lem-coef-cartesian-envelope-product-diagram-recognition
lem-coef-cartesian-grothendieck-colimit-formula
lem-coef-cartesian-left-adjoint-transport
lem-coef-cartesian-mapping-simplex-mixed-mapping-equivalence
lem-coef-cartesian-mapping-simplex-presentation
lem-coef-cartesian-mapping-simplex-prism-extension
lem-coef-cartesian-maps-presheaf-extension
lem-coef-cartesian-marked-lift-generation
lem-coef-cartesian-marked-slice-restriction
lem-coef-cartesian-matrix-model
lem-coef-cartesian-monoidal-straightening
lem-coef-cartesian-monoidal-structure-uniqueness
lem-coef-cartesian-operadic-envelope
lem-coef-cartesian-simplex-inverse-extension
lem-coef-cartesian-terminal-twisted-resolution
lem-coef-cat-infinity-colimits-cartesian-closure
lem-coef-cat-infinity-filtered-finite-calculus
lem-coef-cat-infinity-opposite-involution
lem-coef-categorical-algebra-free-monad
lem-coef-categorical-equivalences-small-generation
lem-coef-categorical-pattern-model-calculus
lem-coef-cellular-tree-presentable-approximations
lem-coef-cellular-weight-coherent-transfer
lem-coef-chain-interval-tensor-cylinder
lem-coef-chunk-bifibrant-localization
lem-coef-chunk-localized-evaluation-exponential
lem-coef-closed-self-enrichment-base-change
lem-coef-coarse-nerve-gluing
lem-coef-cocartesian-categorical-base-change
lem-coef-cocartesian-cone-limit-section-test
lem-coef-cocartesian-full-restriction
lem-coef-cocartesian-horn-completion-comparison
lem-coef-cocartesian-joyal-fibration
lem-coef-cocartesian-local-global
lem-coef-cocartesian-prescribed-cone-colimit-lifting
lem-coef-cocartesian-relative-cylinder-extension
lem-coef-cocartesian-relative-right-adjoint
lem-coef-cocartesian-right-kan-extension-simplex-powers
lem-coef-cocartesian-section-colimits
lem-coef-cocartesian-straightening
lem-coef-cocartesian-straightening-universe-change
lem-coef-cocartesian-three-horn-face-conservation
lem-coef-cocomplete-cofibration-localization
lem-coef-cocomplete-monoidal-tensor
lem-coef-cocone-pie-realization
lem-coef-cocontinuous-localization-factorization
lem-coef-cofibrant-completion-nerve-equivalence
lem-coef-cofibrant-homotopy-groupoid-completion
lem-coef-cofibrant-inclusion-coherent-localization
lem-coef-cofibrant-localization-diagonal-nerve
lem-coef-cofibrant-simplicial-inversion
lem-coef-cofibrant-subset-colimit-decomposition
lem-coef-cofibration-local-mapping-test
lem-coef-cofinal-natural-equivalence-invariance
lem-coef-cofinal-relative-join-slice-restriction
lem-coef-coherent-diagram-coyoneda
lem-coef-coherent-diagram-universe-naturality
lem-coef-coherent-end-twisted-arrow-formula
lem-coef-coherent-fixed-vertex-cofibrations
lem-coef-coherent-inner-anodyne-equivalences
lem-coef-coherent-module-section-model
lem-coef-coherent-nerve-comparison
lem-coef-coherent-nerve-pinched-adjunction
lem-coef-coherent-nerve-relative-cube-comparison
lem-coef-coherent-prism-pinch-identity
lem-coef-coherent-realization-bead-normal-form
lem-coef-coherent-realization-relative-cells
lem-coef-coherent-row-colimit-comparison
lem-coef-coherent-vertex-equivalence-lifts
lem-coef-coherent-weight-limit-recognition
lem-coef-coinitial-monomorphism-left-anodyne
lem-coef-colimit-cocone-transport-equivalence
lem-coef-colimit-subdiagram-approximation
lem-coef-collage-crossing-transformations
lem-coef-colored-operation-section-reconstruction
lem-coef-combinatorial-bounded-resolutions
lem-coef-combinatorial-cofibrant-density
lem-coef-combinatorial-injective-diagram-model
lem-coef-combinatorial-localization-presentability
lem-coef-combinatorial-presheaf-presentation
lem-coef-common-chunk-filtered-approximation
lem-coef-compact-closed-t1-chain
lem-coef-compact-diagram-cocone-transport
lem-coef-compact-model-pr-duality
lem-coef-compact-presentation-functor-refinement
lem-coef-compact-pushout-retract-descent
lem-coef-compact-relative-cocone-factorization
lem-coef-compact-small-colimits
lem-coef-complete-segal-dk-levelwise
lem-coef-complete-segal-path-fiber-comparison
lem-coef-complete-segal-quasicategory-comparison
lem-coef-complete-segal-walking-isomorphism
lem-coef-composable-bimodule-operad-segal
lem-coef-cone-apex-cocone-space-comparison
lem-coef-cone-boundary-projective-cells
lem-coef-cone-equivalence-saturation
lem-coef-cone-presheaf-adjunction
lem-coef-cone-sorted-theory-identification
lem-coef-cone-straightening-coherent-evaluation
lem-coef-cone-triangle-mapping-square
lem-coef-cone-unit-weighted-evaluation
lem-coef-constant-diagram-mapping-limit
lem-coef-contractible-factor-universal-localization
lem-coef-contractible-join-right-anodyne
lem-coef-contractible-split-inclusion-saturation
lem-coef-contraction-word-bar-faces
lem-coef-contravariant-fibrations-between-right-fibrations
lem-coef-contravariant-slice-model
lem-coef-corepresented-equivalence
lem-coef-cosimplicial-frame-mapping
lem-coef-cosimplicial-presheaf-counit
lem-coef-cotorsion-orthogonality-calculus
lem-coef-counit-cone-boundary-extension
lem-coef-countable-equivalence-witness
lem-coef-countable-sphere-homotopy-classes
lem-coef-covariant-derived-replacement-base-change
lem-coef-cube-relation-realization
lem-coef-cubical-open-box-pair
lem-coef-cut-chain-forest-compatibility
lem-coef-day-cocone-relations-compatible
lem-coef-day-model-yoneda-strong-monoidal
lem-coef-day-relative-exponential-model
lem-coef-decomposition-local-colimit-cocones
lem-coef-decomposition-simplex-attachment
lem-coef-decomposition-simplex-lift-right-anodyne
lem-coef-degreewise-cartesian-pullback-cat-infinity
lem-coef-derived-enriched-yoneda
lem-coef-derived-restriction-bifibrant-nerve-equivalence
lem-coef-derived-restriction-rectification
lem-coef-derived-space-module-coyoneda
lem-coef-dg-bifunctor-cofibrancy-fibrancy
lem-coef-dg-derived-quillen-calculus
lem-coef-dg-enrichment-rectification
lem-coef-dg-filtered-quasi-iso
lem-coef-dg-finite-twisted-extension
lem-coef-dg-free-cell-mapping-fibre
lem-coef-dg-mate-pasting
lem-coef-dg-mate-transpose
lem-coef-dg-model-homotopy-colimits
lem-coef-dg-model-mapping-comparison
lem-coef-dg-model-underlying-localization
lem-coef-dg-module-arrow-category-comparison
lem-coef-dg-module-base-change
lem-coef-dg-module-cone-triangulation
lem-coef-dg-module-diagram-classification
lem-coef-dg-module-projective-resolution
lem-coef-dg-module-semi-free-replacement
lem-coef-dg-module-tensor-currying
lem-coef-dg-monoidal-unit-image
lem-coef-dg-product-localization
lem-coef-dg-quasifunctor-invariance
lem-coef-dg-quillen-enriched-adjunction-descent
lem-coef-dg-quotient-hom-cone
lem-coef-dg-resolution-square-projection
lem-coef-dg-semi-free-cofibrant
lem-coef-dg-semi-free-homotopically-projective
lem-coef-dg-two-sided-bar-derived-tensor
lem-coef-dgcat-bimodule-mapping-space
lem-coef-dgcat-cell-comparison-functors
lem-coef-dgcat-cone-word-normal-form
lem-coef-dgcat-equivalence-cell-calculus
lem-coef-dgcat-finite-limit-sketch-signature
lem-coef-dgcat-formal-cone-enlargement
lem-coef-dgcat-free-cell-calculus
lem-coef-dgcat-model-structure
lem-coef-dgcat-sketch-model-identification
lem-coef-dgfunctor-coherent-transport
lem-coef-dgfunctor-rectified-model-comparison
lem-coef-dgfunctor-small-model
lem-coef-diagonal-coherent-nerve-comparison
lem-coef-diagram-cellular-compatible-slices
lem-coef-diagram-compact-pushout-descent
lem-coef-dinatural-section-evaluation
lem-coef-direct-wfs-extension
lem-coef-directed-algebroid-extreme-hom-pushout
lem-coef-directed-cover-colimit-assembly
lem-coef-directed-cover-mixed-subset-cells
lem-coef-directed-decomposition-right-anodyne
lem-coef-directed-enriched-amalgamation
lem-coef-directed-three-face-mapping-pushout
lem-coef-discrete-base-cocartesian-recognition
lem-coef-discrete-inner-cell-transfer
lem-coef-discrete-weight-coherent-cocones
lem-coef-dk-cofibrant-localization-comparison
lem-coef-dk-normalized-presentation-comparisons
lem-coef-dk-weak-exponential-limit-criterion
lem-coef-double-cylinder-weak-equivalence-gluing
lem-coef-double-mapping-cylinder-space-pushout
lem-coef-dugger-cardinal-choice
lem-coef-dugger-homotopically-surjective-map
lem-coef-dugger-localization-criterion
lem-coef-edge-homotopy-quotient-calculus
lem-coef-edge-inverting-anodyne-extension
lem-coef-endpoint-fixed-inner-horn-refinement
lem-coef-enhanced-localization-universal
lem-coef-enriched-bar-projective-replacement
lem-coef-enriched-category-tensor-calculus
lem-coef-enriched-coend-homotopy-invariance
lem-coef-enriched-coherent-adjunction-extension
lem-coef-enriched-completion-localization
lem-coef-enriched-cotensor-mapping-objects
lem-coef-enriched-diagram-homotopy-descent
lem-coef-enriched-diagram-rectification
lem-coef-enriched-evaluation-replacement-coherence
lem-coef-enriched-exponential-nerve-criterion
lem-coef-enriched-fibre-assembly
lem-coef-enriched-fixed-set-model
lem-coef-enriched-functorial-factorizations
lem-coef-enriched-hom-twisted-arrow-comparison
lem-coef-enriched-homotopy-localization
lem-coef-enriched-kan-diagram-weak-equivalence
lem-coef-enriched-mapping-cylinder-localization
lem-coef-enriched-marked-realization
lem-coef-enriched-nerve-transformation
lem-coef-enriched-presheaf-rectification
lem-coef-enriched-projective-diagram-model
lem-coef-enriched-simplicial-presentation
lem-coef-enriched-small-products
lem-coef-enriched-yoneda-evaluation
lem-coef-enrichment-change-adjunction
lem-coef-equifibered-bisimplicial-diagonal
lem-coef-equivalence-over-gaunt-nerve
lem-coef-ex-comparison-weak-equivalence
lem-coef-ex-infinity-finite-products
lem-coef-exact-flat-complex-set-cogeneration
lem-coef-exponential-dependent-product-representation
lem-coef-extreme-bimodule-attachment
lem-coef-face-cocone-evaluation-simplicial
lem-coef-face-cocone-splitting-refinement
lem-coef-fiberwise-arrow-target-cocartesian
lem-coef-fibrant-localized-comma-final
lem-coef-fibrant-pattern-homotopy-inverse
lem-coef-fibrant-pullback-mapping-invariance
lem-coef-fibrant-subcategory-localization
lem-coef-fibration-straightening-space-restriction
lem-coef-filtered-cocartesian-edge-persistence
lem-coef-filtered-cocartesian-section-cofinality
lem-coef-filtered-colimit-cardinal-regrouping
lem-coef-filtered-colimit-weak-equivalences
lem-coef-filtered-fiber-small-cone-lifting
lem-coef-filtered-finite-relative-cone-persistence
lem-coef-filtered-inner-horn-factorization
lem-coef-filtered-operadic-unstraightening
lem-coef-filtered-poset-cone-test
lem-coef-filtered-presentation-common-refinement
lem-coef-final-face-edge-horn-filtration
lem-coef-final-square-full-faithfulness
lem-coef-finite-colimit-approximation
lem-coef-finite-coproduct-regrouping
lem-coef-finite-core-fiber-contraction
lem-coef-finite-embedded-simplex-resolution
lem-coef-finite-inverse-tetrahedron
lem-coef-finite-limit-model-presentability
lem-coef-finite-limit-sketch-models
lem-coef-finite-marked-fibrancy-criterion
lem-coef-finite-pattern-universe-comparison
lem-coef-finite-reedy-localization
lem-coef-finite-relative-lifting-recognition
lem-coef-finite-simplicial-top-simplex-removal
lem-coef-fixed-cylinder-fibrant-target-detection
lem-coef-fixed-hammock-graph-homotopy-invariance
lem-coef-fixed-object-dg-free-model
lem-coef-fixed-object-enriched-rectification
lem-coef-fixed-object-free-arrow-adjunction
lem-coef-fixed-object-scat-bar-reordering
lem-coef-fixed-object-scat-left-proper
lem-coef-fixed-object-simplicial-free-calculus
lem-coef-fixed-object-simplicial-mapping-calculus
lem-coef-fixed-object-simplicial-sm7-free-cell
lem-coef-flat-complex-cotorsion-pairs
lem-coef-flexible-weight-enriched-lift
lem-coef-frame-bisimplicial-span
lem-coef-frame-hammock-action-naturality
lem-coef-frame-pushout-product
lem-coef-frame-source-kan-fibration
lem-coef-framed-projective-diagram-resolution
lem-coef-free-bar-cell-filtration
lem-coef-free-category-graph-nerve
lem-coef-free-category-groupoid-nerve
lem-coef-free-diagram-homotopy-density
lem-coef-free-enriched-edge-square-presentation
lem-coef-free-factor-category-normal-form
lem-coef-free-factor-hammock-comparison
lem-coef-free-factor-hammock-pushout
lem-coef-free-factor-hammock-universal-cover-reduction
lem-coef-free-module-orbit-cell-filtration
lem-coef-free-operadic-active-slice-formula
lem-coef-free-product-nerve-gluing
lem-coef-free-resolution-coproduct-augmentation
lem-coef-full-subcategory-kan-trivial-restriction
lem-coef-functor-coend-homotopy-prism
lem-coef-functor-spine-tower-mapping-descent
lem-coef-gapped-face-inner-horn-presentation
lem-coef-generalized-active-extension-criterion
lem-coef-generalized-cartesian-product-cones
lem-coef-generalized-operad-pattern-fibered
lem-coef-generalized-operadic-fibration-replacement
lem-coef-generalized-operadic-monadicity
lem-coef-generating-set-cotorsion-smallness
lem-coef-ghn-ind-presheaf-cartesian-realization
lem-coef-good-subset-enlargement
lem-coef-good-tree-idempotent-enlargement
lem-coef-graph-product-model
lem-coef-grothendieck-aspherical-base-change
lem-coef-grothendieck-classifier-localization
lem-coef-grothendieck-fibre-localization
lem-coef-groupoid-active-operation-equivalence
lem-coef-groupoidal-cofibrant-nerve-detection
lem-coef-hammock-components-localization
lem-coef-hammock-graph-colimit-presentation
lem-coef-hammock-infinity-localization
lem-coef-hammock-inverted-arrow-actions
lem-coef-hammock-pair-homotopy-invariance
lem-coef-hammock-reduction-diamond
lem-coef-hereditary-cotorsion-complex-lift
lem-coef-hocolim-reindexing-zigzags
lem-coef-hocolim-value-diagram-naturality
lem-coef-homotopy-adjunction-coherent-witnesses
lem-coef-homotopy-category-binary-products
lem-coef-homotopy-category-nerve-adjunction
lem-coef-homotopy-category-triangle-calculus
lem-coef-homotopy-equivalence-weak
lem-coef-homotopy-fractions-hammock-comparison
lem-coef-homotopy-fractions-square-criterion
lem-coef-homotopy-groups-basepoint-change
lem-coef-horn-boundary-cylinder-homeomorphism
lem-coef-horn-completion-point-colimit
lem-coef-ind-finite-poset-realization
lem-coef-ind-kappa-extension
lem-coef-ind-kappa-presentability
lem-coef-ind-presheaf-fibration-accessibility
lem-coef-ind-presheaf-small-locality-generators
lem-coef-ind-right-adjoint-coherent
lem-coef-inert-color-coslice-components
lem-coef-inert-marked-restriction-fibration
lem-coef-inert-operad-color-reconstruction
lem-coef-inert-output-relative-limit
lem-coef-inert-projection-square-fibres
lem-coef-inert-relative-tuple-cone
lem-coef-infinite-cardinal-square-power
lem-coef-infinite-cardinal-successor-regular
lem-coef-infinity-absolute-terminal-relative-colimit
lem-coef-infinity-adjunction-mapping-equivalence
lem-coef-infinity-anodyne-cocones
lem-coef-infinity-arrow-join-geometry
lem-coef-infinity-arrow-morphism-square
lem-coef-infinity-arrow-source-fibers
lem-coef-infinity-arrow-target-right-fibration
lem-coef-infinity-bicartesian-interval-adjunction
lem-coef-infinity-blunt-join-comparison
lem-coef-infinity-blunt-sharp-join-equivalence
lem-coef-infinity-boundary-extension-small-classes
lem-coef-infinity-bounded-colimit-presentation
lem-coef-infinity-cartesian-edge-transitivity
lem-coef-infinity-cartesian-fibration-pullback
lem-coef-infinity-cartesian-initial-boundary-lift
lem-coef-infinity-cartesian-mapping-criterion
lem-coef-infinity-cartesian-mapping-fiber
lem-coef-infinity-cellular-natural-equivalence
lem-coef-infinity-cocartesian-arrow-projection
lem-coef-infinity-cocartesian-base-restriction
lem-coef-infinity-cocartesian-composition-initiality
lem-coef-infinity-cocartesian-equivalence-lift
lem-coef-infinity-cocartesian-image-criterion
lem-coef-infinity-cocartesian-inner-horn-comparison
lem-coef-infinity-cocartesian-mapping-criterion
lem-coef-infinity-cocartesian-prism-comparison
lem-coef-infinity-cocartesian-transport-square
lem-coef-infinity-cocone-opposite-join-functor
lem-coef-infinity-cocone-restriction-initial
lem-coef-infinity-cofinal-colimit-restriction
lem-coef-infinity-cofinal-comma-criterion
lem-coef-infinity-cofinal-common-image
lem-coef-infinity-cofinal-coslice-calculus
lem-coef-infinity-cofinal-kappa-poset
lem-coef-infinity-cofinal-mono-right-anodyne
lem-coef-infinity-cofinality-space-test
lem-coef-infinity-colimit-gluing
lem-coef-infinity-comma-corepresentable-colimit
lem-coef-infinity-comma-equivalence-invariance
lem-coef-infinity-comma-mapping-pullback
lem-coef-infinity-common-compactness-rank
lem-coef-infinity-compact-approximation
lem-coef-infinity-compact-generated-filtered-hull
lem-coef-infinity-compact-stage-factorization
lem-coef-infinity-cone-mono-right-anodyne
lem-coef-infinity-constant-source-section-comparison
lem-coef-infinity-continuous-presheaf-representability
lem-coef-infinity-core-cylinder-restriction
lem-coef-infinity-core-kan-fibration
lem-coef-infinity-coslice-colimit-formula
lem-coef-infinity-directed-cone-cover
lem-coef-infinity-directed-union-local-colimits
lem-coef-infinity-edge-pullback-mapping-fiber
lem-coef-infinity-equivalence-anodyne-factorization
lem-coef-infinity-equivalence-arrow-path-object
lem-coef-infinity-equivalence-cancellation
lem-coef-infinity-equivalence-of-cospan-limits
lem-coef-infinity-equivalence-preserves-cocartesian-edges
lem-coef-infinity-equivalence-prism-extension
lem-coef-infinity-equivalence-section-restriction
lem-coef-infinity-essentially-small-cocones
lem-coef-infinity-fiber-cocone-simplex-extension
lem-coef-infinity-fiber-colimit-collage
lem-coef-infinity-fiber-relative-colimit-criterion
lem-coef-infinity-fiberwise-relative-join
lem-coef-infinity-filtered-cocone-apex-cofinal
lem-coef-infinity-filtered-cofinal-pullback
lem-coef-infinity-final-index-cocone-criterion
lem-coef-infinity-final-index-colimit
lem-coef-infinity-finite-coproduct-envelope
lem-coef-infinity-finite-poset-kan-extension
lem-coef-infinity-finite-shape-generation
lem-coef-infinity-fixed-boundary-functor-kan
lem-coef-infinity-fixed-cocone-opposite-limit
lem-coef-infinity-fixed-edge-prism-coherence
lem-coef-infinity-free-module-bar
lem-coef-infinity-full-essential-image
lem-coef-infinity-functor-pushout
lem-coef-infinity-grothendieck-limits-colimits
lem-coef-infinity-hom-bifunctor-functoriality
lem-coef-infinity-homotopy-precomp-equivalence
lem-coef-infinity-homotopy-pullback-pasting
lem-coef-infinity-initial-evaluation-trivial-fibration
lem-coef-infinity-inner-fibration-corner
lem-coef-infinity-inner-horn-collapse-filtration
lem-coef-infinity-inner-mapping-fiber
lem-coef-infinity-intermediate-presheaf-kan
lem-coef-infinity-isofibration-base-change
lem-coef-infinity-isofibration-exponentiation
lem-coef-infinity-isofibration-pullback-equivalence
lem-coef-infinity-isofibration-pullback-limit
lem-coef-infinity-iterated-slice-mapping
lem-coef-infinity-join-cocone-associativity
lem-coef-infinity-join-cone-calculus
lem-coef-infinity-kan-homotopy-coherent-cube-invariance
lem-coef-infinity-kan-mapping-restriction
lem-coef-infinity-lax-comma-target-fibration
lem-coef-infinity-left-fibration-initial-equivalence
lem-coef-infinity-left-pinch-comparison
lem-coef-infinity-limits-products-pullbacks
lem-coef-infinity-linear-cofinal-cone-extension
lem-coef-infinity-local-adjoint-criterion
lem-coef-infinity-local-union-cell-attachment
lem-coef-infinity-local-union-transfinite-extension
lem-coef-infinity-mapping-composition
lem-coef-infinity-mapping-excision
lem-coef-infinity-marked-coanodyne-rlp-saturation
lem-coef-infinity-marked-cocartesian-lifting
lem-coef-infinity-marked-initial-vertex
lem-coef-infinity-minimal-retract
lem-coef-infinity-monadic-bar
lem-coef-infinity-monadic-comparison
lem-coef-infinity-monadic-sifted-presentability
lem-coef-infinity-monomorphism-boundary-cells
lem-coef-infinity-normalized-final-cone
lem-coef-infinity-op-mapping-reversal
lem-coef-infinity-opposite-adjunction-data
lem-coef-infinity-opposite-subdivision-kan-zigzag
lem-coef-infinity-ordinary-pointwise-kan-extension
lem-coef-infinity-pair-groupoid-thickening
lem-coef-infinity-parameter-cone-extension
lem-coef-infinity-parameterized-evaluation-naturality
lem-coef-infinity-pinch-comparison
lem-coef-infinity-pointwise-adjoint-criterion
lem-coef-infinity-pointwise-cocartesian-transport
lem-coef-infinity-pointwise-equivalences
lem-coef-infinity-pointwise-yoneda-evaluation
lem-coef-infinity-poset-nerve-cofinal-replacement
lem-coef-infinity-precomposition-cylinder
lem-coef-infinity-presentable-presheaf-presentation
lem-coef-infinity-preserves-essential-small-colimit
lem-coef-infinity-presheaf-colimit-locality
lem-coef-infinity-presheaf-free-cocompletion
lem-coef-infinity-presheaf-ind-criterion
lem-coef-infinity-presheaf-presentability
lem-coef-infinity-presheaf-representable-slice-density
lem-coef-infinity-product-colimit-fubini
lem-coef-infinity-pullback-mapping-space
lem-coef-infinity-pushout-join-saturation
lem-coef-infinity-reflection-assembly
lem-coef-infinity-reflector-accessibility
lem-coef-infinity-relative-cocone-parameters
lem-coef-infinity-relative-colimit-completion
lem-coef-infinity-relative-cone-constant-test
lem-coef-infinity-relative-cone-equivalence
lem-coef-infinity-relative-cone-initial-corner
lem-coef-infinity-relative-exponential-restriction
lem-coef-infinity-relative-hom-evaluation
lem-coef-infinity-relative-initial-boundary
lem-coef-infinity-relative-join-cartesian-realization
lem-coef-infinity-relative-join-cocartesian-projection
lem-coef-infinity-relative-join-simplex-extension
lem-coef-infinity-relative-joyal-factorization
lem-coef-infinity-relative-kan-existence
lem-coef-infinity-relative-limit-join-boundary
lem-coef-infinity-relative-slice-sections
lem-coef-infinity-retract-colimit
lem-coef-infinity-right-adjoint-reindexing
lem-coef-infinity-right-anodyne-product
lem-coef-infinity-right-anodyne-saturation
lem-coef-infinity-right-fibration-exponentiation
lem-coef-infinity-right-fibration-fibers
lem-coef-infinity-right-prism-boundary
lem-coef-infinity-section-cylinder-cocone
lem-coef-infinity-sequential-spine
lem-coef-infinity-sharp-accessibility-enlargement
lem-coef-infinity-sifted-colimit-calculus
lem-coef-infinity-sifted-coproduct-cocompleteness
lem-coef-infinity-slice-arrow-equivalence
lem-coef-infinity-slice-equivalence-final
lem-coef-infinity-slice-right-fibration
lem-coef-infinity-small-cocone-representatives
lem-coef-infinity-small-colimit-generation
lem-coef-infinity-small-full-subcategory
lem-coef-infinity-small-localization-saturation
lem-coef-infinity-source-gluing
lem-coef-infinity-space-valued-pointwise-lan
lem-coef-infinity-split-augmentation-colimit
lem-coef-infinity-terminal-anodyne
lem-coef-infinity-terminal-pullback-criterion
lem-coef-infinity-test-equivalence-by-functor-cores
lem-coef-infinity-transport-uniqueness
lem-coef-infinity-twisted-pullback-boundary-filtration
lem-coef-infinity-twisted-pullback-identity-initial
lem-coef-infinity-universe-colimit-descent
lem-coef-infinity-weakly-contractible-cocone-colimits
lem-coef-infinity-yoneda-evaluation
lem-coef-infinity-yoneda-functor-equivalence-lift
lem-coef-infinity-yoneda-presheaf-limits
lem-coef-initial-poset-slice-restriction
lem-coef-injective-simplex-cocone-restriction
lem-coef-inner-anodyne-pointwise-lan-invariance
lem-coef-inner-anodyne-pushout-product
lem-coef-inner-anodyne-slice-categorical-equivalence
lem-coef-inner-horn-cell-generation
lem-coef-interleaved-tensor-suspension
lem-coef-interval-equivalence-cocartesian
lem-coef-interval-string-inert-extraction
lem-coef-interval-string-segal-fibration
lem-coef-inverse-gadget-categorical-contractibility
lem-coef-invertible-interval-product-projection
lem-coef-iterated-span-endomorphism-naturality
lem-coef-iterated-span-fixed-endomorphism
lem-coef-join-boundary-cubical-extension
lem-coef-join-cone-weight-cofibrancy
lem-coef-join-preserves-categorical-equivalences
lem-coef-join-pullback-simplex-extension
lem-coef-join-pushout-right-anodyne
lem-coef-join-slice-cocone-comparison
lem-coef-join-slice-diagram-isomorphisms
lem-coef-join-translation-resolution
lem-coef-joyal-cartesian-pushout-product
lem-coef-joyal-filtered-equivalences
lem-coef-joyal-fixed-object-rectification
lem-coef-joyal-functor-equivalence-test
lem-coef-joyal-generating-trivial-cofibrations
lem-coef-joyal-homotopy-exponentials
lem-coef-joyal-interval-boundary-tests
lem-coef-joyal-localization-cat-infinity
lem-coef-joyal-model-structure
lem-coef-joyal-presentable-monoidal-localization
lem-coef-joyal-quasicategory-characterizations
lem-coef-joyal-small-test-universe-invariance
lem-coef-joyal-strict-currying
lem-coef-joyal-walking-isomorphism-fibration-test
lem-coef-kan-coherent-nerve-cell-filtration
lem-coef-kan-coherent-nerve-inverse-equivalence
lem-coef-kan-coherent-nerve-quasicategory
lem-coef-kan-component-restriction-fibration
lem-coef-kan-diagram-evaluation-restriction
lem-coef-kan-diagram-localized-evaluation
lem-coef-kan-fiber-path-reversal
lem-coef-kan-fibrant-path-recognition
lem-coef-kan-fibration-arbitrary-base-fibers
lem-coef-kan-fibration-edge-fiber-transport
lem-coef-kan-fibration-slice-nerve-equivalence
lem-coef-kan-fibration-tower-limit
lem-coef-kan-homotopy-cartesian-fibration-criterion
lem-coef-kan-homotopy-cartesian-invariance
lem-coef-kan-homotopy-commuting-pullback-invariance
lem-coef-kan-homotopy-pullback-invariance
lem-coef-kan-iterated-chain-comparison
lem-coef-kan-iterated-pullback-fibrancy
lem-coef-kan-locally-trivial-realization
lem-coef-kan-minimal-factorization
lem-coef-kan-nerve-pullback-recognition
lem-coef-kan-nerve-small-products
lem-coef-kan-path-boundary-bijections
lem-coef-kan-pullback-fibration-invariance
lem-coef-kan-pullback-path-comparison
lem-coef-kan-quillen-cartesian-pushout-product
lem-coef-kan-quillen-model-right-proper-core
lem-coef-kan-quillen-right-proper
lem-coef-kan-realization-serre
lem-coef-kan-relative-nerve-left-fibration
lem-coef-kan-weak-equivalence-space-edge
lem-coef-kinjective-flat-model-fibrant
lem-coef-kspace-exponential-law
lem-coef-labelled-spine-prism-horn-calculus
lem-coef-lax-cartesian-classification
lem-coef-left-cone-restriction-cocartesian
lem-coef-left-fibration-colimit-realization
lem-coef-left-fibration-dependent-sum
lem-coef-left-fibration-relative-cylinder-lifting
lem-coef-left-fibration-right-anodyne-base-change
lem-coef-left-fibration-section-homotopy-pullback
lem-coef-linear-monad-tensor-enrichment
lem-coef-lm-algebra-fibre-reconstruction
lem-coef-lm-module-fibre-reconstruction
lem-coef-lm-prism-approximation
lem-coef-local-fiber-relative-colimit-test
lem-coef-local-transport-section-colimits
lem-coef-localization-cartesian-pullback
lem-coef-localization-cartesian-pullback-pushout
lem-coef-localization-filtered-colimit
lem-coef-localization-homotopy-category
lem-coef-localization-kan-cartesian-fibration
lem-coef-localization-monomorphic-pushout
lem-coef-localized-bifunctor-partial-derived-adjoints
lem-coef-localized-good-homotopy-test
lem-coef-locally-cofibrant-dg-restriction
lem-coef-locally-constant-presheaf-slice
lem-coef-locally-small-infinity-size-calculus
lem-coef-many-object-operad-accessibility
lem-coef-mapping-path-square-rectification
lem-coef-mapping-simplex-cone-fibers
lem-coef-mapping-simplex-final-edge
lem-coef-mapping-simplex-last-fiber-pushout
lem-coef-mapping-simplex-termwise-equivalence
lem-coef-marked-action-edge-comparison
lem-coef-marked-anodyne-lifting-calculus
lem-coef-marked-cone-adjunction-substitution
lem-coef-marked-cone-external-product
lem-coef-marked-cone-generator-calculations
lem-coef-marked-cone-straightening-quillen
lem-coef-marked-endpoint-prism-generation
lem-coef-marked-enriched-colimit-universe
lem-coef-marked-flat-categorical-equivalence-test
lem-coef-marked-internal-hom
lem-coef-marked-operadic-model-structures
lem-coef-marked-opposite-relative-calculus
lem-coef-marked-point-cartesian-model
lem-coef-marked-relative-cartesian-model
lem-coef-marked-saturation-perfect-equivalences
lem-coef-marked-sections-pointwise-limits
lem-coef-marked-sharp-anodyne-restriction
lem-coef-marked-sharp-enrichment
lem-coef-marked-triangle-cancellation
lem-coef-matrix-biclosed-monoidal-structure
lem-coef-mixed-grothendieck-products
lem-coef-mixed-join-incidence-cocones
lem-coef-mixed-mapping-cocartesian-recognition
lem-coef-model-cofibrant-colimit-comparison
lem-coef-model-colimit-localization-comparison
lem-coef-model-cylinder-whitehead
lem-coef-model-equivalence-transport
lem-coef-model-finite-limit-detection
lem-coef-model-infinity-derived-adjunction
lem-coef-model-localization-detects-weak-equivalences
lem-coef-model-localization-homotopy-classes
lem-coef-model-localization-map-surjective
lem-coef-model-over-structure
lem-coef-model-product-weak-equivalence
lem-coef-model-right-homotopy-extension
lem-coef-model-structure-determined-by-fibrant-objects
lem-coef-model-undercategory-mapping-fiber
lem-coef-model-weak-equivalence-homotopy-classes
lem-coef-model-weak-equivalence-nerve
lem-coef-model-weak-equivalences-accessible
lem-coef-module-flat-cotorsion-foundation
lem-coef-module-operad-encoding
lem-coef-module-operadic-colimit-detection
lem-coef-module-scalar-restriction-coherence
lem-coef-module-scalar-restriction-mapping
lem-coef-module-universal-arrow-criterion
lem-coef-monadic-bar-totalization
lem-coef-monoidal-block-projection-coherence
lem-coef-monoidal-compact-generators
lem-coef-monoidal-relative-adjoint-inert
lem-coef-monoidal-yoneda-embedding
lem-coef-multilinear-presheaf-kan-recognition
lem-coef-nerve-natural-homotopy-equivalence
lem-coef-nondegenerate-simplex-comma-initial
lem-coef-nondegenerate-simplex-face-poset
lem-coef-nonsymmetric-operadic-tensor-adjunction
lem-coef-nonsymmetric-operads-presentability
lem-coef-open-cover-singular-excision
lem-coef-open-cover-weak-equivalence
lem-coef-operad-groupoid-operator-map
lem-coef-operadic-active-colimit-extension-criterion
lem-coef-operadic-active-cone-boundary
lem-coef-operadic-active-incidence-comparison
lem-coef-operadic-active-lift-criterion
lem-coef-operadic-algebra-colimit-change
lem-coef-operadic-algebra-presentability
lem-coef-operadic-approximation-marked-equivalence
lem-coef-operadic-approximation-restriction
lem-coef-operadic-block-incidence-lifting
lem-coef-operadic-change-enrichment
lem-coef-operadic-cocomplete-extensions
lem-coef-operadic-colimit-active-join-boundary
lem-coef-operadic-colimit-finite-amalgamation
lem-coef-operadic-collage-comparison
lem-coef-operadic-collage-relative-overbase-equivalence
lem-coef-operadic-collage-segal-mapping-bridge
lem-coef-operadic-colorwise-sifted-colimits
lem-coef-operadic-concatenation-colimits
lem-coef-operadic-correspondence-kan-filling
lem-coef-operadic-day-convolution
lem-coef-operadic-family-cell-presentation
lem-coef-operadic-free-cocone-characterization
lem-coef-operadic-free-cocone-criterion
lem-coef-operadic-free-extension
lem-coef-operadic-inert-active-factorization
lem-coef-operadic-inert-factor-equivalence
lem-coef-operadic-localization-operation-criterion
lem-coef-operadic-minimal-interval-reflection
lem-coef-operadic-operation-lifting-fiber
lem-coef-operadic-operation-segal-product
lem-coef-operadic-typec-incidence-cone
lem-coef-operadic-weak-approximation-algebras
lem-coef-opposite-join-comma-comparison
lem-coef-ordered-simplex-cone-evaluation
lem-coef-ordinal-inverse-diagram-model
lem-coef-ordinal-latching-diagram-lifting
lem-coef-ordinary-bar-evaluation-naturality
lem-coef-ordinary-comma-retraction-naturality
lem-coef-ordinary-nerve-discrete-hom-comparison
lem-coef-ordinary-nerve-functor-comparison
lem-coef-ordinary-presheaf-local-presentability
lem-coef-ordinary-two-sided-bar-comparison
lem-coef-parametric-comma-fiber-comparison
lem-coef-parametric-discrete-yoneda
lem-coef-parametric-straightening-mapping-spaces
lem-coef-parametric-universal-arrows
lem-coef-parametrized-adjunction-corner-lifting
lem-coef-partial-cellular-root-descent-extension
lem-coef-pattern-anodyne-generators
lem-coef-pattern-anodyne-lifting-products
lem-coef-pattern-fibered-edge-detection
lem-coef-pattern-generator-product-cells
lem-coef-pattern-induced-fibration-test
lem-coef-pattern-marked-mapping-components
lem-coef-pattern-marking-cancellation
lem-coef-pattern-section-core-identification
lem-coef-perfect-weak-equivalence-model-recognition
lem-coef-pinched-cube-latching
lem-coef-pinched-rigidification-resolution
lem-coef-planar-multilinear-extension
lem-coef-point-family-q-counit-identification
lem-coef-pointed-model-stability
lem-coef-pointwise-compact-diagrams
lem-coef-pointwise-constant-target-square-assembly
lem-coef-pointwise-lan-mapping-property
lem-coef-polytope-boundary-radial-extension
lem-coef-poset-filtered-cofibrant-resolution
lem-coef-poset-relative-vertex-insertion
lem-coef-presentable-cardinal-enlargement
lem-coef-presentable-cartesian-fibration
lem-coef-presentable-cellular-factorization
lem-coef-presentable-infinity-adjoints
lem-coef-presentable-presentation-comparison
lem-coef-presentable-right-adjoint-accessible
lem-coef-presentable-small-object-factorization
lem-coef-presentation-enlargement-retains-diagram
lem-coef-presheaf-bounded-intersection-replacement
lem-coef-presheaf-cylinder-model-recognition
lem-coef-presheaf-external-product-kan
lem-coef-presheaf-naive-fibration-whitehead
lem-coef-presheaf-simplex-hocolim-resolution
lem-coef-presheaf-weak-mono-bounded-enlargement
lem-coef-projective-chains-monoidal-model
lem-coef-projective-cochain-monoidal-model
lem-coef-projective-diagram-simplicial-descent
lem-coef-projective-diagram-universe-cofibrancy
lem-coef-projective-frame-weighted-coend
lem-coef-proper-word-colimit-invariance
lem-coef-pseudofunctor-split-family-strictification
lem-coef-qrep-moduli-pullback
lem-coef-quasicategory-classification-realization
lem-coef-quasicategory-edge-triangle-presentation
lem-coef-quasicategory-full-subcategory-core-equivalence
lem-coef-quasicategory-invertible-interval
lem-coef-quasicategory-labelled-coproduct-equivalences
lem-coef-quasicategory-simplex-join-attachment
lem-coef-quillen-b-comma-homotopy-fiber
lem-coef-quillen-b-discrete-fibration-base-change
lem-coef-quillen-b-path-minmax-homotopy
lem-coef-quillen-derived-counit-criterion
lem-coef-quillen-fibrant-test
lem-coef-quillen-section-rectification
lem-coef-realization-finite-limits
lem-coef-reduced-word-prepend-action
lem-coef-reedy-colimit-comparison
lem-coef-reedy-homotopy-segal-comparison
lem-coef-reedy-left-frame-comparison
lem-coef-reedy-model-structure
lem-coef-reedy-realization-homotopy-invariance
lem-coef-reedy-realization-prism
lem-coef-reedy-simplicial-frame-comparison
lem-coef-reflection-inverting-limit-restriction
lem-coef-relative-cartesian-equivalence-saturation
lem-coef-relative-categorical-cylinder-criterion
lem-coef-relative-comma-coordinate-contraction
lem-coef-relative-cone-presheaf-fibers
lem-coef-relative-coslice-homotopy-pullback-test
lem-coef-relative-cut-nerve-diagrams
lem-coef-relative-final-apex-join-boundary
lem-coef-relative-functor-cocartesian-classifier
lem-coef-relative-grothendieck-localization
lem-coef-relative-join-fixed-source-prism
lem-coef-relative-join-left-kan-reduction
lem-coef-relative-join-prism-comparison
lem-coef-relative-limit-initial-components
lem-coef-relative-limit-join-slice-recognition
lem-coef-relative-marked-anodyne-calculus
lem-coef-relative-marked-anodyne-replacement
lem-coef-relative-nerve-cylinder-contraction
lem-coef-relative-nerve-symmetric-family
lem-coef-relative-operadic-output-mapping
lem-coef-relative-operadic-output-substitution-coherence
lem-coef-relative-operadic-terminal-active-mapping
lem-coef-relative-planar-operation-extension
lem-coef-relative-right-kan-restriction
lem-coef-relative-right-kan-universal-restriction
lem-coef-relative-symmetric-monoidal-localization
lem-coef-relative-triple-mapping-space-pullback
lem-coef-relative-undercategory-limit-creation
lem-coef-representable-right-fibration-classifier
lem-coef-represented-family-slice-fibration
lem-coef-resolution-interval-tensor
lem-coef-rezk-diagonal-sharp
lem-coef-rezk-explicit-completion
lem-coef-rezk-local-model
lem-coef-right-anodyne-lifting-characterization
lem-coef-right-anodyne-mono-cancellation
lem-coef-right-approximation-slice
lem-coef-right-decalage-augmentation-prism
lem-coef-right-decalage-index-calculus
lem-coef-right-fibration-categorical-base-change
lem-coef-right-fibration-cone-section-criterion
lem-coef-right-fibration-constant-right-kan
lem-coef-right-fibration-contractible-fibers
lem-coef-right-fibration-fiberwise-kan
lem-coef-right-fibration-inner-horn-pullback
lem-coef-right-fibration-pushout-mapping-square
lem-coef-right-fibration-section-limit
lem-coef-right-straightening-fiber-comparison
lem-coef-rigidification-boundary-cube
lem-coef-rigidification-component-postcomposition
lem-coef-rigidification-equivalence-detection
lem-coef-rigidification-identity-action
lem-coef-rigidification-postcomposition-comparison
lem-coef-scat-arrow-cell-word-filtration
lem-coef-scat-bergner-left-proper-pushouts
lem-coef-scat-diagram-factorization-uniform-bound
lem-coef-scat-fixed-object-pushout-comparison
lem-coef-scat-framed-diagram-adjunction
lem-coef-scat-injective-universe-generators
lem-coef-scat-uniform-presentability
lem-coef-segal-cartesian-exponent
lem-coef-segal-categorical-constancy
lem-coef-segal-categorical-equivalence-dk
lem-coef-segal-composition-equivalences
lem-coef-segal-cotensor-evaluation-dk
lem-coef-segal-dk-diagonal-equivalence
lem-coef-segal-dk-two-out-of-six
lem-coef-segal-equivalence-classifier
lem-coef-segal-equivalence-outer-horn
lem-coef-segal-equivalence-subspace-filtered
lem-coef-segal-external-local-equivalences
lem-coef-segal-finite-cover-descent
lem-coef-segal-homotopy-category-components
lem-coef-segal-interval-cover
lem-coef-segal-inverse-evaluation
lem-coef-segal-realization-coherent-nerve
lem-coef-segal-space-inner-anodyne-locality
lem-coef-segal-spine-interval-test
lem-coef-segal-vertical-restriction-inner
lem-coef-selectively-marked-terminal-cylinder
lem-coef-serre-disk-lift-boundary-bijection
lem-coef-serre-homotopy-exact-sequence
lem-coef-sharp-filtered-poset-subsets
lem-coef-sharp-pullback-calculus
lem-coef-sharp-pushout-attachment-comparison
lem-coef-sharp-simplex-criterion
lem-coef-sharp-special-colimit-gluing
lem-coef-sheaf-flat-model
lem-coef-sifted-fixed-object-hocolimit
lem-coef-sifted-good-diagram-calculus
lem-coef-sifted-nerve-index-calculus
lem-coef-signed-word-boundary-pushout
lem-coef-simple-inner-anodyne-base-change
lem-coef-simplex-category-last-vertex
lem-coef-simplex-first-vertex-cocone-equivalence
lem-coef-simplex-last-vertex-cocone-equivalence
lem-coef-simplex-nerve-comma-pullback
lem-coef-simplicial-arrow-attachment-localization
lem-coef-simplicial-bar-latching-decomposition
lem-coef-simplicial-bar-projective-resolution
lem-coef-simplicial-bifibrant-localization
lem-coef-simplicial-boundary-collapse-test
lem-coef-simplicial-bousfield-model-structure
lem-coef-simplicial-category-degreewise-colimits
lem-coef-simplicial-derived-exponential
lem-coef-simplicial-derived-hom-adjunction
lem-coef-simplicial-derived-pushout-mapping
lem-coef-simplicial-diagram-equivalence-classes
lem-coef-simplicial-edge-inversion-pushout
lem-coef-simplicial-fixed-object-monic-cofibration
lem-coef-simplicial-fully-faithful-homotopy-image
lem-coef-simplicial-grothendieck-hocolimit
lem-coef-simplicial-groupoid-models
lem-coef-simplicial-interval-cell-stability
lem-coef-simplicial-interval-lifting
lem-coef-simplicial-inversion-product-parameter
lem-coef-simplicial-inversion-universal-property
lem-coef-simplicial-invertible-arrow-pushout
lem-coef-simplicial-latching-degenerate-subset
lem-coef-simplicial-local-bounded-lifting
lem-coef-simplicial-local-equivalences-accessible
lem-coef-simplicial-localization-comparison-calculus
lem-coef-simplicial-localization-essential-image
lem-coef-simplicial-localization-existence
lem-coef-simplicial-mapping-localization
lem-coef-simplicial-marked-cylinder-comparison
lem-coef-simplicial-model-arrow-lifting
lem-coef-simplicial-model-coherent-diagrams
lem-coef-simplicial-model-nerve-localization
lem-coef-simplicial-model-target-test
lem-coef-simplicial-natural-equivalence-homotopy
lem-coef-simplicial-operator-nerve
lem-coef-simplicial-opposite-homotopy-calculus
lem-coef-simplicial-presheaf-localization-comparison
lem-coef-simplicial-presheaf-projective-model
lem-coef-simplicial-projective-model-calculus
lem-coef-simplicial-pullback-equivalence
lem-coef-simplicial-realization-cylinder
lem-coef-simplicial-realization-extra-degeneracy
lem-coef-simplicial-relative-homotopy-invariance
lem-coef-simplicial-right-fibration-presentation
lem-coef-simplicial-shape-categorification
lem-coef-simplicial-simplex-colimit-product
lem-coef-simplicial-sm7-generator-extension
lem-coef-simplicial-small-chunks
lem-coef-simplicial-space-localization-interval-criterion
lem-coef-simplicial-space-reedy-cartesian
lem-coef-simplicial-space-small-subobjects
lem-coef-simplicial-strict-pushout-derived-comparison
lem-coef-simplicial-undercategory-model
lem-coef-simplicial-walking-groupoid-components
lem-coef-single-horn-relative-completion
lem-coef-singular-bar-realization-cylinder
lem-coef-singular-counit-weak-equivalence
lem-coef-singular-span-bar-cylinder-gluing
lem-coef-slice-cartesian-colimit-criterion
lem-coef-slice-cone-prism-simplicial
lem-coef-slice-straightening-counit
lem-coef-small-cellular-tree-descent
lem-coef-small-cocartesian-model
lem-coef-small-cotorsion-model-recognition
lem-coef-small-diagram-model-rectification
lem-coef-small-direct-colimit-lifting
lem-coef-small-family-accessibility-rank
lem-coef-small-inner-horn-completion
lem-coef-small-monoidal-full-subcategory
lem-coef-small-right-adjoint-diagram-compact-model
lem-coef-small-right-lifting-accessibility
lem-coef-small-saturated-arrow-accessibility
lem-coef-small-saturated-coslice-presentability
lem-coef-small-simplicial-diagram-cardinality
lem-coef-small-tree-presentable-vertices
lem-coef-smith-model-recognition
lem-coef-smith-small-saturated-intersection
lem-coef-sorted-simplicial-algebra-model
lem-coef-space-bimodule-collage
lem-coef-space-constant-diagram-limit
lem-coef-space-contractible-fiber-equivalence
lem-coef-space-geometric-descent
lem-coef-space-kan-fibration-fiber-criterion
lem-coef-space-path-fibration-replacement
lem-coef-space-point-cocone-criterion
lem-coef-space-presheaf-cocompletion
lem-coef-space-presheaf-presentability
lem-coef-space-presheaf-right-kan-mapping-formula
lem-coef-space-transport-classification
lem-coef-space-universal-colimits
lem-coef-space-universe-repletion
lem-coef-space-valued-straightening
lem-coef-space-yoneda-density
lem-coef-spaces-homotopy-fiber-detection
lem-coef-spaces-kappa-limit-filtered-colimit
lem-coef-spaces-slice-cartesian-closure
lem-coef-spaces-small-colimits-universe
lem-coef-spatial-mapping-interchange
lem-coef-special-hammock-reduction
lem-coef-special-resolution-zigzag-nerve
lem-coef-special-resolutions-aspherical
lem-coef-sphere-mapping-weak-equivalence
lem-coef-spine-cancellation-inner-horns
lem-coef-split-coproduct-bar-extra-degeneracy
lem-coef-split-functor-coend-filtration
lem-coef-sset-anodyne-pushout-product
lem-coef-sset-cellular-comparison
lem-coef-sset-gluing-filtered-equivalences
lem-coef-standard-simplex-realization-contraction
lem-coef-strict-bimodule-rectification
lem-coef-strict-diagram-evaluation-conservative
lem-coef-strict-intrinsic-right-fibration-slices
lem-coef-strong-monoidal-operation-morphism-lifting
lem-coef-strong-retraction-idem-colimit
lem-coef-subdivision-anodyne
lem-coef-subdivision-ex-homotopy-adjunction
lem-coef-subdivision-face-poset-calculus
lem-coef-subdivision-last-vertex-equivalence
lem-coef-suspension-square-comparison
lem-coef-symmetric-cartesian-cylinder-edge-comparison
lem-coef-symmetric-cartesian-cylinder-slice-comparison
lem-coef-symmetric-family-active-slice-calculus
lem-coef-symmetric-family-block-assembly
lem-coef-symmetric-family-block-restriction
lem-coef-symmetric-family-inert-active-orthogonality
lem-coef-symmetric-family-inert-cone-initiality
lem-coef-symmetric-inert-active-orthogonality
lem-coef-symmetric-inert-projection-detection
lem-coef-symmetric-monoidal-segal-classification
lem-coef-symmetric-operadic-active-seed-attachment
lem-coef-symmetric-operadic-base-matching
lem-coef-symmetric-operadic-extension-boundaries
lem-coef-symmetric-operadic-fibrant-objects
lem-coef-symmetric-operadic-fibration-recognition
lem-coef-symmetric-operadic-left-horn-filling
lem-coef-symmetric-operadic-mapping-cylinder
lem-coef-symmetric-relative-product-comparison
lem-coef-symmetric-weak-approximation-algebras
lem-coef-system-localization-universal
lem-coef-tensor-coend-skeletal-pushouts
lem-coef-terminal-comparison-coherence
lem-coef-terminal-local-kan-corepresentability
lem-coef-thomason-grothendieck-comparison
lem-coef-topological-serre-model
lem-coef-transfinite-isofibration-limit
lem-coef-tree-leaf-zigzag-retraction
lem-coef-tree-zigzag-finite-subtree-colimit
lem-coef-triangular-bar-excision
lem-coef-triangular-cofibrant-resolution
lem-coef-triangular-top-deletion-anodyne
lem-coef-trivial-fibration-fraction-model
lem-coef-truncated-coend-skeleton-image
lem-coef-tuple-operad-incidence
lem-coef-twisted-arrow-equivalence-invariance
lem-coef-twisted-arrow-join-horn
lem-coef-twisted-arrow-left-fibration
lem-coef-two-object-localization-pullback
lem-coef-two-sided-bar-leading-unit-extension
lem-coef-two-sided-bar-regular-word-identification
lem-coef-two-sided-coherent-bar-construction
lem-coef-two-sided-simplicial-grothendieck-invariance
lem-coef-universal-arrow-comparison
lem-coef-universal-cocone-restriction-right-anodyne
lem-coef-universal-left-fibration-identity
lem-coef-universal-localization-degenerate-edges
lem-coef-universal-localization-pushout
lem-coef-unmarked-cone-model-comparison
lem-coef-unmarked-relative-nerve-cone-comparison
lem-coef-unmarked-straightening-quillen
lem-coef-unmarked-straightening-target-change
lem-coef-unstraightening-homotopy-descent
lem-coef-unstraightening-homotopy-descent-gluing
lem-coef-unstraightening-simplex-dk-equivalence
lem-coef-unstraightening-simplex-pointwise
lem-coef-unstraightening-simplex-transport
lem-coef-unstraightening-strict-base-change
lem-coef-walking-adjunction-cell-filtration
lem-coef-walking-isomorphism-alternating-horn-filtration
lem-coef-walking-isomorphism-edge-anodyne
lem-coef-walking-module-weight-cells
lem-coef-weak-cartesian-structure-restriction
lem-coef-weak-equivalence-representable-local-model
lem-coef-weak-retraction-coherent-extension
lem-coef-weak-saturation-tree-presentation
lem-coef-weighted-coend-skeletal-filtration
lem-coef-zigzag-concatenation-invariance
lem-pur-system-section-cone
lem-pur-system-section-suspension
```

### Applicable route-pivot repair note

```json
{
 "state": "released",
 "stage": "1",
 "item": "lem-coef-semilinear-derived-sections",
 "by": "L (route pivot, decision of the human 2026-10-18)",
 "date": "2026-10-18",
 "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)",
 "note": "route pivot (the human, 2026-10-18): re-split on the ordinary derived route; restate the statement; machinery cited at step 1: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 2: lem-coef-quillen-section-rectification; step 3: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 4: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 5: lem-coef-dg-derived-quillen-calculus, lem-coef-kinjective-flat-model-fibrant, lem-coef-quillen-section-rectification; step 6: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 7: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-sheaf-flat-model; step 8: lem-coef-dg-derived-quillen-calculus, lem-coef-kinjective-flat-model-fibrant; step 9: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 10: lem-coef-dg-derived-quillen-calculus",
 "reason": "Route decision (the human, 2026-10-18): the infinity-categorical / dg / model-category route that stage-1 workers built for the l-adic coefficient work (about 1300 nodes below the cone hubs def-cbc-enhanced-diagrams-cones, lem-cbc-enhanced-functor-cone-calculus and the enhanced part of lem-coef-semilinear-derived-sections, mostly absent from Mathlib) was judged far larger than the ordinary derived route, and is no longer reached from the targets. Use the ordinary derived route: the coefficient category is the ordinary derived category D(Tow) of the ringed topos of towers [det-sp-coefficient-towers-abelian, sk-def-sp-coefficient-towers], Rlim is a right derived functor; right adjoints of compact-support functors come from Brown representability [lem-grothendieck-derived-brown-right-adjoint, lem-pc-brown-representability-right-adjoint, sk-prop-sf-existence]; their levels and coefficient maps come from uniqueness of adjoints [det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients] together with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels]; gluing goes by uniqueness of representing pairs [det-sp-tower-gluing]; flat models are replaced by K-flat resolutions (Stacks 06YS) [lem-pc-kflat-resolution, lem-pc-kflat-closure, lem-pc-kflat-total-tensor-associativity, lem-kun-derived-tensor-well-defined]; filtered work uses the ordinary filtered derived category (Stacks 09QJ) [lem-coef-dg-abc-homotopy-category-triangulated]. Exactness/shift facts for ordinary derived functors: [lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-sf-triangulated-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism]; ordinary mates [def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting]. This note is guidance with its evidence, not a lock: another route is acceptable if it avoids that machinery and the split report justifies it. Do not cite any node of the machinery listed under 'machinery_cited'.\n\nNODE-SPECIFIC REPAIR (lem-coef-semilinear-derived-sections):\nRestate on the ORDINARY derived category D(S(B)) of strict semilinear systems with levelwise operations. Drop from the statement: the enhanced derived module categories, homotopy coherent semilinear sections and the enhanced equivalence (clauses citing lem-coef-dg-derived-quillen-calculus and lem-coef-quillen-section-rectification; these stmt_deps were removed). Keep: componentwise exactness, evaluations D(S(B))->D(B_n) computed componentwise, normalized (cartesian) objects defined by M_m (x)^L B_n -> M_n invertible [lem-pur-derived-change-of-rings], detection of isomorphisms by evaluations, and the levelwise derived operations (exact inverse image, Ru_*, j_!, coefficient change, derived tensor, RHom) with their evaluation formulas and the exchange/projection maps as unit-counit words. 48 of the 55 citers use only this ordinary part (checked 2026-10-18). Do NOT promise an enhanced right adjoint on cartesian sections: the five citers needing right adjoints (lem-coef-cartesian-section-adjoint-mates, lem-coef-finite-adjunction-diagram-realization, lem-sf-constructible-exceptional-adjunction-coefficients, lem-pur-finite-coefficient-adjoint-comparisons, lem-pur-condensed-exceptional-reconstruction) are returned separately and get them from Brown representability. Per step: step 1 (derived coefficient extension via the flat model and dg Quillen calculus) -> K-flat resolutions [lem-pc-kflat-resolution, lem-weil-pbc-ringed-topos-kflat-pullback, lem-pur-derived-change-of-rings, lem-weil-pbc-site-flat-quotient-tensor-ses]; steps 2-3 (section rectification, cartesian criterion) -> cohomology of a complex of systems is computed componentwise, so D(S(B)) and its evaluations need no enhanced comparison; the cartesian criterion is the levelwise statement; steps 4-6 (inverse image, direct image, extension by zero on systems) -> levelwise derived functors on the ringed topos of systems [lem-weil-pbc-ringed-topoi-derived-pullback, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, prop-pur-kinjective-resolutions-exist, lem-pur-site-restriction-module-adjunction-exact, lem-weil-pbc-ringed-slice-extension-tensor]; step 7 (tensor, coefficient change) -> K-flat tensor [lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-pc-tensor-complex-sheaves]; step 8 (RHom) -> K-injective RHom [def-pur-derived-internal-hom, lem-pur-rhom-well-defined]; steps 9-10 (exchange and projection words) -> ordinary unit/counit words of the derived adjunctions [def-weil-pbc-adjunction-mate], whose evaluations are the levelwise maps; step 0 stays.\n\nLocations that cite the machinery (0-based proof steps as in the node file): step 1: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 2: lem-coef-quillen-section-rectification; step 3: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 4: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 5: lem-coef-dg-derived-quillen-calculus, lem-coef-kinjective-flat-model-fibrant, lem-coef-quillen-section-rectification; step 6: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 7: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-sheaf-flat-model; step 8: lem-coef-dg-derived-quillen-calculus, lem-coef-kinjective-flat-model-fibrant; step 9: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 10: lem-coef-dg-derived-quillen-calculus. Statement citations of the machinery: none.\n\nNon-machinery children of the old split, to reuse in the re-split where they still fit: def-pc-cochain-complex-modules, def-pc-kflat-complex, def-pc-sheaf-restrict-scalars, def-pc-tensor-complex-sheaves, def-pur-derived-internal-hom, def-weil-abstract-derived-category, def-weil-pbc-adjunction-mate, def-weil-pbc-sites-and-cohomology, def-weil-sheaf-of-modules-category, lem-pur-derived-change-of-rings, lem-pur-rhom-well-defined, lem-pur-site-restriction-module-adjunction-exact, lem-weil-pbc-ringed-slice-extension-tensor, lem-weil-pbc-ringed-topoi-derived-pullback, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-ringed-topoi-module-adjunction, lem-weil-pbc-ringed-topos-kflat-pullback, lem-weil-pbc-site-flat-quotient-tensor-ses, prop-pur-kinjective-resolutions-exist.\n\nReturned WITHOUT keep_plan: the old plan's children are not reached until the new split cites them. The old proof text stays in the node file as a starting point; the statement is to be restated as described above.",
 "machinery_cited": [
  "lem-coef-dg-derived-quillen-calculus",
  "lem-coef-kinjective-flat-model-fibrant",
  "lem-coef-quillen-section-rectification",
  "lem-coef-sheaf-flat-model"
 ],
 "machinery_steps": [
  {
   "step": 1,
   "cites": [
    "lem-coef-dg-derived-quillen-calculus",
    "lem-coef-sheaf-flat-model"
   ]
  },
  {
   "step": 2,
   "cites": [
    "lem-coef-quillen-section-rectification"
   ]
  },
  {
   "step": 3,
   "cites": [
    "lem-coef-dg-derived-quillen-calculus",
    "lem-coef-quillen-section-rectification"
   ]
  },
  {
   "step": 4,
   "cites": [
    "lem-coef-dg-derived-quillen-calculus",
    "lem-coef-sheaf-flat-model"
   ]
  },
  {
   "step": 5,
   "cites": [
    "lem-coef-dg-derived-quillen-calculus",
    "lem-coef-kinjective-flat-model-fibrant",
    "lem-coef-quillen-section-rectification"
   ]
  },
  {
   "step": 6,
   "cites": [
    "lem-coef-dg-derived-quillen-calculus",
    "lem-coef-sheaf-flat-model"
   ]
  },
  {
   "step": 7,
   "cites": [
    "lem-coef-dg-derived-quillen-calculus",
    "lem-coef-quillen-section-rectification",
    "lem-coef-sheaf-flat-model"
   ]
  },
  {
   "step": 8,
   "cites": [
    "lem-coef-dg-derived-quillen-calculus",
    "lem-coef-kinjective-flat-model-fibrant"
   ]
  },
  {
   "step": 9,
   "cites": [
    "lem-coef-dg-derived-quillen-calculus",
    "lem-coef-quillen-section-rectification"
   ]
  },
  {
   "step": 10,
   "cites": [
    "lem-coef-dg-derived-quillen-calculus"
   ]
  }
 ],
 "keep_children": [
  "def-pc-cochain-complex-modules",
  "def-pc-kflat-complex",
  "def-pc-sheaf-restrict-scalars",
  "def-pc-tensor-complex-sheaves",
  "def-pur-derived-internal-hom",
  "def-weil-abstract-derived-category",
  "def-weil-pbc-adjunction-mate",
  "def-weil-pbc-sites-and-cohomology",
  "def-weil-sheaf-of-modules-category",
  "lem-pur-derived-change-of-rings",
  "lem-pur-rhom-well-defined",
  "lem-pur-site-restriction-module-adjunction-exact",
  "lem-weil-pbc-ringed-slice-extension-tensor",
  "lem-weil-pbc-ringed-topoi-derived-pullback",
  "lem-weil-pbc-ringed-topoi-derived-pushforward-composition",
  "lem-weil-pbc-ringed-topoi-derived-tensor-pullback",
  "lem-weil-pbc-ringed-topoi-module-adjunction",
  "lem-weil-pbc-ringed-topos-kflat-pullback",
  "lem-weil-pbc-site-flat-quotient-tensor-ses",
  "prop-pur-kinjective-resolutions-exist"
 ],
 "removed_stmt_deps": [
  "lem-coef-dg-derived-quillen-calculus",
  "lem-coef-quillen-section-rectification"
 ],
 "statement_restated": true
}
```

### Pre-pivot proof and comparison

The immutable pre-pivot item record was recovered from the retained pre-pivot snapshot blob `1c045a1e16ea2b73ade26f6edecbac3350094c07` (13 proof steps). The current item proof is byte-identical to the ordinary-route snapshot blob `21f7a5ed7ef4de4e74af55c341a496fbaac44f45`; the pre-pivot record differs in the statement display, proof-origin place, and Steps 1, 5, 11, and 13. Steps 2, 3, 4, 6, 7, 8, 9, 10, and 12 are byte-identical. The exact pre-pivot statement and all 13 pre-pivot proof steps follow.

```json
{
 "statement": "Fix $k=\\overline{\\mathbf F}_q$, a prime $\\ell\\ne\\operatorname{char}k$, a finite extension $E/\\mathbf Q_\\ell$, its valuation ring $R$, uniformizer $t$, and $A_n=R/t^n$, $n\\ge1$ [def-weil-l-adic-coefficient-extension]. Schemes are separated finite type over $k$, with their small pro-etale sites [def-weil-scheme-morphism-properties, def-weil-pbc-proetale-site]. Put $\\widehat R_T=\\lim_n(A_n)_T$. Use the strict semilinear system category $\\mathscr S_T$, reduction $\\mathcal R_T$, total limit $\\mathcal L_T$, and actual unit and counit of [lem-coef-derived-system-evaluation-calculus]. Let $\\mathcal T_T=\\operatorname{Fun}(\\mathbf N_{\\ge1}^{op},\\operatorname{Mod}(\\underline R_T))$ and use its derived category, strict reduction $\\mathcal R_T^{\\mathcal T}$ and total limit $\\mathcal L_T^{\\mathcal T}$ of [lem-sf-cbc-compact-support-composition-limit]. Let $U_T:D(\\mathscr S_T)\\to D(\\mathcal T_T)$ be exact termwise restriction along $\\underline R_T\\to(A_n)_T$, and let $H_T$ be restriction along $\\underline R_T\\to\\widehat R_T$, an equivalence on complete objects [lem-weil-pbc-constant-completion-equivalence].\n\nTake either a proper map $p:V\\to T$ and $A=S_p$, or a quasi-compact open immersion $j:V\\hookrightarrow T$ and $A=J_j$, with the simultaneous section operations of [lem-coef-semilinear-derived-sections]. Let $M$ be a derived-complete constructible integral complex on $V$; require its input and output systems to have compatible etale-origin witnesses and normalized reductions with cohomological and finite Tor amplitudes in common finite intervals, exactly as in [lem-sf-generator-reduction-coherence]. Let $A_{\\rm int}$ be integral proper direct image in the first case and localized completed-ring open extension in the second [lem-sf-integral-open-reduction-comparison]. Let $r_{A,M}:\\mathcal R_T(A_{\\rm int}M)\\to A\\mathcal R_VM$ be the specified basic coefficient comparison of [lem-sf-generator-reduction-coherence]. On constant coordinates put $A_c=Rp_*$ or $J_j^c=C_TJ_j$ respectively, and $\\widetilde A=R_p^{\\mathcal T}$ or $J_j$. Here $C_T=\\mathcal L_T^{\\mathcal T}\\mathcal R_T^{\\mathcal T}$ has its quotient-tower completion unit. Let $q_{A,HM}$ be precisely the one-letter comparison of [lem-sf-cbc-compact-support-composition-limit]: the diagram-site counit-tensor projection map for proper direct image, or the completed-open comparison defined by reduction of the completion unit.\n\nUse the canonical derived scalar-restriction identifications $U_TA\\cong\\widetilde A U_V$, and $\\rho_M:U_V\\mathcal R_VM\\cong\\mathcal R_V^{\\mathcal T}H_VM$, induced by the single strict quotient diagram and tensor reassociation. Write $\\sigma_{A,M}:H_TA_{\\rm int}M\\xrightarrow{\\sim}A_cH_VM$ for the identification by the canonical proper direct-image scalar comparison, respectively the completed-open identification fixed by the completion unit. Then the two maps from $U_T\\mathcal R_T(A_{\\rm int}M)$ to $\\widetilde A\\mathcal R_V^{\\mathcal T}(H_VM)$ are equal:\n$$ (\\widetilde A\\rho_M)\\circ(U_TA\\cong\\widetilde A U_V)\\circ U_T(r_{A,M})\n =q_{A,H_VM}\\circ\\mathcal R_T^{\\mathcal T}(\\sigma_{A,M})\\circ\\rho_{A_{\\rm int}M}.$$\nThe scalar-restriction operation comparisons intertwine the units and counits of the proper inverse-image/direct-image and open-extension/restriction adjunctions, with inverse image the exact termwise inverse image of [lem-coef-semilinear-derived-sections]. The identifications and the displayed equality are natural in the derived strict-tower category, including the quotient transitions. No compactification-composition comparison is asserted.",
 "proof": [
  {
   "text": "Realize strict systems as modules on one diagram topos. On the site $\\mathbf N_{\\ge1}\\times T_{\\rm proet}$ of [lem-weil-pbc-diagram-site-realization], put $\\mathcal A_T(n,W)=(A_n)_T(W)$ and $\\mathcal B_T=\\Delta\\underline R_T$. The sheaf condition is imposed at each fixed $n$, so a module over $\\mathcal A_T$ is exactly a strict semilinear system: its restriction in the integer direction is the specified semilinear transition. This is an additive exact identification, also on complexes and derived localizations. The ring map $\\mathcal B_T\\to\\mathcal A_T$ defines an identity-topos ringed morphism $v_T$ with derived pullback $E_T=-\\otimes^L_{\\mathcal B_T}\\mathcal A_T$ and exact direct image $U_T$, adjoint with the specified tensor unit/counit by [lem-pur-sheaf-ring-derived-coefficient-adjunction]. For a geometric map $f:V\\to T$, inverse image on diagram sheaves is termwise $f^{-1}$, with termwise right adjoint; their Hom bijection commutes with the transition maps by naturality. Since $f^{-1}(A_n)_T=(A_n)_V$ and $f^{-1}\\underline R_T=\\underline R_V$, this gives ringed morphisms $f_a,f_b$ with exact pullbacks $F_a,F_b$ and $v_Tf_a=f_bv_V$. The operation $G_a=Rf_{a*}$ is the $S_f$ of [lem-coef-semilinear-derived-sections]: both are right adjoint to the same exact section inverse image. Write $G_b=Rf_{b*}$.",
   "uses": [
    "lem-weil-pbc-diagram-site-realization",
    "lem-weil-pbc-ringed-topoi-module-adjunction",
    "lem-weil-pbc-ringed-projection-mate-exact",
    "lem-coef-semilinear-derived-sections",
    "lem-pur-sheaf-ring-derived-coefficient-adjunction"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md",
    "place": "coefficient comparisons on the single quotient diagram"
   }
  },
  {
   "text": "Apply [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] to the two factorizations of the common ringed morphism $v_Tf_a=f_bv_V$. Since $Rv_{T*}=U_T$ and $Rv_{V*}=U_V$ are exact restriction, it gives a canonical isomorphism\n$$d:U_TG_a\\xrightarrow{\\sim}G_bU_V.$$\nThis proves the required proper system operation comparison without asserting that restriction along $R\\to A_n$ preserves K-injectives. Use [lem-sfb-ringed-derived-monoidal-comparisons] to normalize the corresponding pullback isomorphism\n$$c:F_aE_T\\xrightarrow{\\sim}E_VF_b.$$\nIts two composite adjunctions are identified by $c,d$, including their units and counits. These theorems apply on the small diagram sites just constructed and to unbounded complexes and nonflat structural ring maps. In particular $d$ is an actual derived strict-tower comparison, not a collection of evaluated arrows.",
   "uses": [
    "lem-weil-pbc-ringed-topoi-derived-pushforward-composition",
    "lem-sfb-ringed-derived-monoidal-comparisons"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/sites-cohomology.tex",
    "place": "Tags 0D6E (lemma-derived-pushforward-composition), 0D6D (lemma-derived-pullback-composition), 07A6 (lemma-adjoint), and 0FPI (lemma-adjoints-push-pull-compatibility); use the adjunction-normalized comparisons of the cited node"
   }
  },
  {
   "text": "Identify the geometric inverse-image comparison $a:F_bU_T\\xrightarrow{\\sim}U_VF_a$ with the mate of $c^{-1}$ across $E_V\\dashv U_V$ and $E_T\\dashv U_T$. If $z_T:E_TU_T\\to1$ is the scalar counit, this mate is the scalar adjunct of\n$$E_VF_bU_TX\\xrightarrow{c^{-1}}F_aE_TU_TX\\xrightarrow{F_a z_{T,X}}F_aX.$$\nTo compute it, take a flat-term K-flat $\\mathcal B_T$-resolution $Q\\to U_TX$. By [lem-pur-sheaf-ring-derived-coefficient-adjunction], the scalar counit is represented by $\\mathcal A_T\\otimes Q\\to X$, $b\\otimes q\\mapsto bq$. The composite above is $b\\otimes f^{-1}q\\mapsto b f^{-1}q$; its scalar adjunct is the exact inverse image of $Q\\to U_TX$. Because $F_b$ is exact, its localization is precisely the tautological isomorphism $a$. The representative and composition conventions are those of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and [lem-sfb-ringed-derived-monoidal-comparisons], and the mate is the explicit Hom-bijection formula of [def-weil-pbc-adjunction-mate]. Thus this computes the comparison with its derived normalization; it does not apply scalar restriction to a chosen injective resolution. The resulting map is also the scalar-unit comparison $\\tau$ specified in [lem-pur-ringed-coefficient-restriction-counit], since the structural ring map is an isomorphism.",
   "uses": [
    "lem-weil-pbc-ringed-topoi-derived-tensor-pullback",
    "lem-sfb-ringed-derived-monoidal-comparisons",
    "def-weil-pbc-adjunction-mate",
    "lem-pur-ringed-coefficient-restriction-counit",
    "lem-pur-sheaf-ring-derived-coefficient-adjunction",
    "lem-pc-kflat-resolution"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/sites-cohomology.tex",
    "place": "Tags 07A4 (lemma-pullback-tensor-product), 0D6D (lemma-derived-pullback-composition), 0FPI (lemma-adjoints-push-pull-compatibility)"
   }
  },
  {
   "text": "Apply [lem-pur-ringed-coefficient-restriction-counit] to the diagram topoi of Step 1, with its constant ring $A=R$ and algebra sheaves $R_W=\\mathcal A_W$. Its comparison $\\kappa$ is exactly $d$: both are normalized by the two factorizations through the constant coefficient ring. Its scalar-unit comparison $\\tau$ is exactly $a$: $f^{-1}\\mathcal A_T=\\mathcal A_V$, so its representative $x\\mapsto1\\otimes x$ is the inverse-image identity under the tensor unit isomorphism (also computed in Step 3). Its statement therefore gives\n$$\\epsilon^b_{U_VY}F_b(d_Y)=U_V(\\epsilon^a_Y)a_{G_aY}.$$\nBy the transpose formula of [def-weil-pbc-adjunction-mate], this says that $d$ is the mate of $a$. The inverse mate word applied at $X$ gives\n$$a_X=\\epsilon^b_{U_VF_aX}F_b(d_{F_aX})F_bU_T(\\eta^a_X).$$\nTranspose this equation under $F_b\\dashv G_b$ and use its triangle identity to obtain\n$$d_{F_aX}U_T\\eta^a_X=G_b(a_X)\\eta^b_{U_TX}.$$\nThese are precisely the proper system counit and unit equations. The generic counit node allows arbitrary small ringed topoi, unbounded complexes, nonflat constant-to-algebra maps and nonconstant algebra sheaves, so it applies to the single varying-coefficient diagram ring; no etale or bounded-below specialization is being substituted.",
   "uses": [
    "lem-pur-ringed-coefficient-restriction-counit",
    "def-weil-pbc-adjunction-mate"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/sites-cohomology.tex",
    "place": "Tags 07A6 (lemma-adjoint), 0D6E (lemma-derived-pushforward-composition), 0FPI (lemma-adjoints-push-pull-compatibility); explicit double-adjunction Hom calculation"
   }
  },
  {
   "text": "Record the strict scalar reduction identification. Let $\\Delta$ denote the constant tower and put $T_T=E_T\\Delta$. The flatness and quotient assertions of [lem-weil-pbc-constant-completion-equivalence] give an isomorphism\n$$k_X:\\mathcal R_TX\\xrightarrow{\\sim}T_TH_TX$$\nin the semilinear derived category, whose scalar restriction is $\\rho_X$. Indeed take a flat-term K-flat completed-ring representative $Q$. Its restriction is K-flat over $\\underline R_T$: for an acyclic $D$, $D\\otimes_RQ=(D\\otimes_R\\widehat R_T)\\otimes_{\\widehat R_T}Q$ is acyclic by flatness of $\\widehat R_T$ and K-flatness of $Q$. The terms are flat over $R$ by the same two exact tensor functors. The constant-diagram pullback sends this flat-term K-flat representative to $\\Delta Q$, again flat-term K-flat by the same ringed-pullback theorem. Both reductions are therefore the single strict complex $(Q/t^nQ)_n$, as $\\widehat R_T/t^n=(A_n)_T=\\underline R_T/t^n$. The identifications send a class of $q$ to itself and commute with all quotient maps before localization. The reduction representative is the one in [lem-coef-derived-system-evaluation-calculus]; derived tensor and pullback are computed on these representatives by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. This gives $k$, including its naturality, rather than a lift of unrelated finite-level isomorphisms. The coefficient theorems apply with $A=R,I=(t)$: [lem-weil-l-adic-extension-integers-dvr] makes $R$ a PID, hence Noetherian because every ideal is generated by one element. The quotients are finite by [lem-weil-valued-dvr-finite-quotients], so $R/(t)$ is additive torsion; $0\\to R\\xrightarrow{t^n}R\\to A_n\\to0$ is a finite-free resolution, since $R$ is a domain and $t\\ne0$, so each quotient is perfect.",
   "uses": [
    "lem-weil-pbc-constant-completion-equivalence",
    "lem-coef-derived-system-evaluation-calculus",
    "lem-weil-pbc-ringed-topoi-derived-tensor-pullback",
    "lem-weil-l-adic-extension-integers-dvr",
    "lem-pc-kflat-resolution",
    "lem-weil-valued-dvr-finite-quotients"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/sites-cohomology.tex",
    "place": "Tags 07A4 (lemma-pullback-tensor-product) and 06YY (lemma-derived-base-change); flatness and quotient properties are the additional complete-coefficient assertion cited"
   }
  },
  {
   "text": "Check the constant-tower counit normalization needed below. Let $\\chi_P:\\Delta Rp_*P\\xrightarrow{\\sim}G_b\\Delta P$ be [lem-sf-cbc-constant-tower-direct-image-normalization]. For $I=\\mathbf N_{\\ge1}^{op}$, there is exactly one arrow $n\\to1$. Thus the formula for the evaluation right adjoint in [lem-weil-pbc-diagram-site-realization] gives $e_{1*}=\\Delta$, right adjoint to exact evaluation. It sends a K-injective complex $J$ to a K-injective tower by [lem-weil-pbc-right-adjoint-preserves-kinjective]. Choose a K-injective representative $J$ of $P$. The two sides of $\\chi_P$ are then represented by the same tower $\\Delta p_*J=p_*^{\\mathcal T}\\Delta J$, exactly as in clause (1) of the normalization node. Since inverse images here are exact, the corresponding derived counits are the underived counits on $J$ and $\\Delta J$ by [lem-pc-pre-derived-adjoint-functors-general], with $s=t=f=1$ in its representative characterization of the counit at a K-injective target. Therefore\n$$\\epsilon^b_{\\Delta P}F_b(\\chi_P)=\\Delta(\\epsilon_P)$$\nunder $F_b\\Delta\\cong\\Delta p^{-1}$, as an identity of chain maps of towers on these representatives. This proves the needed counit equation, rather than inferring it from the evaluated identity of $\\chi$.",
   "uses": [
    "lem-sf-cbc-constant-tower-direct-image-normalization",
    "lem-weil-pbc-diagram-site-realization",
    "lem-weil-pbc-right-adjoint-preserves-kinjective",
    "lem-pc-pre-derived-adjoint-functors-general",
    "prop-pur-kinjective-resolutions-exist"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/sites-cohomology.tex",
    "place": "Tag 0FPI (lemma-adjoints-push-pull-compatibility); use the K-injective representative of the constant tower, with Tag 08BJ (derived-lemma-adjoint-preserve-K-injectives)"
   }
  },
  {
   "text": "For the proper case put $P=H_VM$ and $D=Rp_*P$. On diagram categories let $\\chi:\\Delta D\\xrightarrow{\\sim}G_b\\Delta P$ be the constant-tower comparison of [lem-sf-cbc-constant-tower-direct-image-normalization]. Define a semilinear map\n$$b:T_TD\\longrightarrow G_aT_VP$$\nas the $F_a\\dashv G_a$ transpose of\n$$F_aE_T\\Delta D\\xrightarrow{c}E_VF_b\\Delta D\\cong E_V\\Delta p^{-1}D\\xrightarrow{E_V\\Delta\\epsilon_P}E_V\\Delta P.$$\nThe comparison involving $\\Delta$ is the exact termwise inverse-image identity; Step 6 proves its counit compatibility with $\\chi$. Thus all factors are actual diagram morphisms. After $d$, the scalar restriction of $b$ is exactly the diagram projection map $h_P:\\mathcal R_T^{\\mathcal T}D\\to G_b\\mathcal R_V^{\\mathcal T}P$. In fact its $F_b$-transpose, using Step 4, is\n$$U_V\\epsilon^a\\,a\\,F_b(U_Tb)=U_V(\\epsilon^a F_ab)\\,a=U_V(E_V\\Delta\\epsilon_P)\\,U_V(c)\\,a.$$\nThe last composite, on a flat tensor model, sends $q\\otimes\\bar r$ to $\\epsilon_P(q)\\otimes\\bar r$. This is precisely counit tensor identity after the pullback/tensor comparison, the defining transpose of $h_P$ in [lem-weil-pbc-ringed-projection-mate-exact]. Injectivity of the $F_b$-adjunction bijection proves $d\\,U_Tb=h_P$. No invertibility of a projection map was used in this computation.",
   "uses": [
    "lem-sf-cbc-constant-tower-direct-image-normalization",
    "lem-sfb-ringed-derived-monoidal-comparisons",
    "lem-weil-pbc-ringed-projection-mate-exact"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/sites-cohomology.tex",
    "place": "Tags 07A6 (lemma-adjoint), 07A4 (lemma-pullback-tensor-product), and 0B56 (equation-projection-formula-map); scalar-restriction equality is the displayed transpose computation, not Tag 0E48"
   }
  },
  {
   "text": "Write $C_Z=\\mathcal L_Z^{\\mathcal T}\\mathcal R_Z^{\\mathcal T}$ and let $\\eta_Z:1\\to C_Z$ be the specified completion unit. Put\n$$a_P:Rp_*C_VP\\xrightarrow{\\sim}\\mathcal L_T^{\\mathcal T}G_b\\mathcal R_V^{\\mathcal T}P.$$\nThis is the common-composite direct-image comparison of [lem-weil-ringed-tower-pushforward-limit-comparison]. The normalizations in [lem-sf-cbc-constant-tower-direct-image-normalization] imply the equality\n$$\\mathcal L_T^{\\mathcal T}(h_P)\\eta_D=a_P\\,Rp_*(\\eta_P).\\tag{*}$$\nTo see the whole-map equality, let $i_Z:\\Delta Z\\to\\mathcal R^{\\mathcal T}Z$ be the strict quotient map, and $\\delta_Z:Z\\to R\\lim\\Delta Z$ the constant-tower unit. Then $\\eta_Z=R\\lim(i_Z)\\delta_Z$. Clause (4) gives $h_Pi_D=G_b(i_P)\\chi_P$. Taking $R\\lim$, using naturality of $a$ at $i_P$ and clause (3), $R\\lim(\\chi_P)\\delta_D=a_{\\Delta P}Rp_*(\\delta_P)$, gives $(*)$ by substitution. This uses identities of derived tower maps, rather than uniqueness from their projections. The units here are the quotient-tower units of [lem-weil-pbc-constant-completion-equivalence].",
   "uses": [
    "lem-weil-ringed-tower-pushforward-limit-comparison",
    "lem-sf-cbc-constant-tower-direct-image-normalization",
    "lem-weil-pbc-constant-completion-equivalence"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/sites-cohomology.tex",
    "place": "Tag 0D6E (lemma-derived-pushforward-composition), with the strict-tower normalization clauses of the cited nodes"
   }
  },
  {
   "text": "Let $X=A_{\\rm int}M$ and $N=S_p\\mathcal R_VM$. The proper tower-definition identification is $d_A:\\mathcal L_TN\\xrightarrow{\\sim}X$ of [lem-sf-generator-reduction-coherence]. Restricting the completed-ring limit and then using $d$ and $k_M$ gives\n$$\\lambda:H_T\\mathcal L_TN\\xrightarrow{\\sim}\\mathcal L_T^{\\mathcal T}G_b\\mathcal R_V^{\\mathcal T}P.$$\nRestriction commutes with this total limit by [lem-weil-pbc-constant-completion-equivalence], applied to identity-topos scalar restriction of the underlying tower; equivalently apply [lem-weil-ringed-tower-pushforward-limit-comparison] to the identity-topos ringed map. Define the proper constant-coordinate identification by its tower normalization:\n$$\\sigma_X=(a_P\\,Rp_*\\eta_P)^{-1}\\lambda H_T(d_A^{-1}):H_TX\\xrightarrow{\\sim}Rp_*P.$$\nHere $P$ is complete by the complete-coefficient equivalence, hence $\\eta_P$ is invertible, and $Rp_*$ preserves completeness by [lem-sp-completed-pullback-adjunction]. This is the canonical scalar comparison: the three factors are respectively the inverse-image of the same strict reduction tower through the actual completion unit, the common direct-image/limit comparison, and the defining integral tower. Each is normalized by that tower, so this definition chooses no reconstruction or arbitrary isomorphism.",
   "uses": [
    "lem-sf-generator-reduction-coherence",
    "lem-weil-pbc-constant-completion-equivalence",
    "lem-weil-ringed-tower-pushforward-limit-comparison",
    "lem-sp-completed-pullback-adjunction"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/sites-cohomology.tex",
    "place": "Tag 0D6E (lemma-derived-pushforward-composition); completion-reflector adjunction and actual integral reduction-tower normalization as in the cited statements"
   }
  },
  {
   "text": "Using the semilinear lift of Step 7, form\n$$b'_M=G_a(k_M^{-1})\\,b\\,T_T(\\sigma_X)\\,k_X:\\mathcal R_TX\\to N.$$\nIts restricted map, after $d$ and $\\rho_M$, is $h_P\\mathcal R_T^{\\mathcal T}(\\sigma_X)\\rho_X$. The $\\mathcal R_T\\dashv\\mathcal L_T$ adjunct of $b'_M$ is $\\mathcal L_T(b'_M)u_X$ [lem-coef-derived-system-evaluation-calculus]. Apply $H_T$ and $\\lambda$ to this adjunct. Step 5 and the unit-preserving limit comparison identify the result with\n$$\\mathcal L_T^{\\mathcal T}(h_P)\\mathcal L_T^{\\mathcal T}\\mathcal R_T^{\\mathcal T}(\\sigma_X)\\eta_{H_TX}\n=\\mathcal L_T^{\\mathcal T}(h_P)\\eta_D\\sigma_X\n=a_P Rp_*(\\eta_P)\\sigma_X\n=\\lambda H_T(d_A^{-1}),$$\nusing naturality of the completion unit, $(*)$, and the definition of $\\sigma_X$. Both $X$ and $\\mathcal L_TN$ are complete: $N$ is normalized by the item hypotheses, so [lem-coef-normalized-dvr-effectivity] makes $\\mathcal L_TN$ complete; use the isomorphism $d_A$ for $X$. The complete-coefficient equivalence is therefore faithful on these two objects. Cancel $\\lambda$ and $H_T$ to see that the adjunct is $d_A^{-1}$. By the actual adjunction bijection, $b'_M=e_N\\mathcal R_T(d_A^{-1})=r_{A,M}$ [lem-sf-generator-reduction-coherence]. Finally [lem-sf-cbc-compact-support-composition-limit] identifies $h_P$ with the prescribed proper $q_{A,P}$. This proves the full proper equality, including the constant-coordinate factor.",
   "uses": [
    "lem-coef-derived-system-evaluation-calculus",
    "lem-weil-pbc-constant-completion-equivalence",
    "lem-sf-generator-reduction-coherence",
    "lem-sf-cbc-compact-support-composition-limit",
    "lem-coef-normalized-dvr-effectivity"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md",
    "place": "coefficient comparisons of the prescribed maps before taking adjunction mates"
   }
  },
  {
   "text": "For an open $j$, extension by zero is the exact localized-site adjunction [lem-pur-site-restriction-module-adjunction-exact]. Restriction of a module action leaves its extension-by-zero generators unchanged, so $U_TJ_j=J_jU_V$ and $H_Tj_!=j_!H_V$ on the underlying complexes; restriction to the open is the same equality. The open unit takes an open section to that same section, and the counit takes an extension generator over the open to its section on the ambient object. Forgetting the action leaves each of these maps unchanged. Thus these are equalities of the two exact adjunctions on complexes, hence on their derived localizations, including the strict integer transitions. This proves the open scalar unit/counit clause directly. It uses no infinite-limit claim about ordinary extension by zero. Put $Q=j_!P$ and $X=j_!M$. By [lem-sf-integral-open-reduction-comparison], $X$ is complete; restriction through the complete-coefficient equivalence makes $Q=H_TX$ complete. The canonical constant-coordinate identification is therefore $\\sigma_X:H_TX=Q\\xrightarrow{\\eta_Q}C_TQ=J_j^cP$, with the actual completion unit.",
   "uses": [
    "lem-pur-site-restriction-module-adjunction-exact",
    "lem-sf-integral-open-reduction-comparison",
    "lem-weil-pbc-constant-completion-equivalence"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md",
    "place": "open adjunction and completion-unit-normalized coefficient comparison"
   }
  },
  {
   "text": "On the common flat-term completed-ring representative in Step 5, $r_j$ is the open tensor map of [lem-sf-integral-open-reduction-comparison]. Its scalar restriction, after $\\rho$, is the strict constant-coordinate tensor comparison $q^{\\rm tens}_{j,P}$. This is a whole-tower calculation: both adjuncts under the open extension/restriction adjunction send the extension generator $x\\otimes\\bar r$ to $x\\otimes\\bar r$ on the open. Replacing $\\bar r$ by its image in $A_n$ gives the identical formula for every transition $A_m\\to A_n$. Thus the chain maps of strict quotient systems agree before localization. The open-completion theorem [lem-sf-cbc-extension-zero-completion] states\n$$q_{j,P}\\mathcal R_T^{\\mathcal T}(\\eta_Q)=q^{\\rm tens}_{j,P}.$$\nSubstitute $\\sigma_X=\\eta_Q$ from Step 11 and the reduction identification $\\rho_X$; this gives exactly\n$$J_j(\\rho_M)(U_TJ_j\\cong J_jU_V)U_Tr_j\n=q_{j,P}\\mathcal R_T^{\\mathcal T}(\\sigma_X)\\rho_X.$$\nThe one-letter $q$ in [lem-sf-cbc-compact-support-composition-limit] is this same $q_j$. Its finite-level formula, used here with its strict transition normalization, is explicitly supplied by the extension-zero-completion statement.",
   "uses": [
    "lem-sf-integral-open-reduction-comparison",
    "lem-sf-cbc-extension-zero-completion",
    "lem-sf-cbc-compact-support-composition-limit"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md",
    "place": "canonical open tensor comparison and its completion-unit normalization"
   }
  },
  {
   "text": "All transformations used above are natural. The proper comparison is formed from the derived composition comparisons on diagram ringed topoi, so its naturality is that of [lem-sfb-ringed-derived-monoidal-comparisons]; $k$ and the completion units are natural strict quotient constructions of [lem-weil-pbc-constant-completion-equivalence]; and $q$ has the strict-tower naturality of [lem-sf-cbc-compact-support-composition-limit]. The proper unit and counit equalities were proved by the two adjunction Hom bijections in Step 4, and the open ones by the exact open adjunction in Step 11. Consequently their mates agree as well by substituting these equalities in the unit/comparison/counit formula of [def-weil-pbc-adjunction-mate]. The finite cohomological/Tor intervals and compatible etale-origin witnesses are used only to remain in the domain of $d_A,r_A$ in [lem-sf-generator-reduction-coherence]; no stronger bounds or flatness of a finite quotient are assumed. These are morphism equalities in the strict derived diagram categories. No assertion that evaluations detect equality of arbitrary derived arrows or any compactification-composition comparison occurs.",
   "uses": [
    "lem-sfb-ringed-derived-monoidal-comparisons",
    "lem-weil-pbc-constant-completion-equivalence",
    "lem-sf-cbc-compact-support-composition-limit",
    "def-weil-pbc-adjunction-mate",
    "lem-sf-generator-reduction-coherence"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md",
    "place": "naturality and adjunction-mate coherence of the individual generator comparisons"
   }
  }
 ],
 "proof_origin": {
  "by": "agent",
  "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md",
  "place": "Normalized individual coefficient maps and adjunction mates; additional agent expansion using the ringed-topos composition/adjunction route, with explicit whole-tower normalization and no appeal to Tag 0E48 for scalar restriction."
 }
}
```

Comparison result: the pre-pivot Step 1 identified `S_f` with the ringed-topos right derived functor only by saying both are right adjoint to the same section inverse image; the current Step 1 instead invokes the ordinary unbounded derived adjunction and the repaired ordinary `lem-coef-semilinear-derived-sections` interface. The pre-pivot Step 5 called its reduction representative directly “the reduction representative”; the current Step 5 identifies it as the ordinary derived reduction representative. The pre-pivot Step 11 used the same open calculation but omitted the explicit “ordinary exact localized-site adjunction” route phrase; the current step states that route. The pre-pivot Step 13 only asserted naturality of the transformations; the current step explicitly records that Steps 1–4 construct ordinary derived functors and Steps 5–12 compute their maps, and says no extra localization or section-realization interface is used. Thus no pre-pivot proof step is resubmitted verbatim as the justification for the pivot: the four changed steps carry the route correction, while the nine unchanged calculations are ordinary ringed-topos/K-flat/adjunction calculations and do not cite dropped nodes.

### Route-pivot audit conclusion

I intersected the exact manifest above with the transitive `stmt_deps` and `proof_deps` closures of all 27 roots used by the 13 steps. Every intersection is empty. I also checked the applicable repair note: its four forbidden machinery nodes are `lem-coef-dg-derived-quillen-calculus`, `lem-coef-kinjective-flat-model-fibrant`, `lem-coef-quillen-section-rectification`, and `lem-coef-sheaf-flat-model`; none occurs in this item statement, proof, or dependency closure. The current ordinary interface is the route-pivot replacement named by the note. This exact artifact section repairs C7 by making the manifest, note, and historical proof comparison reviewable from the delivery report itself.
