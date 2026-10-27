# Q76 stage-1 report: lem-sfb-affine-adjoint-unit-properties

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-adjoint-unit-properties.json: statement unchanged, seven proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-pseudocoherent-rhom-quasicoherent.json: statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, Loogle, grep and LeanSearch.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-global-trace-adjunction.json: statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, Loogle, grep and LeanSearch.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-test-relative-perfection.json: statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, Loogle, grep and LeanSearch.

## Attachments

None. The tag and conceptual searches of lean/WeilConjectures found no declaration stating this item. PseudoCoherentRHomQuasiCoherent.lean states a Noetherian scheme/algebra-source theorem; it does not cover arbitrary algebraic spaces and arbitrary pseudo-coherent sources. No Lean file was written or compiled.

## WANTED

None. All proof sources are present in literature/stacks-project/.

## Corrections and scope

The item agrees with Stacks Tag 0E5V, lemma-properties-relative-dualizing, and is unchanged. Its imported proof was empty. The inherited chain leads to the coherent-duality prerequisite of stable-curve alteration; I read the current latest blueprint proof det-thm-sf-ctf-stability-direct-images (3), as well as the chapter and unit records. I have not changed their route. The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor reports None, so I preserved that value rather than inventing an ancestor. All from.place entries are specific and same_as is empty after blueprint searches.

The displayed third paragraph in Stacks mixes a Hom group with RΓ, a derived object. Step 5 writes H^0 explicitly. This is a notational repair to the proof, not a statement dispute. The global trace node retains the coherator limitation: it asserts a derived global comparison, never the generally false uncoherated sheaf-Hom comparison for arbitrary L. The source proof suppresses the lower-bound check needed before applying 0A8A to RHom(W,W); Step 2 obtains local boundedness from relative perfection. Step 6 checks that the tested morphism is scalar multiplication.

Generic off-unit tools are declared in split_report.tool_uses: affine perfect preimages, derived pushforward composition, the finite-projective Tor-window theorem, and closed symmetric monoidal structure of a ringed-site derived category. These are tools within the same Stacks proof, not alternate routes.

## Unfinished work

The three new nodes are intentionally statement-only inputs for later stage-1 work. No unfinished argument remains inside the item split.

## Not duplicates

lem-sfb-space-affine-global-trace-adjunction vs lem-sfb-affine-etale-derived-module-realization: the new node is an affine-base derived global trace comparison for arbitrary quasi-coherent L and its adjoint W, with evaluation normalization; the existing node has the distinct statement "Affine small-etale realization of the unbounded module derived category". In particular the new node does not assert the nodal dualizing-line, arbitrary-base sheaf, or Zariski-etale equivalence theorem of that existing node.
lem-sfb-space-affine-global-trace-adjunction vs lem-sfb-derived-etale-zariski-equivalence: the new node is an affine-base derived global trace comparison for arbitrary quasi-coherent L and its adjoint W, with evaluation normalization; the existing node has the distinct statement "Derived quasi-coherent etale-Zariski equivalence and pullback comparison". In particular the new node does not assert the nodal dualizing-line, arbitrary-base sheaf, or Zariski-etale equivalence theorem of that existing node.
lem-sfb-space-affine-global-trace-adjunction vs lem-sfb-proper-flat-space-derived-base-change: the new node is an affine-base derived global trace comparison for arbitrary quasi-coherent L and its adjoint W, with evaluation normalization; the existing node has the distinct statement "Perfect coherent derived direct image for proper flat algebraic spaces". In particular the new node does not assert the nodal dualizing-line, arbitrary-base sheaf, or Zariski-etale equivalence theorem of that existing node.
lem-sfb-space-affine-global-trace-adjunction vs lem-sfb-scheme-derived-etale-qcoh-comparison: the new node is an affine-base derived global trace comparison for arbitrary quasi-coherent L and its adjoint W, with evaluation normalization; the existing node has the distinct statement "Unbounded derived Zariski-etale quasi-coherent comparison". In particular the new node does not assert the nodal dualizing-line, arbitrary-base sheaf, or Zariski-etale equivalence theorem of that existing node.

Other conceptual near matches: lem-sfb-perfect-tests-detect-pseudocoherence is scheme-only and concludes pseudo-coherence, not finite relative Tor amplitude; it cannot replace the new algebraic-space relative-perfectness criterion. lem-sc-rhom-supported-qcoherent-pseudo-part is scheme-only on the Zariski site, unlike the new algebraic-space/small-etale internal-Hom result. Existing perfect sections, ringed-site duality, affine etale realization, and localizing generation were reused instead of duplicated.

## Review by Q76

I read spaces-duality.tex, lemma-properties-relative-dualizing (Tag 0E5V), in full, including all three proof paragraphs. For the perfect-test node I read spaces-more-morphisms.tex, lemma-characterize-relatively-perfect (Tag 0GFL), its proof and the preceding bounded-on-fibres criterion, together with definition-relatively-perfect (0DKN). For the trace node I read spaces-duality.tex, lemma-iso-on-RSheafHom (0E58), its adjunction/projection-formula proof, the warning example and remark-iso-on-RSheafHom (0GG4). The passage to global derived Hom tests the coherator comparison against O_Y and all its shifts; this removes no quasi-coherence hypothesis on the internal Hom. For the internal-Hom node I read spaces-perfect.tex, lemma-quasi-coherence-internal-hom (0A8A), both cases and its etale-local proof. The local-bound formulation is obtained by applying that theorem separately on each bounded-below neighbourhood.

Step 1 uses exactly the perfect-duality node for dual perfection and E tensor W = RHom(E dual,W), the new normalized global trace node for the middle comparison, and flat-proper perfect-sections for perfection of G(E dual). All source hypotheses hold: X is qcqs, f is flat proper finitely presented, and Y is affine. Applying perfect duality on the one-object A-site proves perfection of the dual without needing any Noetherian hypothesis.

Step 2 uses the full new perfect-test criterion, not the existing scheme-only pseudocoherence test. W is in D_QCoh by the codomain of a. Properness supplies separatedness. Its finite relative Tor dimension implies local cohomological bounds by taking the inverse-image coefficient ring itself as test module; the new internal-Hom theorem then gives quasi-coherence for RHom(W,W). I verified that the target of this internal Hom is locally bounded below before invoking that theorem.

Step 3 uses the existing flat-proper perfect-sections theorem and affine projection formula precisely with E=O_X and an arbitrary A-module M. It uses the existing proper-flat structure-sheaf base-change theorem only for perfectness of its Zariski image, not for arbitrary perfect complexes. The affine perfect-preimage node provides the pseudo-coherence hypothesis of the projective-window theorem. The scheme site comparison, affine etale module equivalence and generic pushforward compositor identify that preimage with B; hence the window theorem is applied to a pseudo-coherent object with Tor amplitude [0,N], not just a cohomological bound. Negative cohomology of the projection formula target vanishes from an ordinary nonnegative injective resolution. The upper bound N exists from any bounded finite-projective model of B. This supplies the lower Tor-bound reasoning compressed in Stacks.

Step 4 takes L=O_X in the new trace theorem; bounded projectivity makes its ordinary dual compute derived Hom, and the supported degrees become [-N,0]. The pushforward-preserves-QCoh clause comes from the qcqs-space right-adjoint node. The affine module equivalence identifies each cohomology sheaf, not merely its group of global sections, so vanishing really is sheaf vanishing. The generic Leray compositor is used only for morphisms of ringed topoi, including global sections to the one-point A-ringed topos.

Step 5 uses the closed ringed-site tensor-Hom adjunction, ordinary right-adjunction formula, the normalized trace comparison already used in Step 1, and perfect biduality. The global-Hom node supplies H^0 RHom = Hom for the final group equality, and affine realization interprets the adjunction on Y as one over A. No scheme-only Hom theorem is substituted for the algebraic-space one. Step 6 is an elementary check of these cited formulas: evaluation at the section corresponding to u is u tensor 1_W followed by the adjunction trace, exactly the functional defining the comparison. The tensor-Hom transpose is alpha composed with u. This checks the specified scalar map rather than inferring invertibility from arbitrary group bijections.

Step 7 uses only the statement of localizing generation. It does not pretend that this node explicitly states conservativity of perfect tests: I wrote the orthogonality argument using shifts, cones, retracts and coproducts, then tested the cone against itself. Long exact Hom sequences supply its vanishing. Each proof-step citation has a verbatim statement quote in citations.json, and proof_deps is exactly the union of uses.

I checked B1-B10: all new nodes have only a statement, introduce every object and hypothesis, use single TeX escapes, record actual search outputs, give Stacks tags and labels, and have explicit blueprint provenance. None is an elementary reformulation or a clause of the item: the criterion treats every K, the trace theorem every qcqs affine-base morphism and L without properness, and the internal-Hom theorem every algebraic space and suitable K,L. I checked C1-C8: every substantive input is cited, each cited statement was opened, generic tools are declared, and no cited input has a dependency path back to this item. D1-D5 are met by the explicit duality, Tor-model, normalization and generation arguments; none says merely apply a new copy of a conclusion. E1-E7 were checked against proper-flat-finite-presentation, qcqs, affine, perfect/pseudocoherent and boundedness assumptions at their actual uses. All seven steps are under 2000 characters.

Small cases: for f the identity, W=O_Y and all comparisons reduce to perfect biduality and scalar action. For X empty or the zero base ring every derived category on X is zero, so perfection, vanishing and scalar-isomorphism assertions still hold. Over a field a proper smooth curve has W=omega[1], so its own negative-degree cohomology is allowed, while Rf_*W has no positive cohomology; this checks the shift orientation. The trace node works for identity and zero complexes and does not require W itself to be perfect on X. The perfect-test criterion is not claimed for nonseparated or non-finitely-presented spaces. The internal-Hom assertion deliberately requires a locally bounded-below target in its pseudo-coherent case; no unbounded-target strengthening was made.

## Validation

The required deliver.py --no-push and final push are run after this report is written; their output is the delivery authority.
