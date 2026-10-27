# Repair report for lem-amb-tate-root-projection-reduction


## Files written

- lem-amb-tate-root-projection-reduction: unchanged statement, four-step assembly, 2396 characters.

- lem-amb-root-tower-finite-tensor: statement, unsplit; no Mathlib match.

- lem-amb-root-tower-pullback-coherence: statement, unsplit; no Mathlib match.


## Attachments

None. The upstream Tate sheaf is an etale finite-level construction, not this pro-etale inverse-limit comparison. The local ambTateRootProjectionReduction existence theorem is postponed, so it is not an attachment.


## WANTED

None.


## What was wrong and what changed

The returned proof was 7523 characters in nine steps. This repair distributes its substantive arguments between two independently provable tasks; neither depends on the other or on the parent. The finite comparison does not contain j, scheme pullbacks, or coherence. The pullback task does not prove projection surjectivity, kernels or finite tensor invertibility. The parent keeps its exact statement and assembles the tasks with reassociation and transition calculations. The stale Tag 093M completion-flat attribution was removed: no completion-flat theorem is used.


## Unfinished work

The two new tasks are intentionally statement-only, with empty proof/proof_deps and null proof_origin, as required by the return. No compiler was run.


## Review by Q143

I read GOAL.md, the chapter and unit sk-prop-an, and the current blueprint thm-amb-vector-bundle-purity proof paragraph 1. I read Stacks proetale.tex Tag 0990 (enough affine weakly contractible objects), sites.tex Tag 090K (evaluation surjectivity), and sites-modules.tex Tags 03EK and 03EL (sheafified balanced tensors and tensor pullback). These supply tools, not a published statement of the two agent-written combinations. The source places distinguish the agent argument from the Stacks lemma. No SGA route is used.

Parent step 1 uses the actual finite-twist formula in def-coefficient-twists-detailed, the root and sectionwise limit definitions for the Z_l action, and the sheafified tensor definition for the mutually inverse balancing formulas. Step 2 uses the whole finite-tensor task: A=O_E/varpi_E^n is a commutative Z_l-algebra, ell is invertible on T, r is positive and ell^r A=0. It needs neither flatness nor e|n. Step 3 uses root transitions, tensor formation and pure-tensor determination from the exact statements quoted in citations.json; equality on compatible tuples proves the transition equation and its identity/composition laws. Step 4 uses the pullback task with the same constant algebra A; its h_v square has exactly the specified c_r^v, and conjugating by j gives the displayed b_v square and cancels the j factors in compositions.

For the finite-tensor task, I checked the existing Kummer transition epimorphism, both general-site epi criteria, and the full-site weakly contractible covering statement. They say respectively precisely that consecutive root maps are epis, that these are locally surjective set maps, and that all consecutive choices can be made on each fixed covering object. The proof does not require an infinite refinement of etale covers. The kernel division x_(s+r) really is an ell^s-th root when x_r=1. For the inverse local tensor construction, the difference of lifts is ell^r y, whose tensor with b is y tensor ell^r b=0; the output glues. I read lem-pur-torsion-sheaf-constant-module (2), which provides the finite constant-ring linearity on slices; the tensor section calculus provides pure-tensor determination. The normalized inverse and both composites are therefore well specified.

For the pullback task, I read def-pur-roots-of-unity-inverse-image and lem-pur-roots-of-unity-inverse-image-iso: the latter supplies transition compatibility and semilinearity, but not the identity/composition equations. Those remain a real argument of the new task: compute the specified adjunct on the actual fibre products. I read the inverse-image definition, the limit definition, the monoidal composition assertion of lem-weil-pbc-left-exact-site-inverse-image-tensor, the ordinary module tensor pullback statement of lem-weil-pbc-ringed-topoi-module-pullback-tensor, and lem-pe-constant-left-module-inverse-image with its composition clause. They justify exactly the cone, semilinearity, canonical constant-ring identifications, tensor square and coherence in the preserved argument below. Inverse image is never assumed to preserve an infinite limit.

Edge cases checked: T empty gives zero sheaves and unique maps; r=1 has the same shift division; no restriction beyond r>=1 is needed because only ell invertibility is used. At a separably closed field the root tower is a compatible rank-one tower and the comparison is scalar reduction. B=F_ell considered over Z/ell^2 is nonflat but the local inverse remains valid. A ramified extension of index e=2 with n=3 and ell^2 A=0 needs no divisibility of n by the ramification index. B=0 also gives zero tensors. The pullback result works for identity and two composable maps without assuming finite root comparisons are isomorphisms.

B-E self-check: each new statement introduces all its objects and notions; neither has proof steps or hidden proof prose. Searches were run through msearch.py, with both semantic phrasings, Loogle and source grep; ordinary tensor quotient hits were read and are not sheaf comparisons. Existing DAG and blueprint searches covered root projections, finite tensor reduction and root pullback; comparisons are detailed below. New tasks have no proof dependencies and no dependency on their parent, so they introduce no cycle. Parent citations use statements, not proofs. The two extracted arguments have sizes 2509 and 3776 characters before allocation of the final edge-case sentences; the parent assembly is under 3000. The complete old argument is retained below, not abbreviated.


## Second reading by Q143

This is the required direct-delivery author self-review recorded above; no second worker or independent review is claimed. The maintainer provides the independent review.


## Not duplicates

- lem-amb-root-tower-finite-tensor vs lem-fix-residue-lisse-projective-models: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "Projective sheaf models from lisse residue cohomology on a weakly contractible affine".

- lem-amb-root-tower-finite-tensor vs det-lem-int-integral-heart-local-model: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "Local models of integral constructible complexes and their cohomology".

- lem-amb-root-tower-finite-tensor vs sk-lem-int-integral-heart: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "Structure of integral constructible complexes".

- lem-amb-root-tower-finite-tensor vs lem-weil-pbc-ind-etale-basis-wcontractible-cover: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "Weakly contractible covers within the affine ind-etale basis".

- lem-amb-root-tower-finite-tensor vs lem-weil-pbc-proetale-representable-epi-local-lifting: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "Represented epimorphisms give local lifts on the pro-etale site in their value universe".

- lem-amb-root-tower-finite-tensor vs lem-weil-pbc-source-affine-wcontractible-evaluation: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "Closed full-site evaluation at a geometrically w-contractible affine object".

- lem-amb-root-tower-finite-tensor vs lem-weil-pbc-finite-etale-tower-cover: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "Weakly contractible refinement of a finite etale covering cone".

- lem-amb-root-tower-finite-tensor vs lem-weil-pbc-proetale-affine-wcontractible-covering-family: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "Affine weakly contractible covering family on the pro-etale site".

- lem-amb-root-tower-finite-tensor vs lem-weil-pbc-affine-contractible-extension-full-site: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "An affine contractible extension valid on every full small pro-etale site".

- lem-amb-root-tower-finite-tensor vs lem-sf-fullcd-detection-equivalence: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "The full cohomological-dimension condition is a bound on the pro-étale cohomology of the base-changed source".

- lem-amb-root-tower-finite-tensor vs lem-sf-proetale-vanishing-detection: the new task asserts the root-projection kernel, local lift and normalized finite ordinary tensor inverse, not just covering/evaluation/derived local-model statements; the existing node is "Detection of vanishing on affine weakly contractible objects".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-site-inverse-image-multimap-universal: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Universality of inverse-image units for natural maps with finitely many inputs".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-site-inverse-image-bilinear-adjunction: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Bilinear adjunction for the inverse image of a morphism of sites".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-ringed-slice-normalized-comparisons: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Existence of normalized slice tensor, Hom and Koszul comparisons".

- lem-amb-root-tower-pullback-coherence vs def-coef-semilinear-geometry-derived: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Derived geometric system operations and normalization".

- lem-amb-root-tower-pullback-coherence vs def-sf-point-evaluation-tensor-coherence: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Signed tensor coherence for point sections".

- lem-amb-root-tower-pullback-coherence vs def-sf-point-evaluation-scalar-data: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Balanced scalar comparison for point sections".

- lem-amb-root-tower-pullback-coherence vs lem-coef-signed-single-dual-restriction: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized slice comparison for a single coefficient dual".

- lem-amb-root-tower-pullback-coherence vs lem-sf-open-operation-models: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Open operation comparisons with fixed tensor models and right square".

- lem-amb-root-tower-pullback-coherence vs lem-weil-ramified-finite-pullback-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized finite pullback comparison along coefficient quotient base change".

- lem-amb-root-tower-pullback-coherence vs lem-weil-finite-pullback-transition-generators: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Composite finite pullback transitions reduce both tensor coefficients".

- lem-amb-root-tower-pullback-coherence vs def-sf-point-evaluation-tensor-data: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized tensor presentation for point sections".

- lem-amb-root-tower-pullback-coherence vs def-sf-point-evaluation-derived-compatibility: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Representative-normalized derived point comparisons".

- lem-amb-root-tower-pullback-coherence vs def-coef-semilinear-geometry-ops: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical geometric mate and projection words".

- lem-amb-root-tower-pullback-coherence vs lem-weil-etale-native-tensor-pullback: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Native unbounded derived tensor commutes with etale inverse image".

- lem-amb-root-tower-pullback-coherence vs lem-sf-point-ringed-evaluation-model: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Ringed geometric-point evaluation with signed tensor and coefficient models".

- lem-amb-root-tower-pullback-coherence vs def-coef-semilinear-geometry-base: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Geometry base fields for coefficient linear operations".

- lem-amb-root-tower-pullback-coherence vs def-sf-evaluation-hom-site-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Evaluation-induced derived Hom comparison for the etale-proetale morphism".

- lem-amb-root-tower-pullback-coherence vs def-sf-point-evaluation-scalar-coherence: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Tensor square for balanced point scalar data".

- lem-amb-root-tower-pullback-coherence vs def-sf-open-normalization-data: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Geometric and operation data for open tensor normalization".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-scalar-inverse-image-tower-diagram: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Ordinary inverse-image and balanced scalar-tower square".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-ringed-derived-tensor-diagrams: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Coherence equations for explicit canonical derived comparison maps".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-ringed-derived-tensor-lift: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Symmetric monoidal coherence of a canonical derived tensor lift".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-condensed-support-projection-formula: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Natural support tensor projection formulas on unbounded condensed modules".

- lem-amb-root-tower-pullback-coherence vs def-sfb-ringed-slice-comparison-model: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized ringed slice comparison data".

- lem-amb-root-tower-pullback-coherence vs def-sfb-module-object-projection-map: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical derived projection map for condensed module objects".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-ringed-derived-two-iso-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Specified geometric 2-isomorphism comparison on derived modules".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-proetale-intrinsic-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Right-tensor comparison for intrinsic constant-ring realization".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-etale-stalk-total-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical signed total tensor stalk comparison and chain naturality".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-geometric-two-iso-scalar-pairing: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Geometric two-isomorphisms preserve the ordinary scalar balanced pairing".

- lem-amb-root-tower-pullback-coherence vs def-sfb-condensed-pullback-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized condensed-module pullback tensor comparison".

- lem-amb-root-tower-pullback-coherence vs def-sfb-proetale-trace-coefficient-interfaces: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical internal-module trace coefficient interfaces".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-localized-site-tensor-restriction: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Restriction to a localized site commutes with the sheaf tensor product".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-kflat-scalar-comparison-normalization: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Representative and adjunction normalization of scalar pullback comparison".

- lem-amb-root-tower-pullback-coherence vs lem-sfb-scalar-ordinary-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized ordinary scalar tensor comparison in independent site universes".

- lem-amb-root-tower-pullback-coherence vs lem-per-local-system-tensor-monodromy: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Tensor comparison for arbitrary torsion local systems".

- lem-amb-root-tower-pullback-coherence vs lem-per-proetale-scalar-slice-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized scalar extension comparison on a pro-etale slice".

- lem-amb-root-tower-pullback-coherence vs lem-a1-balanced-finite-tower-generator-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Balanced finite-tower association and quotient-generator normalization".

- lem-amb-root-tower-pullback-coherence vs lem-per-galois-descent-monodromy-tensor: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Monodromy and tensor of modules descended along a finite Galois cover".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-continuous-module-encoding-scalar-extension: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Scalar extension under the continuous integral and rational module encodings".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-closed-immersion-scalar-change: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Ordinary closed scalar change with transported coefficients".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-left-exact-site-inverse-image-tensor: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Inverse image induced by a continuous left-exact site functor and its tensor structure".

- lem-amb-root-tower-pullback-coherence vs def-weil-pbc-canonical-ringed-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized ordinary tensor comparison data".

- lem-amb-root-tower-pullback-coherence vs def-weil-pbc-actual-finite-coefficient-transport: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Actual-ring finite coefficient transport and normalized local restriction".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-canonical-ringed-tensor-comparison-construction: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Construction of the normalized ordinary tensor comparison".

- lem-amb-root-tower-pullback-coherence vs def-weil-pbc-normalized-scalar-restriction: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized completed-coefficient scalar and restriction comparison".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-continuous-module-encoding-restriction: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Continuous module encoding commutes with restriction along an etale morphism".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-localization-inverse-image-coherence: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Coherent localization comparison for exact inverse image".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-algebraic-inverse-image-pairing-isIso: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Universality of the transported inverse-image pairing".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-ringed-topoi-module-pullback-tensor: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Underived tensor comparison for pullback of modules on ringed topoi".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-algebraic-inverse-image-pure-pairing: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "The canonical bilinear pairing of the specified inverse image".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-reduction-pullback-derived-tower: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized derived pullback of a strict coefficient reduction tower".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-scalar-extension-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Scalar extension preserves the normalized sheaf tensor".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-algebraic-inverse-image-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "The normalized tensor comparison for the specified algebraic inverse image".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-continuous-module-encoding-lattices: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Local freeness and lattice compatibility of the explicit continuous encodings".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-proetale-closed-underived-projection: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Underived tensor projection for closed pro-etale immersions with arbitrary ring coefficients".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Tensor comparison tail for scalar-extended inverse-image modules".

- lem-amb-root-tower-pullback-coherence vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Common quotient reduction of the geometric scalar comparison".

- lem-amb-root-tower-pullback-coherence vs def-weil-pbc-ringed-tensor-square-presentation: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Representative presentation of a commutative ringed tensor square".

- lem-amb-root-tower-pullback-coherence vs def-pur-signed-line-pullback-normalization-data: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized signed pullback families and scalar squares".

- lem-amb-root-tower-pullback-coherence vs lem-sp-proetale-scalar-balancing-chain: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Constant-coefficient balancing and its natural inverse-image chain map".

- lem-amb-root-tower-pullback-coherence vs lem-pur-common-line-positive-scalar-powers: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Common-line presentations and nonnegative powers under scalar extension".

- lem-amb-root-tower-pullback-coherence vs lem-sp-bounded-flat-coefficient-site-square: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Bounded-flat coefficient/site square with its canonical derived comparison".

- lem-amb-root-tower-pullback-coherence vs lem-pur-scalar-tensor-unit: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Scalar action unitor for a normalized signed tensor comparison".

- lem-amb-root-tower-pullback-coherence vs lem-pur-module-tensor-extension-equation: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Ordinary scalar-extension tensor equation".

- lem-amb-root-tower-pullback-coherence vs lem-pur-signed-line-derived-base-change: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Signed line comparisons and their unbounded derived tensor action".

- lem-amb-root-tower-pullback-coherence vs lem-pur-module-tensor-composition-equation: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Ordinary tensor square for composite module pullback".

- lem-amb-root-tower-pullback-coherence vs lem-pur-ringed-site-pullback-dual-free-chart: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Invertibility of a pulled evaluation comparison on a finite-free chart".

- lem-amb-root-tower-pullback-coherence vs lem-pur-tate-inverse-limit-base-change: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Base change of an ell-adic inverse-limit tower and of its finite reduction tensor".

- lem-amb-root-tower-pullback-coherence vs def-pur-semilinear-tensor-presentation-data: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Data for semilinear transport of sheaf tensor presentations".

- lem-amb-root-tower-pullback-coherence vs lem-pur-normalized-tensor-constraint-transport: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Transport of normalized tensor constraints through coherent realization".

- lem-amb-root-tower-pullback-coherence vs lem-pur-proetale-inverse-image-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison".

- lem-amb-root-tower-pullback-coherence vs def-pur-cochain-coefficient-arrows: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical scalar-association and transition arrows on cochain sheaves".

- lem-amb-root-tower-pullback-coherence vs lem-pur-ringed-site-pullback-pairing-transfer: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Extension of module pairings along a ringed site morphism".

- lem-amb-root-tower-pullback-coherence vs lem-pur-module-tensor-monoidal-equations: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Associativity and symmetry of the canonical ordinary module tensor comparison".

- lem-amb-root-tower-pullback-coherence vs lem-pur-cochain-pullback-tensor-coherence: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Signed tensor comparison and composition on cochain sheaf pullbacks".

- lem-amb-root-tower-pullback-coherence vs def-pur-cochain-tensor-coherence-data: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical cochain ringed-pullback and coherence data".

- lem-amb-root-tower-pullback-coherence vs lem-pur-torsion-line-system-base-change: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized tensor extension of compatible torsion line systems".

- lem-amb-root-tower-pullback-coherence vs lem-pur-canonical-ringed-tensor-comparison-independent-universes: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Existing normalized ordinary tensor comparison with independent site universes".

- lem-amb-root-tower-pullback-coherence vs def-sp-proetale-scalar-mate-identifications: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications".

- lem-amb-root-tower-pullback-coherence vs lem-pur-strict-coefficient-comparison-calculus: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Simultaneous strict coefficient comparisons on ring-sheaf towers".

- lem-amb-root-tower-pullback-coherence vs lem-pur-inverse-image-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "The unit-normalized tensor comparison for an isomorphic base change".

- lem-amb-root-tower-pullback-coherence vs def-sp-constant-scalar-pullback-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical constant-coefficient scalar extension, direct image and pullback comparison".

- lem-amb-root-tower-pullback-coherence vs lem-pur-independent-ringed-tensorator-existence: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Existence of the tensorator for fixed scalar insertion at independent site sizes".

- lem-amb-root-tower-pullback-coherence vs lem-pur-module-tensor-generator-calculus: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Pure tensors and normalized insertion naturality for sheaf modules".

- lem-amb-root-tower-pullback-coherence vs lem-pur-cochain-comparison-monoidal-equations: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Monoidal equations for the canonical cochain pullback comparison".

- lem-amb-root-tower-pullback-coherence vs lem-pur-independent-normalized-scalar-composition: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized composition of module scalar extensions".

- lem-amb-root-tower-pullback-coherence vs lem-pur-inverse-image-scalar-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Inverse image commutes with extension of scalars, with its unit formula".

- lem-amb-root-tower-pullback-coherence vs lem-pur-inverse-image-scalar-unit-normalization: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical algebraic realization and scalar-unit normalization of pro-etale inverse image".

- lem-amb-root-tower-pullback-coherence vs lem-kun-derived-pullback-composition-monoidal: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical derived etale inverse-image composition is monoidal".

- lem-amb-root-tower-pullback-coherence vs def-pur-cochain-coefficient-universe-transport: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Canonical common-universe transport of ring and module sheaves".

- lem-amb-root-tower-pullback-coherence vs lem-pur-coefficient-scalar-units: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Multiplication units for derived scalar extension".

- lem-amb-root-tower-pullback-coherence vs lem-sf-reduction-pull-finite-evaluation: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Finite evaluation respects the specified reduction/pullback comparison".

- lem-amb-root-tower-pullback-coherence vs lem-pur-independent-inverse-image-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized tensor comparison for an algebraic inverse image at independent site sizes".

- lem-amb-root-tower-pullback-coherence vs lem-pur-varying-ring-tensor-comparison: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Normalized tensor comparison for one varying-ring inverse image".

- lem-amb-root-tower-pullback-coherence vs lem-sf-finite-field-local-tensor-model: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Localized inverse-image constant models under field scalar extension".

- lem-amb-root-tower-pullback-coherence vs lem-pur-module-tensor-coefficient-equations: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Ordinary module tensor equations for coefficient change".

- lem-amb-root-tower-pullback-coherence vs lem-pur-isomorphism-inverse-image-tensor-hom: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Inverse image along an isomorphism of schemes commutes with tensor products and sheaf Hom".

- lem-amb-root-tower-pullback-coherence vs lem-pd-generalized-tensor-normalization-unit-equation: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Generalized tensor normalization implies the geometric-unit equation".

- lem-amb-root-tower-pullback-coherence vs lem-pd-ringed-tensor-adjunction-mate: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Identify ringed tensor comparisons with specified adjunction mates".

- lem-amb-root-tower-pullback-coherence vs lem-pd-section-ordinary-oplax-normalization: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Ordinary module pullback oplax mate on balanced generators".

- lem-amb-root-tower-pullback-coherence vs lem-pod-etale-stalk-tensor-scalar: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Geometric stalks commute with tensor products and scalar extension on the etale site".

- lem-amb-root-tower-pullback-coherence vs lem-pod-lisse-tensor-and-scalar-extension: the new task asserts identity/composition for the specified root adjuncts and their limit and ordinary tensor maps, not general tensor comparisons or their derived realizations; the existing node is "Tensor products, scalar extension and stalks of lisse sheaves of modules".

- lem-amb-root-tower-finite-tensor vs lem-amb-tate-root-projection-reduction: the new task has arbitrary annihilated scalar algebra B, exact root projection data and its local inverse, but no prescribed finite twist P_T, j_T, level-transition equations or scheme-pullback clauses.

- lem-amb-root-tower-pullback-coherence vs lem-amb-tate-root-projection-reduction: the new task has arbitrary scalar algebra B and root/tensor pullback maps without any finite-comparison invertibility or prescribed finite twist P_T.

- lem-amb-root-tower-finite-tensor vs lem-pur-twist-sheaf-locally-free: that node asserts local rank-one freeness and finite reduction over the completed coefficient sheaf; this task fixes projections and their kernels over constant (Z_l)_T and normalizes the inverse by local lifts.

- lem-amb-root-tower-finite-tensor vs lem-pur-twist-root-local-models: that node gives existence of local trivializations and reductions from the completed root module; it does not give the constant-ring normalized local inverse or the sectionwise kernel division.

- lem-amb-root-tower-finite-tensor vs lem-weil-pbc-sheaf-tensor-ideal-quotient: that general quotient identity neither proves that p_r is locally surjective nor computes its kernel; it can support a future proof, but does not state this task.

- lem-amb-root-tower-pullback-coherence vs lem-pur-tate-inverse-limit-base-change: the existing general tower lemma assumes finite comparisons are isomorphisms obeying identity/composition. This task proves those identity/composition equations for the specified root adjuncts without assuming invertibility, and constructs the semilinear root cone. It is not a specialization satisfying the existing lemma's hypotheses without additional work.


## Preserved arguments and ownership

The following are the exact nine returned proof texts, not proof fields of the new unsplit nodes. Steps 2-4 belong to the finite-tensor task, steps 6-8 and the coherence content of step 9 belong to the pullback task. Steps 1 and 5 remain in the parent. Step 9's empty-scheme and annihilation observations are checked in both tasks and in the assembly. Each future worker has its full argument here, while the new node itself remains statement-only.


### Returned step 1

Give $L_T$ its $Z_T$-action by $(a x)_s=x_s^{a\bmod\ell^s}$; the power transitions respect reduction of the exponent, so this is an action on compatible tuples. In additive module notation, define $j_T((x\otimes b)\otimes a)=x\otimes ba$ and its inverse by $x\otimes a\mapsto(x\otimes1)\otimes a$. The balancing relations make both maps well defined, and their composites are the identity on pure tensors. Sheafify these natural sectionwise formulas. The definition of $P_T$ identifies the first source with the prescribed finite twist.

Uses: def-pur-roots-of-unity-sheaf, def-pur-sheaf-inverse-limit, def-coefficient-twists-detailed, def-pur-sheaf-tensor-product.

Source: literature/stacks-project/sites-modules.tex; Tag 03EK, section-tensor-product: sheaf tensors and associativity; finite twist definition in the cited blueprint.


### Returned step 2

The projections $p_{r,T}$ are locally surjective. Indeed, apply lem-pur-twist-root-transitions to every consecutive power map. The general-site abelian epi criterion makes it locally surjective on underlying sets, and the set epi criterion makes it an epimorphism of set sheaves. Given an object $U$ and $u\in\mu_{\ell^r}(U)$, cover $U$ by the affine objects $V_i$ weakly contractible for the full $T_{\mathrm{proet}}$ site. On each fixed $V_i$, every consecutive transition is surjective on sections by that precise weak contractibility assertion. Set $x_r=u|_{V_i}$, define $x_s=u|_{V_i}^{\ell^{r-s}}$ for $s<r$, and choose recursively $x_{s+1}$ above $x_s$ for $s\geq r$. This gives a compatible tuple, hence an element of $L_T(V_i)$ with $r$th projection $u|_{V_i}$. All uses are on the full site; no infinite refinement of etale covers is asserted.

Uses: lem-pur-twist-root-transitions, lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective, lem-weil-pbc-site-sheaf-sets-epi-locally-surjective, lem-weil-pbc-proetale-affine-wcontractible-covering-family, def-pur-sheaf-inverse-limit.

Source: literature/stacks-project/proetale.tex; Tag 0990, lemma-proetale-enough-w-contractible; sites.tex Tag 090K, lemma-w-contractible; Kummer transitions from etale-cohomology.tex Tag 03PK.


### Returned step 3

Compute the kernel on every object $U$. If $x=(x_s)_s\in L_T(U)$ has $x_r=1$, put $y_s=x_{s+r}$. Since $x_{s+r}^{\ell^s}=x_r=1$, this really belongs to $\mu_{\ell^s}(U)$, and $y_{s+1}^\ell=y_s$. Also $y_s^{\ell^r}=x_s$. Conversely $(\ell^r y)_r=y_r^{\ell^r}=1$ for every $y$. Thus in additive notation $\ker p_r(U)=\ell^rL_T(U)$, with an explicit division map on the kernel, compatible with restrictions.

Uses: def-pur-roots-of-unity-sheaf, def-pur-sheaf-inverse-limit.

Source: literature/stacks-project/proetale.tex; Elementary coordinate calculation for the root inverse system; applied below the vector-bundle integration coefficient convention.


### Returned step 4

Put $H=L_T\otimes_{Z_T}A_T$, which is killed by $\ell^r$ since $\ell^rA=0$. For local sections $u$ of $\mu_{\ell^r}$ and $a$ of $A_T$, choose local lifts $x$ of $u$ by step 2 and set $B(u,a)=x\otimes a$. Two lifts differ by $\ell^r y$ by step 3, so their tensors differ by $y\otimes\ell^ra=0$. The local outputs therefore glue uniquely and commute with restrictions. Addition in either input follows by choosing lifts $x+x'$ and by distributivity of the tensor. For fixed $a$ this is an additive map to $H$ on the slice site, so lem-pur-torsion-sheaf-constant-module (2) makes it $R_{r,T}$-linear; both source and target are killed by $\ell^r$. Consequently $B(cu,a)=B(u,ca)$ for local $c\in R_{r,T}$, and $B(u,aa')=a'B(u,a)$. The universal property of the sheaf tensor gives an $A_T$-linear map $D_{r,T}\to H$. Conversely $x\otimes a\mapsto p_r(x)\otimes a$ is $Z_T$-balanced, since the action in step 1 projects to exponent reduction. Both composites are identity: on $x\otimes a$ choose the lift $x$, and on $u\otimes a$ use any local lift of $u$. The pure-tensor determination statement proves equality of the resulting sheaf maps. Compose $H\cong D_{r,T}$ with $j_T$ to obtain precisely $\theta_{r,T}$. No exactness of tensoring with $A$ was used.

Uses: def-pur-sheaf-tensor-product, def-weil-pbc-ringed-tensor-section-calculus, lem-pur-torsion-sheaf-constant-module.

Source: literature/stacks-project/sites-modules.tex; Tags 03EK, section-tensor-product, and 03CY, lemma-sheafification-presheaf-modules; agent-written local-lift inverse using steps 2-3.


### Returned step 5

For $r'\geq r$, apply both sides of the asserted transition equation to $j_T^{-1}(x\otimes a)$. They give respectively $x_{r'}^{\ell^{r'-r}}\otimes a$ and $x_r\otimes a$, which agree by compatibility of the tuple. Pure tensors determine the maps, so $(P_{r',r}\otimes1)\theta_{r',T}=\theta_{r,T}$. In particular the transition is $\theta_{r,T}\theta_{r',T}^{-1}$ and is invertible. For three levels, the exponent identity $\ell^{r''-r'}\ell^{r'-r}=\ell^{r''-r}$ proves composition; at equal levels the exponent is $1$. The tensors over the different finite rings are well defined because each power map is linear after restriction to the larger finite ring and $A$ factors through the smaller quotient.

Uses: def-pur-roots-of-unity-sheaf, def-pur-sheaf-tensor-product, def-weil-pbc-ringed-tensor-section-calculus.

Source: literature/stacks-project/sites-modules.tex; Tag 03EK, section-tensor-product; defining power-transition formula in def-pur-roots-of-unity-sheaf.


### Returned step 6

For $v:T'\to T$, lem-pur-roots-of-unity-inverse-image-iso (1)-(2) says exactly that $c^v_s$ commutes with the power transitions and is semilinear over the constant finite ring maps. It also obeys identity and composition laws under the canonical inverse-image identifications: by def-pur-roots-of-unity-inverse-image its adjunct on an object $U\to T$ is the pullback of the same unit along $T'\times_TU\to U$. For $w:T''\to T'$, the iterated pullback on $T''\times_{T'}(T'\times_TU)$ is the pullback on $T''\times_TU$, because the canonical fibre-product identification commutes with the projections and pullback of global functions respects composition. Hence these adjuncts are equal, and the adjunction bijection gives $c^{v\circ w}_s=c^w_s\,w^{-1}(c^v_s)$ after the comparison isomorphism. The identity projection gives $c^{\mathrm{id}}_s=\mathrm{id}$. These are equalities of the specified maps, rather than choices of isomorphisms.

Uses: lem-pur-roots-of-unity-inverse-image-iso, def-pur-roots-of-unity-inverse-image, def-weil-proetale-inverse-image, lem-weil-pbc-left-exact-site-inverse-image-tensor.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-amb-vector-bundle-purity.proof.md; Paragraph 1, functorial finite Tate coefficients; explicit adjunct computation using the root comparison definition and canonical site inverse-image composition.


### Returned step 7

The maps $c^v_s\,v^{-1}p_{s,T}$ form a cone by the transition equation in step 6. Apply the universal property of the limit on $T'_{\mathrm{proet}}$ to obtain $c^v_L:v^{-1}L_T\to L_{T'}$. Its projection equations are exactly those of the statement, and joint uniqueness of maps to a limit proves uniqueness. It is semilinear for the constant $\mathbf Z_\ell$ map: after $p_{s,T'}$ this says that pulling back an exponent and reducing it modulo $\ell^s$ gives the same scalar as reducing first, followed by the finite constant-ring map. This is the semilinearity in step 6 and the coordinatewise action in step 1, so the projections prove the assertion. This construction uses a cone into $L_{T'}$, never an assertion that $v^{-1}$ preserves the infinite limit.

Uses: def-pur-sheaf-inverse-limit, lem-pur-roots-of-unity-inverse-image-iso, def-weil-proetale-inverse-image, def-pur-roots-of-unity-sheaf.

Source: literature/stacks-project/proetale.tex; Root inverse-limit universal property; def-pur-sheaf-inverse-limit (Stacks Tags 03DB and 03CO).


### Returned step 8

The structure maps $c^v_\Lambda:v^{-1}\Lambda_T\to\Lambda_{T'}$ of the constant coefficient rings ($\Lambda=\mathbf Z_\ell,\mathbf Z/\ell^r,A$) are the canonical ring-sheaf isomorphisms of lem-pe-constant-left-module-inverse-image for the geometric morphism $v_{\mathrm{proet}}$; this is the identification of the statement. Apply lem-weil-pbc-ringed-topoi-module-pullback-tensor to the pro-etale geometric morphism and these constant coefficient ring maps. Together with $j_T,j_{T'}$ this identifies $v^*P_T$ with $v^{-1}L_T\otimes_{v^{-1}Z_T}A_{T'}$. The semilinear map of step 7 induces $x\otimes a\mapsto c^v_L(x)\otimes a$; this is the required $b_v$ after the stated identifications. On a pure tensor, the two sides of the required square are $p_{r,T'}c^v_L(x)\otimes a$ and $c^v_r(v^{-1}p_{r,T}(x))\otimes a$. Step 7 equates these expressions. The pure-tensor determination property gives equality of the sheaf morphisms, proving the full square with the specified root maps.

Uses: lem-weil-pbc-ringed-topoi-module-pullback-tensor, def-weil-pbc-ringed-tensor-section-calculus, def-weil-proetale-inverse-image, def-pur-sheaf-inverse-limit, lem-pe-constant-left-module-inverse-image.

Source: literature/stacks-project/sites-modules.tex; Tag 03EL, lemma-tensor-product-pullback, with Tag 03EK pure tensors and the root projection equations.


### Returned step 9

For the identity morphism, every projection of $c_L^{\mathrm{id}}$ equals $p_s$, so $c_L^{\mathrm{id}}=\mathrm{id}$. For $T''\xrightarrow w T'\xrightarrow v T$, project $c_L^w\,w^{-1}(c_L^v)$ to level $s$. Using step 7 twice gives $c_s^w\,w^{-1}(c_s^v)\,(v\circ w)^{-1}p_{s,T}$ after the canonical comparison; step 6 identifies this with $c_s^{v\circ w}\,(v\circ w)^{-1}p_{s,T}$. Limit uniqueness gives the composition law for $c_L$. On a pure tensor both the composite pullback map for $b_w,w^*b_v$ and $b_{v\circ w}$ therefore send $x\otimes a$ to $c_L^{v\circ w}(x)\otimes a$. Identity and composition follow from pure-tensor determination, the canonical monoidal inverse-image comparisons, and the compatibility of the constant-ring identifications with composition of geometric morphisms stated in lem-pe-constant-left-module-inverse-image. On the empty scheme all these formulas are the unique maps of zero sheaves. Every inverse constructed in step 4 uses only $\ell^rA=0$, so the proof imposes neither flatness over $\mathbf Z/\ell^r$ nor any divisibility of $n$ by the ramification index.

Uses: def-pur-sheaf-inverse-limit, def-weil-pbc-ringed-tensor-section-calculus, lem-weil-pbc-left-exact-site-inverse-image-tensor, lem-weil-pbc-ringed-topoi-module-pullback-tensor, lem-pe-constant-left-module-inverse-image.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-amb-vector-bundle-purity.proof.md; Paragraph 1, Tate coefficient pullback in vector-bundle integration; explicit root-coordinate and tensor coherence calculation.
