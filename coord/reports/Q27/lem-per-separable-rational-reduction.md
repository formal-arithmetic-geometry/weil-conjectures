# Q27: lem-per-separable-rational-reduction

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-separable-rational-reduction.json: statement preserved, now split into five steps.
- dag/nodes/sec-deligne-laumon-a1/lem-per-normalized-generically-finite-domination.json: statement-only geometric prerequisite; Mathlib searches found no match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-integral-trace-dual-lattice.json: statement-only trace-coordinate sheaf prerequisite; algebraic ingredients occur in Mathlib, but the sheaf statement is not a leaf.
- dag/nodes/sec-deligne-laumon-a1/lem-per-normal-surface-modification-h1-monotone.json: statement-only prerequisite, the injection in Stacks 0AXF; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-normal-surface-modification-torsion-bound.json: statement-only prerequisite, Stacks 0AXJ with its displayed torsion identification; no Mathlib match.
- citations.json: one verbatim statement quotation for every node used by each numbered proof step.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 checkout for the item tag and for rational singularities, reduction to rational singularities, surface modifications, and trace lattices. No project declaration supplies the assertion. The corresponding search of exact upstream master also returned no surface assertion. Mathlib declarations are not project attachments.

## WANTED

None. The Stacks sources used here are present locally.

## Corrections and scope

The item statement agrees with Stacks Tag 0AXL (resolve-lemma-go-up-separable) and was preserved. The imported node had no proof. The phrase “reduction to rational singularities” is a uniform bound on modification H1 lengths, not a claim that every singularity in the extension is rational. This meaning is exactly the statement of def-per-rational-surface-singularity.

The source's reduction to a finite normal model uses domination and H1 monotonicity implicitly. They are now explicit prerequisites. The proof also fills in the scalar bookkeeping omitted in the source: the trace comparison is R-linear, its target has bounded R-length, but the uniform torsion input initially gives S-length. The residue-field degree converts the torsion bound before the final estimate. There is no division by the degree of the extension, and no tame or characteristic-zero hypothesis.

All pre-existing search results and searches.jsonl were retained. I read the earlier research result files and reused their exact queries. The additional searches concern the sheaf version of the trace lattice, which the earlier algebra-only queries did not test. Entries reproduce executed commands and their actual results; no unavailable response was relabeled as a negative search. Four new nodes are unsplit statements only. Their arguments below explain the intended next work without putting proof sketches into their statements.

## Unfinished work

No unfinished part of this one-level split. The four new prerequisites remain future stage-1 items as required. No Lean was written, compiled, or built. No live file or launcher was edited, and no git command was run in either read-only checkout.

## Review by Q27

I read Stacks resolve.tex from lemma-exact-sequence through lemma-go-up-separable, including the full proof of lemma-bound-a-torsion and equation-a-torsion. I also read flat.tex lemma-finite-after-blowing-up (0B49), and fields.tex lemma-separable-trace-pairing (0BIL). The normalization reference 035S is the Nagata-normalization lemma, not an excellence-only normalization claim. I read the chapter and unit records and the ancestor's current proof: this is the existing technical surface-resolution branch below dimension-normalized duality in lem-per-artin-gabber-affine-curve, via the ancestor chain already recorded on the item. The unit and chapter route are unchanged; this is not a unit key-node delivery.

Step 1 uses def-per-rational-surface-singularity for precisely the uniform length definition, and lem-per-integral-trace-dual-lattice for the basis and nonzero discriminant fixed independently of the model. Its finite injective normal-domain and separability hypotheses are exactly those of the item. The trace prerequisite packages the geometric integral-trace restriction as well as the algebra: locally on an affine normal model, an element integral over the coordinate ring has integral trace, and that trace lies in the coordinate ring by normality. These restrictions agree because they are all the same map on the function fields. Nondegeneracy gives injectivity. If psi is the map sending a coordinate tuple to its b_i-linear combination, Phi psi has matrix T; composing psi with the adjugate of T shows that d times every target section lies in the image. This is a sheaf assertion for every normal model, not a declaration of Mathlib about one ring trace. I checked the algebraic search hits (nonzero discriminant, integral trace and trace dual bases) against that distinction.

Step 2 uses lem-per-normalized-generically-finite-domination for all three pieces of data it actually needs: the normal R-model, the normal S-model dominating the prescribed Y_0, and the finite map between them. This prerequisite is strictly geometric and contains no H1 or bounded-genus claim. In the source, first restrict to an open on which the proper generically finite map is finite locally free, then use 0B49 and take normal models. One must normalize after forming the appropriate dominant component over the normalized base; merely asserting that normalization commutes with every base change would be wrong. Nagata hypotheses supply finite normalizations. This geometric construction is substantial enough to retain as a prerequisite, rather than mark it elementary. The other cited statement, lem-per-normal-surface-modification-h1-monotone, explicitly states an S-linear injection on H1. I checked this is exactly the initial arrow of 0AXF, with both objects normal modifications over the SAME local ring S and h proper birational. No definition is cited in place of this injection theorem.

The first full delivery dry run passed at 611f3cac63. Final review then made the injective-resolution hypothesis in Step 3 explicit by citing lem-weil-pbc-scheme-modules-enough-injectives and pqf-def-cohomology. The former states exactly that module sheaves on a scheme have enough injectives; the latter states the module-derived global-sections cohomology convention. Global sections preserves kernels directly from sectionwise kernels, so it is left exact. These are existing tools, and the new citations are included in citations.json.

Step 3 applies the trace prerequisite only after the finite normal models and their identified fields have been supplied. The statement really gives Phi injective and d annihilating its cokernel. def-weil-finite-integral-morphism explicitly includes affineness, so the hypothesis of lem-weil-pbc-affine-morphism-cohomology-edge is checked; that node states the edge isomorphism for quasi-coherent modules, not an etale finite-pushforward statement. The structure sheaf is quasi-coherent directly from its affine description. lem-weil-pbc-derived-functor-long-exact explicitly supplies the connecting arrow and exactness for a short exact sequence, and def-sc-zariski-cohomology identifies this cohomology with a right derived global-sections functor. The finite-sum identification is explained using finite sums of injective resolutions; there is no infinite-product commutation assertion. R-linearity gives d ker(alpha)=0. This last inference is the reason the entire H0 of the cokernel need not itself have bounded length.

Step 4 uses lem-per-normal-surface-modification-torsion-bound for exactly H1(Y,O_Y)[d], not for the whole H1. I checked its source 0AXJ proves a bound for Coker(A -> H0(Z,O_Z)), and equation-a-torsion identifies that cokernel with H1[a]; thus the new statement is faithful to the source. The bound is uniform in the modification but may depend on the fixed element. Injectivity R -> S makes d nonzero in S. The other node, lem-exc-semilocal-restriction-length, states the residue-degree-weighted restriction-of-scalars formula. S has one maximal ideal, it contracts to the maximal ideal of R because the homomorphism is local, and the displayed spanning argument proves the residue degree finite from the finite R-module hypothesis. Applying that node to M[d], whose S-length has already been bounded, therefore gives its finite R-length e times as large. I did not apply a formula requiring M finite-length to the full M before proving it.

Step 5 is an elementary chain argument for module length, written out from def-weil-pbc-module-length. It proves the bound eC+nB first over R and then over S, since S-submodule chains are R-submodule chains. The injection of Step 2 returns the estimate to the arbitrary original model. def-per-rational-surface-singularity then gives the conclusion. The constants n, e, B and C depend only on the given ring inclusion and the fixed discriminant, not on Y_0. This carries the boundedness conclusion in the item's own proof rather than moving it into a new node.

For small cases, the identity extension has n=e=1 and may take b_1=1, d=1, with zero trace cokernel; the torsion bound for a unit is zero. The identity modification has H1=0. The new monotonicity assertion allows h to be the identity. The domination assertion allows R=S and gives a common dominating model; it asserts no resolution or regularity. Ramified separable extensions are allowed, where d need not be a unit, so the torsion step remains necessary. Characteristic p and degree divisible by p cause no error: separability makes the pairing nondegenerate even if Tr(1)=0, and the argument never divides by n. Purely inseparable extensions were not admitted into the trace prerequisite. These checks found no statement dispute.

I checked B--E of delivery-errors.md against the actual JSON and sources: complete independently quantified statements with cited or explicit notions, TeX escaping, correct Stacks tags, all non-elementary proof facts supplied by cited statements, no invocation of another node's proof, no re-labeled clause of the item's boundedness assertion, no circular use of the item, and no hidden hypothesis of excellence or invertibility. All five proof steps are below 2000 characters. The generic off-unit cohomology and length lemmas are declared as tool uses with their purpose; they do not replace the unit route. citations.json quotes the actual statements I read.

## Not duplicates
lem-per-integral-trace-dual-lattice vs lem-per-complete-normal-surface-resolution: the existing statement concerns Resolution of complete normal local surfaces; it does not assert the universal trace-coordinate embedding of structure sheaves with one discriminant annihilator.

lem-per-integral-trace-dual-lattice vs lem-per-separable-rational-reduction: the existing statement concerns Bounded modification genus ascends through separable finite extensions; it does not assert the universal trace-coordinate embedding of structure sheaves with one discriminant annihilator.

lem-per-normalized-generically-finite-domination vs lem-trf-conductor-smooth-base-change: the existing statement concerns The conductor ideal of normalization commutes with smooth pullback; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-trf-normalized-blowup-calculus: the existing statement concerns Normalized blowup universal property and smooth comparison; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-trf-alteration-blowup-finite: the existing statement provides finite blowup models without normality; the new statement supplies normal models over the two fixed local surface rings under the weaker Nagata, rather than excellence, hypothesis.

lem-per-normalized-generically-finite-domination vs lem-trf-alteration-finite-refinement: the existing alteration refinement has reduced, not normal, models; the new statement includes the finite normal-model construction over the fixed surface inclusion.

lem-per-normalized-generically-finite-domination vs lem-trf-finite-after-blowup: the existing statement produces a finite locally free strict transform over an admissible blowup but does not assert normality of both models or a normal S-model dominating the prescribed Y; the new statement includes the Nagata normalization step and does not assert the normalized cover is flat.

lem-per-normalized-generically-finite-domination vs lem-per-noetherian-log-pair-strict-resolution: the existing statement concerns Strict boundary resolution of an excellent Noetherian log regular pair; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-per-excellent-quasiprojective-normalized-blowup: the existing statement concerns Normalized blowups preserve quasi-projectivity over an excellent affine base; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-per-potential-dualizing-uniqueness: the existing statement concerns Uniqueness with fixed prime-power local pinnings; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-per-complete-normal-surface-resolution: the existing statement asserts a regular resolution for a complete local surface; the new prerequisite asserts neither completeness nor regularity and does not use that resolution.

lem-per-normalized-generically-finite-domination vs lem-per-separable-rational-reduction: the existing item is the H1 boundedness ascent theorem; the new geometric or trace prerequisite has no boundedness assumption or conclusion.

lem-per-normalized-generically-finite-domination vs lem-per-integral-etale-chart-flatification: the existing statement assumes quasi-excellence and gives finite locally free charts whose sources are not asserted normal; the new diagram assumes only Nagata and normalizes the source without asserting flatness.

lem-per-normalized-generically-finite-domination vs lem-per-excellent-normalized-blowup-tower: the existing statement concerns Geometry of finite normalized point-blowup towers; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-per-alteration-cover-standard-refinement: the existing statement concerns Standard refinement of an arbitrary prime-to-ell alteration cover; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-per-excellent-normalization-preparation: the existing statement normalizes one excellent scheme; the new statement constructs a compatible finite diagram dominating a prescribed modification over Nagata surfaces, which need not be excellent.

lem-per-normalized-generically-finite-domination vs lem-per-normalized-blowup-tower-etale-descent: the existing statement concerns Descent and projectivity of finite normalized blowup towers; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-per-log-regular-projective-log-resolution: the existing statement concerns Projective logarithmic resolution over an excellent affine base; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-per-normal-projective-compactification: the existing statement concerns Normal projective compactification over a complete trait; it does not assert a finite morphism between normal modifications dominating an arbitrary model over a finite inclusion of Nagata local surface rings.

lem-per-normalized-generically-finite-domination vs lem-per-normal-surface-cover-completed-degree: the existing statement starts with a regular excellent surface model and studies completed local degrees; the new geometric statement starts with an arbitrary prescribed normal modification and asserts a dominating finite normal diagram.

The new H1-monotonicity and fixed-element torsion nodes have no existing same-tag node (0AXF and 0AXJ). Searches by concept and the whole-blueprint searches also found no statement giving either result. The existing finite-field trace-pairing lemma is restricted to finite fields, while the existing etale-field trace criterion supplies no normal-model sheaf statement.
