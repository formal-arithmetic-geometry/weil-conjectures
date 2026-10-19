# Worker report — Q102

## Files written
- dag/nodes/sec-deligne-laumon-a1/lem-per-strict-log-jacobian-criterion.json: item, split, original statement retained.
- dag/nodes/sec-deligne-laumon-a1/lem-per-etale-local-infinitesimal-lifts-smooth.json: one new statement-only node; no Mathlib match.
- citations.json: full verbatim statements for every cited step.

## Attachments
None. Searched the item tag and log smooth/Jacobian notions in /home/ubuntu/weil-src-slopmaster2/WeilConjectures. Its logarithmic structures and this criterion have no declaration there; logarithmic power series are unrelated.

## WANTED
WANTED: Kato, Logarithmic structures of Fontaine--Illusie, section 3, especially 3.12, for lem-per-strict-log-jacobian-criterion. The local ILO source cites this result but does not prove it. An online PDF reference was located but its screenshot access hit provider HTTP 429; it was not used as evidence. The proof_origin is agent, not document.

## Source and route audit
Read local ILO Expose X Proposition 1.2 and proof, printed pp.136--139, especially p.138. It uses strictness, log smoothness of both objects over the base, and injectivity on logarithmic differentials to obtain smoothness. The imported item states precisely that general input, not the equivariant preparation theorem. No group-action hypothesis is needed here. The current unit and chapter records were read; this is an internal preparation ingredient of the ancestor's Step 3, not a replacement of a unit-level argument. Blueprint searches `log smooth`, `Jacobian`, `infinitesimal`, `lifting` found no blueprint version of the new general criterion. Whole-DAG statement searches included formal smoothness, lifting, etale-local lifts and the source tags; relevant existing nodes were opened and reused.

The new node is an etale-local variant of Stacks 02H6, more-morphisms.tex, lemma-smooth-formally-smooth, whose proof's sheaf of lifts and derivation torsor were read. Also read etale-cohomology.tex theorem-zariski-fpqc-quasi-coherent, 03P2. Its intended downstream proof is: the sheaf of lifts is locally nonempty by hypothesis and is a torsor under Hom(a_0^*Omega, I); Omega is finitely presented because f is lfp, so this Hom is quasi-coherent. On the affine test scheme H^1_et of that quasi-coherent module vanishes by the comparison and affine vanishing, so the torsor has a section. Then 02H6 applies. This argument is guidance in this report only; the new node has no proof. It is a generic scheme fact, with no log structure or cotangent-map injectivity hypothesis, so it does not move a clause of the item into a child.

## Faults corrected
The imported proof was empty. In particular its reference to the Jacobian criterion did not supply a split. The new proof spells out the sign of the correction, the effect on both functions and log sections, and the need for an etale-local-to-global scheme criterion. No statement dispute or statement weakening.

## Review by Q102
Step 1 uses exactly the finite local freeness and etale-localization assertions of lem-per-log-smooth-infinitesimal-calculus and the injective-residue clause of lem-pc-finite-free-map-residue-localization-strong. The geometric residue field is an extension of the ordinary residue field, and injectivity descends by the vector-space basis argument written there. All matrices are finite; identities spread with finitely many equalities, not a finiteness assumption on a test scheme. The retraction has direction F to E, so it extends covectors on E to F.

Step 2 uses the lfp conclusion of the calculus twice, the statement of lem-weil-pbc-lfp-affine-opens-finite-presentation for compatible affines, and lem-weil-pbc-finite-presentation-over-finite-type-algebra with R the base algebra, S'=B the target algebra, S=C the source algebra. In particular finite presentation implies finite type by the displayed generators. Neither affineness of arbitrary intersections nor separatedness is assumed.

Step 3 uses the arbitrary-fine-test-scheme lifting clause of the calculus, not just a definition of log smoothness. A pulled-back finite integral chart is fine even when the test ring is non-Noetherian; saturation of test log structures is not needed. Strictness identifies the source pullback with the target pullback. The pushout description explains the canonical log square directly. The new criterion explicitly permits a covering of the thickening, so this step does not silently claim a global lift.

Step 4 uses both explicit torsor clauses of the same calculus: once for Y/S to measure ha minus b, and once for U/S to change a. The statement actually gives the action formulas on ring and log maps. The computation epsilon*u=-delta uses r*u=1. The final equality follows from the uniqueness of the difference, not from a tangent calculation alone. I^2=0 is exactly what makes the action additive, and I is a module on T_0. No flatness of h has been assumed.

Step 5 uses the full new criterion (lfp plus all affine square-zero tests) and the pointwise clause of lem-trf-etale-source-smoothness, which was read in full. The latter requires an etale neighborhood, not a globally surjective single map, in its pointwise assertion; this is exactly our situation. All four off-unit tools are declared with their specific roles.

For the new node I checked the hypotheses against the sheaf-of-lifts proof of 02H6 and the etale cohomology comparison in 03P2. Finite presentation is retained, test schemes are arbitrary affine schemes, and no global lift is assumed. Mathlib hits were read: algebra lifting theorems do not globalize etale-local solutions on arbitrary scheme tests in one line. Small cases: empty V is vacuous and smooth; an identity has its obvious lift; a finite inseparable field extension fails the lifting premise; a non-smooth closed immersion has a square-zero obstruction, which cannot disappear on a faithfully flat etale cover. For the item, rank(E)=0 gives the unique zero defect, equal ranks give the same correction with a two-sided differential isomorphism, and trivial log structures recover the usual smooth Jacobian argument. In characteristic p, t mapping to t^p fails injectivity; the boundary inclusion into (A^1,0) is not log smooth over the trivial base, so is not a counterexample. The strictness hypothesis was used explicitly rather than discarded. All proof steps have fewer than 2000 characters; the separate general descent lemma is the only hidden lemma found and was extracted.

## Not duplicates
lem-per-etale-local-infinitesimal-lifts-smooth vs def-pbc-canonical-coherent-etale-comparison: existing node is Canonical normalized coherent-etale comparison and transported additive action; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs def-pbc-etale-additive-cech-normalization: existing node is Augmentation normalization of additive etale Cech edges; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs def-sbc-smooth-morphisms: existing node is Smooth morphisms; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. Its definition requires a global affine-test lift; upgrading etale-local solutions is the additional theorem here.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-additive-cech-beta-quasi-iso: existing node is Fixed affine additive coefficient augmentation quasi-isomorphism; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-additive-cech-coefficient-columns: existing node is Fixed affine additive coefficient column augmentations are quasi-isomorphisms; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-additive-cech-coefficient-horizontal: existing node is Fixed additive coefficient maps commute with horizontal differentials; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-additive-cohomology-base-change-square: existing node is Linear untensored additive cohomology base-change square; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-additive-cohomology-linear-base-change: existing node is Canonical linear scalar extension of additive first etale cohomology; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-additive-cohomology-pullback-comparison: existing node is Coordinate-normalized additive cohomology pullback comparison; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-additive-cohomology-tensor-kernel: existing node is Trivial kernel of additive cohomology tensor pullback; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-additive-cohomology-tensor-surjective: existing node is Surjectivity of additive cohomology tensor pullback; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-additive-scalar-base-change: existing node is Scalar-compatible canonical base change for additive first cohomology; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-canonical-additive-cohomology-square: existing node is Canonical additive structure-sheaf cohomology square; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-coherent-etale-comparison-morphism: existing node is Dimension shifting for normalized coherent cohomology maps; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-coherent-etale-effacing-sequence: existing node is Simultaneous acyclic sequences on the Zariski and etale sites; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-coherent-etale-normalized-additive-map: existing node is Existence of a normalized additive coherent comparison; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-augmentation-homology: existing node is Homology of the explicit additive Cech augmentations; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-augmentation-prescribed-class: existing node is Cech augmentation compatibility for a prescribed target global class; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-augmentation-transfer: existing node is Transport of an equal pair of additive Cech augmentation classes; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-beta-homology: existing node is Additive cycle lift and bijective homology map for beta; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-inverse-image: existing node is Etale additive Cech coordinates and inverse-image cocycles; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-normalized-existence: existing node is Existence of augmentation-normalized additive etale Cech edges; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-normalized-inverse-image: existing node is Inverse-image class of matched cycles under normalized additive etale edges; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-normalized-scalar: existing node is Scalar compatibility of augmentation-normalized additive etale Cech edges; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-pullback-chain-transfer: existing node is Pullback chain maps preserving additive Cech augmentations; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-pullback-total-transfer: existing node is Tuple restriction of an augmented comparison into a Cech total map; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pbc-etale-additive-cech-resolution-transfer: existing node is Transfer of additive Cech augmentations between resolutions; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-pc-proper-base-change: existing node is Proper and smooth morphisms are stable under base change; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-additive-cohomology-finite-dimensional: existing node is Finite-dimensionality of the section-induced scalar action on first additive cohomology; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-additive-cohomology-finite-scalar-model: existing node is Finite-dimensional scalar model of first additive etale cohomology; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-additive-cohomology-scalar-comparison: existing node is Scalar-compatible comparison of derived additive etale and ordinary structure-sheaf first cohomology; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-affine-open-cech-derived-evaluation: existing node is Acyclic affine-open cover computes derived evaluation; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-affine-open-cech-derived-evaluation-succ: existing node is Positive-degree affine-open Čech derived evaluation; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-affine-open-cech-resolution-columns: existing node is Affine-intersection vertical homology of the open Čech resolution; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-base-change-geometric: existing node is Pointwise etaleness is preserved and reflected by field extension; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-qcoherent-cohomology-ulift: existing node is Quasi-coherent etale cohomology is unchanged by coefficient universe lift; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-qcoherent-source-comparison-natural: existing node is Natural comparison of lifted tensor-sheaf cohomology with ordinary H; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-qcoherent-ulift-cohomology-natural: existing node is Natural coefficient-universe comparison for quasi-coherent etale cohomology; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-qcoherent-ulift-cohomology-natural-succ: existing node is Natural coefficient-universe comparison for positive-degree etale cohomology; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-qcoherent-ulift-finite-cech-comparison: existing node is Positive lifted etale cohomology computed by a finite affine section complex; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-tensor-direct-image-identification: existing node is Natural direct-image identification of tensor-sections sheaves; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-tensor-positive-direct-image-vanishing: existing node is Positive direct images of quasi-coherent tensor-sections sheaves vanish; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-tensor-positive-object-cohomology: existing node is Positive object cohomology of tensor-sections sheaves vanishes on affine opens; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-zariski-abelian-positive-comparison: existing node is Positive-degree natural comparison for the underlying Zariski abelian sheaf; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-etale-zariski-qcoh-comparison: existing node is Etale and Zariski cohomology of quasi-coherent modules agree, naturally in the module; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-singleton-tensor-cech-coface-evaluation: existing node is Evaluation of a singleton tensor Čech coface; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-singleton-tensor-cech-normalized-coface: existing node is Geometric Čech coface of normalized singleton tensor sections; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-sc-singleton-tensor-normalized-restriction: existing node is Restriction of evaluated normalized singleton tensor sections; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-coherent-frobenius-comparison: existing node is Frobenius compatibility of the canonical additive/coherent cohomology comparisons; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-etale-smooth-zero-dimensional-fibres: existing node is An etale morphism is smooth with zero-dimensional fibres; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-qcoherent-cohomology-comparison-pullback: existing node is Quasi-coherent etale cohomology comparison natural in scheme pullback; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-qcoherent-normalized-comparison-exists: existing node is Existence and uniqueness of the normalized comparison on a quasi-compact separated scheme; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-qcoherent-normalized-pullback-square: existing node is The normalized comparison commutes with the canonical pullback cohomology maps; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-qcoherent-pullback-sections-map: existing node is Structural pullback of a tensor section across a square; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-smooth-coproduct: existing node is A disjoint union of smooth schemes over a base is smooth; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-smooth-curve-etale-structure-direct-images: existing node is Etale structure-sheaf cohomology in smooth proper curve families; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension: existing node is Differentials of a smooth morphism are free near a point, of rank the fibre dimension; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-smooth-locally-standard-smooth: existing node is Smooth morphisms are locally standard smooth; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-smooth-restrict-open-subschemes: existing node is Smoothness under restriction to open subschemes, composition with an open immersion, and isomorphism; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-smooth-ring-map-iff-smooth-affine: existing node is A ring map is smooth iff the morphism of spectra is smooth; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. It compares ring and affine-scheme smoothness, without etale-local lifting hypotheses.

lem-per-etale-local-infinitesimal-lifts-smooth vs lem-weil-pbc-smooth-zero-differentials-affine-open-etale: existing node is A smooth morphism is etale on an affine open where the differentials vanish; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-coherent-etale-comparison-pullback: existing node is Canonical coherent-etale comparison respects structural pullback; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-coherent-power-comparison: existing node is Coherent power semilinearity and normalized etale power comparison; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-amitsur: existing node is Affine singleton tensor-section Cech complex as Amitsur; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-cofaces: existing node is Extending the singleton pure-tensor coface equation; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-degree-comparison: existing node is Normalized degree comparisons for affine singleton tensor sections; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-degree-comparison-bijective: existing node is Bijectivity of normalized affine degree comparison homomorphisms; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-degree-comparison-degree: existing node is Degreewise normalized affine singleton tensor comparison; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-degree-comparison-hom: existing node is Normalized affine degree comparison homomorphism; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-degree-comparison-hom-normalization: existing node is Pure-tensor normalization of the affine degree comparison homomorphism; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-degree-comparison-inverse: existing node is Two-sided inverse of a normalized affine degree comparison; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-degree-kernel: existing node is A normalized affine singleton comparison has zero kernel.; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-degree-surjective: existing node is A normalized affine singleton comparison lifts every target section.; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-pure-coface-fixed: existing node is Fixed-degree pure-tensor coface equation; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-pure-cofaces: existing node is Pure-tensor coface equation for normalized singleton sections; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-singleton-tensor-sections-span: existing node is Normalized pure sections generate the affine iterated pullback sections.; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-tensor-cech-amitsur-comparison: existing node is Comparison of lifted affine tensor-section Cech complexes with Amitsur complexes; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-affine-tensor-cech-vanishing: existing node is Lifted tensor-section sheaves have zero positive finite affine Cech cohomology; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-singleton-tensor-cech-coface-map-down: existing node is Downstairs evaluation of the raw coface map; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-singleton-tensor-cech-coface-raw-projection: existing node is Raw categorical coface projection; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-singleton-tensor-normalization-evaluation: existing node is Additive evaluation of the normalized singleton tensor comparison; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-singleton-tensor-normalized-range: existing node is Pure normalized sections lie in the evaluated comparison range.; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-etale-singleton-tensor-pure-image: existing node is Canonical evaluation of a normalized lifted pure tensor.; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-w2-additive-cech-beta-representative: existing node is Beta cycles represent arbitrary total homology classes; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-w2-additive-cech-common-representative: existing node is Common augmentation representatives for additive etale Cech cohomology; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs new-w2-additive-cech-scalar-transport: existing node is Scalar transport of common additive etale augmentation representatives; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs sbc-lem-affine-space-smooth: existing node is Affine space is smooth; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

lem-per-etale-local-infinitesimal-lifts-smooth vs sbc-lem-smooth-criterion: existing node is Smoothness by flatness and smooth fibres; it does not assert smoothness from etale-local solutions of every affine square-zero lifting problem. The shared tag supplies a scheme/cohomology tool in that different statement, not this lifting criterion.

## Unfinished
No part of the assigned one-level split remains. The new scheme criterion is intentionally unsplit for its future worker. No Lean was written or compiled.
