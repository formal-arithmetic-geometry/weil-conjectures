## Worker report

Repair of returned immutable head `4c430c8051a4`, group NG, item
`lem-pod-canonical-coefficient-pullback-reduction`.
The saved packet was inspected and dry-run first, as instructed. Its mechanical
checks passed, but its definitions still had the mathematical faults identified
in the return. This delivery replaces those definitions and the theorem signature.
The node is refreshed from the current shared copy; only its `lean` field changes.
There are no new nodes, dependency repairs or statement corrections.

The module `Sheaf.Paper.CanonicalCoefficientPullbackReduction` defines the actual
maps needed to state the node, then postpones their coefficient-isomorphism
properties and the main theorem. No definition contains `sorry`. The two named
postponed theorems are `canonicalCoefficientModelMaps_isIso` (the coefficient-map,
finite multiplication and reduction isomorphism assertions already in this node)
and `canonicalCoefficientPullbackReduction`. Both have source/blueprint tags and
natural-language proofs. All 23 declarations are listed in `lean.declarations`.

Hypotheses and objects, in the order of the node:

* The global tuple is `(D : FiniteFieldDatum.{u})`, and `_hl : l ≠ D.p` retains the
  distinct-characteristic hypothesis. The section binds `(l : ℕ) [Fact l.Prime]`,
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The integers, uniformizer and quotient rings are the existing Padic coefficient
  constructions, not new data or arbitrary choices.
* `{X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]` is the stated scheme isomorphism.
  `hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)` and the analogous `hY`
  express invertibility of l on BOTH schemes and are passed to the recorded kappa.
* The modules and complexes are on the recorded small `Scheme.ProEt` sites,
  with object universe u+1 and morphism universe u. There is no site-universe
  equality assumption or substitute large site. The existing completed sheaf
  `completedIntegralCoefficientSheafUnrestricted` is R; `integralCoefficientSheaf`
  is B. A Lean index n denotes the paper's positive exponent n+1.
* `canonicalCoefficientIntegralUnit` and `canonicalCoefficientFiniteUnit` send
  1 to 1 in the recorded sectionwise inverse-image module functors, whose actions
  already use the inverse coefficient ring maps. Their inverses, through the
  standard single-complex/derived-single comparisons, are precisely c_R and c_n
  on regular objects (`canonicalCoefficientIntegralComparison` and
  `canonicalCoefficientFiniteComparison`). These are independent of kappa, lambda
  and rho. Their isomorphism proof is postponed as a named clause theorem.
* `P_g` is the existing `integralDerivedPullback l E g`. The regular complex is
  `constantWeilIntegralComplex l E Y` and its flat-term K-flat witness is the
  existing `constantWeilIntegralGood l E Y`. Completeness, constructibility and
  canonical reduction invertibility are supplied by the recorded
  `integralConstantCoefficient_constructible`; they are facts about these
  coefficient objects, not additional assumptions on an arbitrary object.

Canonical maps and all conclusion clauses:

* `canonicalCoefficientKappa l E g hX hY` is EXACTLY
  `inverseImagePullbackComparison l E g hX hY
  (constantWeilIntegralComplex l E Y) (constantWeilIntegralGood l E Y) (𝟙 _)`.
  It is not defined from lambda. Thus the recorded dependency declaration is used
  in the statement through the actual specified Roos augmentation.
* `canonicalCoefficientLambda` is `constantWeilIntegralLambda`, the existing
  normalized finite-multiplication/entire-cone/inverse-completeness composite,
  followed by `canonicalCoefficientInverseImageTransport`. This transport goes
  from the older termwise inverse-image realization to the specified sectionwise
  realization through their independently constructed regular coefficient maps
  c_R. It uses neither kappa nor an existence-only `Nonempty` isomorphism.
* `canonicalCoefficientLambdaFinite` is the inverse of the recorded
  `inverseImageFiniteComparisonComplex` on the finite regular complex. That map
  is the specified x to x tensor 1 map. An inverse of THIS map is uniquely
  determined; it is exactly the finite multiplication x tensor b to c_n^-1(b)x.
  There is no choice of an unspecified multiplication isomorphism.
* `canonicalCoefficientReduction` is the adjoint transpose of the ACTUAL
  `constantCoefficientProjection` under the normalized scalar-reduction
  adjunction. Its chain version is the canonical multiplication reduction h_n.
  `canonicalCoefficientPullbackReductionIso` applies finite pullback to h_n,
  then Res_n, identifying the genuine strict pullback-tower term with
  Res_n Lg_n^* B_Y,n.
* `canonicalCoefficientRho` starts with
  `integralDerivedPullbackComparison.hom.app` at that good regular complex,
  then applies Q to `mappingCocone.fst ≫ Pi.π ... n` of the ACTUAL
  `constantWeilPullbackRoosEndomorphism` and tower, and finally Q of the preceding
  reduction identification. It has source P_g R_Y and target
  Res_n Lg_n^* B_Y,n, in the single integral R_X derived category.
* Conjuncts 1 and 2 assert `kappa ≫ lambda.hom = 𝟙 _` and
  `lambda.hom ≫ kappa = 𝟙 _`. They identify the two independently defined maps;
  they are not `Iso.hom_inv_id` restatements by definition.
* Conjunct 3, for EVERY n, is
  `rho_n ≫ Q.map (Res_n.map lambda_n.hom) = lambda.hom ≫ Fpi_n`.
  Here `canonicalCoefficientProjection` is the degree-zero pi_n as an integral
  derived map. `canonicalCoefficientInverseProjection` is its inverse image,
  rendered through the stated canonical coefficient square as
  `c_R.hom ≫ pi_n,X ≫ Q.map (Res_n.map c_n.inv)`.
  It depends only on coefficient projections and c_R,c_n, never lambda or rho.
  Hence this is the genuine completed-derived-pullback projection equation,
  not a finite ring square used as its replacement.
* `canonicalCoefficientTheta = lambda ≪≫ c_R`. Conjunct 4, for EVERY n, is
  `theta.hom ≫ pi_n,X = rho_n ≫ Q.map (Res_n.map (lambda_n.hom ≫ c_n.hom))`.
  It is the second requested projection identity as an equality of derived
  morphisms with domain P_g R_Y. No predicate hiding a different equation occurs.
* `canonicalCoefficientPullbackTransition` is the recorded pure-tensor pullback
  transition, conjugated by the two canonical h_n reductions.
  `canonicalCoefficientTransition` is the recorded quotient transition on the
  regular complex, conjugated by those reduction maps and restricted to R_X.
  `canonicalCoefficientInverseTransition` transports that actual coefficient
  quotient through c_(n+1),c_n. Conjunct 5 is the adjacent multiplication square
  `pullbackTransition ≫ Res_n(lambda_n) =
  Res_(n+1)(lambda_(n+1)) ≫ inverseTransition` as an equality of CHAIN MAPS,
  before localization or inverse limit. Conjunct 6 additionally asserts
  `rho_(n+1) ≫ Q.map pullbackTransition = rho_n` in the derived category.
  Together these state the transition compatibility of both displayed projection
  identities; the coefficient square supplies the corresponding c_n transport.
* Conjunct 7 identifies `canonicalCoefficientTheta` with the PUBLISHED
  `constantWeilIntegralTheta`, retaining the required normalization for all g
  and hence for the geometric Frobenius specialization in the node. Lambda is
  the published normalized lambda with just the explicit model transport above.
  No cohomological Frobenius claim is introduced. The obsolete
  `canonicalCoefficientThetaProjection` and both duplicated ring-square
  conjuncts have been removed.

Dependency declarations used (names below are qualified by the module namespace
`WeilConjectures`, unless explicitly indicated):

* `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: recorded
  `Padic.finite_coefficientExtensionRing`, reexporting the Padic coefficient ring,
  uniformizer and positive quotient constructions. No new finiteness assumption
  is needed for the maps.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
  The scheme-morphism-properties node is a convention; `CategoryTheory.IsIso`
  and the explicit stalk-unit hypotheses express the properties used here.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` reexports the existing completed
  coefficient sheaf and quotient projections used through the recorded
  `constantCoefficientProjection`; the limit is not reconstructed privately.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`, and
  `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `AlgebraicGeometry.Scheme.isoSectionwiseInverseImage_equivalence` and
  `isoSectionwiseModuleInverseImage`, underlying the specified sectionwise model.
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: recorded
  `IntegralOnSlice.completedTensor`, reexporting the actual global integral
  operations. The pullback used here is `integralDerivedPullback`, with
  `integralDerivedPullbackComparison`, `integralOperationsLevelPullback`,
  `integralOperationsRestrict`, `integralOperationsPullbackTransition` and
  `unrestrictedIntegralTransition` from its existing global interfaces.
* `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparison`,
  `inverseImageFiniteComparisonComplex`, `inverseImageIntegralModules` and
  `inverseImageFiniteModules`.
* `Sheaf.Paper.IsomorphismDerivedPullback`:
  `isomorphismIntegralTermwiseInverseImage`; the recorded
  `isomorphismIntegralDerivedPullback_termwise` describes the underlying
  comparison existence, but its `Nonempty` conclusion is NOT used to choose
  the normalized map.
* `Sheaf.Paper.ConstantCoefficientObjectsConstructible`:
  `integralConstantCoefficientObject`, `integralConstantCoefficient_constructible`
  and `constantCoefficientProjection`.
* `Sheaf.Paper.ConstantWeilStructure`: `constantWeilIntegralLambda`,
  `constantWeilDerivedCoefficientComparison`, `constantWeilIntegralTheta`,
  `constantWeilIntegralComplex`, `constantWeilIntegralGood`,
  `constantWeilPullbackTower`, `constantWeilPullbackRoosEndomorphism`.
* `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`, used by the existing good
  regular representative; its resolution interface is imported explicitly.
* Proof-source interfaces are also imported explicitly: site tensor
  functoriality, exact countable products, derived limits, integral-operations
  invariance, strict Roos comparison, finite-free completed scalar comparison,
  unrestricted reduction-tower invariance and cochain-model change of rings.
  The theorem docstring explains their roles in all nine source proof steps.

Sources read: Stacks `sites-modules.tex`, definition-pushforward (03D6), and
`derived.tex`, definition-derived-limit (08TC), together with current blueprint
`main-20261015/blueprint/sec-poincare-duality/sk-lem-finite/prop-cohomological-finiteness.proof.md`,
Step 7. The node's detailed nine-step normalization agrees with these sources.

Searches during this repair, in addition to the retained stage-1 search records:

* `msearch.py ... leanfinder` query: "The canonical completed derived pullback of
  a regular coefficient sheaf along a scheme isomorphism is inverse to the
  specified tensor-unit Roos augmentation and commutes with all finite quotient
  cone projections". Eight hits were scheme-module unit/pullback coherence and
  `SheafOfModules.pullbackObjFreeIso` / free-generator naturality; no match.
* `msearch.py ... loogle "SheafOfModules.pullbackObjFreeIso"`: five hits, the
  free-sheaf pullback isomorphism and its naturality/generator lemmas in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`.
  I read the unit transpose, its IsIso instance, and free-isomorphism signatures
  and docstrings there. They are underived and contain no specified Roos map.
* `msearch.py ... leansearch` query: "Completed derived coefficient pullback
  inverse image tensor multiplication commutes with strict Roos cone projections
  and finite quotient reduction". Eight hits: ordinary lTensor/rTensor right
  exactness, tensor quotient equivalence, tensor multiplication/commutation,
  Over tensor projection, ordinary limit-cone projection and CommSq cocone.
  None mentions the completed coefficient construction or the specified maps.
* `rg` searched `canonicalCoefficient|inverseImagePullbackComparison|
  constantWeilIntegralLambda` in the upstream WeilConjectures source and shared
  `lean/Sheaf`: the existing normalized lambda and specified kappa were found
  and reused; the desired combined projection theorem was not present.
  Searching the exact node id in upstream WeilConjectures found no occurrence.
  Mathlib grep for `pullbackObjUnitToUnit|pullbackObjFreeIso` found the same
  underived `PullbackFree.lean` declarations.

Edge cases checked by reading the actual constructions and signatures:
`g = 𝟙 X` still uses the recorded augmentation and inverse completeness, not a
substituted identity map; the empty scheme needs no chosen point or nonemptiness;
`n = 0` denotes exponent 1 rather than a zero coefficient ring; consecutive n and
n+1 have the correct quotient direction; arbitrary scheme isomorphisms need no
finite-type/properness/connectedness assumption; only the final conditional
Frobenius specialization uses a geometric finite-field fiber. All derived maps
are in the same R_X category and every finite arrow is explicitly restricted.

No `STATEMENT-DISPUTED` or node fault was found. The required scompile wrapper
compiled the final theorem (including D, l ≠ D.p and hX/hY) cleanly, with only
expected postponed-proof warnings; both sandbox and library checks succeeded.

## Second reading by NG

This is a fresh self-reading of the repaired node and module. The dispatcher
explicitly forbids starting other agents, so it is not represented as a separate
worker's independent review. The maintainer's independent review remains pending.

I compared each paragraph and displayed equation with the signature and unfolded
map definitions, rather than carrying forward the old report's conclusion.
The old second reading was wrong: its kappa was lambda's inverse, its finite ring
square did not state either requested derived projection identity, and it omitted
l-invertibility. Those mismatches are corrected above. In the repaired version:

* Kappa unfolds to the exact recorded dependency, with hX,hY and the regular good
  representative. Lambda unfolds to the published normalized comparison and an
  independently coefficient-defined transport. Neither defines the other.
* Rho unfolds to the real pullback-cone projection and canonical reduction;
  lambda_n unfolds to the uniquely determined inverse tensor-unit chain map.
  Both derived projection equations mention rho, lambda and pi with the required
  domains, codomains and composition order.
* The transition square is at the chain level, with adjacent indices and explicit
  Res functors. Cone projection compatibility is additionally stated after Q.
  There is no duplicate finite ring-square conjunct or ThetaProjection predicate.
* The global finite-field/coefficient context, invertibility on both schemes,
  small-site sizes and positive-exponent indexing all match. No arbitrary
  `Nonempty` choice, hollow data or weakened conclusion is used.
* The last equality names the existing constant-Weil normalization. Each helper
  carries the owning blueprint tag; both postponed theorems carry proof steps.

This reading found no further statement mismatch after the repair. Only the lean
record was changed in the node; its mathematical statement and dependency graph
remain as reviewed at stage 1.
