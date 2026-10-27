## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceInverseModulePerfectTests` states
`AlgebraicGeometry.AlgebraicSpace.inverseModule_perfectTensorTest`, with one whole-proof
`sorry` and no new definitions. It is precisely the perfectness assertion of Stacks
0CX6(1), not the separate base-change clause. Source read: `spaces-flat.tex`,
Situation `situation-existence` and `lemma-compute-against-perfect`, lines 2144–2234.
The statement and the accepted five-step proof plan are unchanged.

Hypothesis and clause correspondence:

- Schemes and algebraic spaces over Spec Z: `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`.
  `ULift` retains Spec Z in the chosen scheme universe. Explicit `u w` and
  `[HasDerivedCategory.{w} X.SmallModules]` implement the size convention, with no
  equation between the site/coefficients universe and the derived morphism universe.
- The inverse sequence is `A : ℕ → CommRingCat.{u}` with `r n : A (n+1) ⟶ A n`;
  Lean n is paper n+1, including every positive stage and every transition.
- Surjectivity is `hsurj`; locally nilpotent kernels are exactly `hnil`, quantifying
  over each kernel element, with no uniform nilpotence exponent.
- `c : Cone (Functor.ofOpSequence r)` and `hc : IsLimit c` specify the inverse-limit
  ring `c.pt` and its actual projections, allowing every limit cone.
- The structural map is `f : X ⟶ schemeSpace (inverseModuleSpec c.pt)`;
  separatedness is `hsep : MapIsSeparated f` and finite presentation is
  `hfp : ProperQuotFinitePresentation f` (local finite presentation, quasi-compactness,
  quasi-compact diagonal).
- `properQuotFibre f (inverseModuleTest c n)` is the actual sheaf fibre product X_n.
  `M n` is an existing small-etale module on it. `hqc` is quasi-coherence and `hfin`
  is finite presentation, using Mathlib's locally finite-free presentation predicate.
- `hflat` checks the module's scheme restriction on every etale chart using
  `Scheme.Modules.IsFlatOver`, the recorded affine-local equivalent of stalk flatness.
- `hsupp` spells out every support clause: a space Z and a representable closed
  immersion i, properness of its composite to Spec A_n, a quasi-coherent finite-type
  module G on Z, and an isomorphism from its canonical direct image to M_n.
- `e n` is the specified tensor-pullback isomorphism from M_(n+1) to M_n, using
  the canonical fibre map induced by `inverseModuleTestMap c n`.
- `inverseModuleDerivedTerm` is the degree-zero canonical direct image to X, transported
  to the fixed equivalent small ringed model; `hq` supplies its quasi-coherent
  cohomology certificate. The dependency `inverseModuleDerivedLimit` supplies such
  certificates and the intrinsic product. These binders unpack that construction;
  they impose no additional geometric condition.
- `K : X.DerivedQCoh`, the intrinsic `[HasProduct ...]`, arrows `p` and `δ`, and
  `hK : IsDerivedLimitTriangle ... K p δ` specify precisely the product triangle
  with 1 minus the transition shift. `inverseModuleDerivedTransition` uses the
  original tensor isomorphism and adjunction quotient, not a freely chosen map.
  Its n-th projection is `p ≫ Pi.π _ n`; no extra projection condition is imposed.
- `E : X.DerivedModules` is arbitrary, and `hE` uses the recorded
  `IsPerfectOnRingedSiteOfUniverses` predicate: etale locally bounded models of
  finite-free retracts, with local bounds and ranks.
- The conclusion `DerivedCategory.IsPerfectRingComplex ((perfectTensorTest ... E).obj K)`
  is a derived-category assertion over `c.pt`. Unfolding this existing functor gives
  derived tensor followed by `affineDerivedSections`, with the structure-induced
  scalar action. `IsPerfectRingComplex` says there is a bounded cochain complex with
  `Module.Projective` and `Module.Finite` in every degree and an isomorphism to it.
  Thus the conclusion is exactly RΓ(X,K tensor^L E) perfect in D(A).
- Derived tensor is the existing K-flat-normalized tensor in `X.derivedDualityModel`;
  derived global sections use the existing K-injective right derived functor.
  No boundedness, flatness of X, uniform Tor bound, or ambient-product assumption
  has been added.

Dependency declarations used (full module names):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `Modules` (inside namespace `AlgebraicGeometry.AlgebraicSpace`).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, underlying the existing `properQuotFibre`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the shared
  `SheafOfModules.IsQuasicoherent` predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  `moduleTensorPullback`, `moduleTensorAdjunction`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotFinitePresentation`,
  `properQuotFibre`, `properQuotSnd`, `properQuotFibreMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`,
  `MapIsProper`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor` (via the inverse term).
- `Sheaf.AlgebraicGeometry.SpaceInverseModuleDerivedLimit`: `inverseModuleSpec`,
  `inverseModuleTest`, `inverseModuleTestMap`, `inverseModuleDerivedTerm`,
  `inverseModuleQCohTerm`, `inverseModuleDerivedTransition`, `inverseModuleDerivedLimit`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `IsDerivedLimitTriangle`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, through the existing derived tensor.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `ringedSiteZerothHypercohomologyOfUniverses`, the recorded H⁰ RΓ convention;
  the conclusion correctly uses the whole derived sections object, not H⁰ alone.
- `Sheaf.AlgebraicGeometry.SpacePerfectTensorTestHolim`: `perfectTensorTest`.
  The new definition node `def-sfb-space-perfect-tensor-test` owns this existing
  functor. The holim theorem remains solely a proof dependency.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineDerivedSections`,
  used by that functor, with `Iso.refl _` identifying the chosen Spec with itself.

All recorded proof modules currently available were imported without `public`, except
those also used for the signature. The following proof nodes have no recorded Lean
module on the read base, so there is no import yet:
`lem-sfb-space-module-proper-carrier-support`,
`lem-sfb-scheme-derived-etale-qcoh-comparison`, `lem-sfb-etale-detects-perfect`,
`lem-sfb-space-qcqs-derived-projection-formula`, `lem-sfb-space-fp-qcqs-source`,
`lem-sfb-perfect-inverse-ring-reconstruction`. Their proof steps remain in the docstring.

Edge cases checked before writing: zero rings (empty spectra), the empty algebraic
space, all-zero modules, and the zero perfect test are admitted. Constant towers with
identity transitions are admitted. Locally nilpotent kernels need not be nilpotent
as ideals. No global bound or fixed degree interval is required for E. A nonproper
X with properly supported coefficients is admitted. Indices cover all n≥1, with the
first transition represented at Lean 0. Products are in D_QCoh, never ambient products.

Searches actually run through `msearch.py Q49 lem-sfb-space-inverse-module-perfect-tests`:

- leanfinder: `perfect tensor test derived global sections homotopy inverse limit flat
  finitely presented modules algebraic space perfect`: eight hits, concerning affine
  scheme limits, scheme flatness, and condensed modules; no exact statement.
- loogle: `DerivedCategory.IsPerfectRingComplex, IsDerivedLimitTriangle`: zero hits;
  unknown identifier `DerivedCategory.IsPerfectRingComplex` in the Mathlib index.
- grep: `inverseModule.*[Pp]erfect|perfectTensorTest|IsPerfectRingComplex`: zero Mathlib hits.
- leansearch: `derived global sections of perfect tensor homotopy inverse limit of flat
  finitely presented modules is a perfect ring complex`: eight hits on sections of
  affine schemes preserving limits and flat tensor functors, no exact statement.
- `rg -n 'inverseModule.*[Pp]erfect|perfectTensorTest|lem-sfb-space-inverse-module-perfect-tests'`
  in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: only the
  existing perfect tensor test and its products/holim theorem in Sheaf; no target match.
  The upstream tree has no occurrence of the item id or these target names.

Validation: scompile.py compiled both the sandbox probe and the delivery module against
published server artifacts in 2.1 seconds each, with no diagnostics. No local/global
build was run. No statement dispute, statement correction, or dependency-module repair.
The repair adds a definition node attaching the existing tensor-test functor.

## Second reading by Q49

Author's second reading (the dispatcher explicitly forbids starting another agent;
this is not an independent-agent review): reopened the node and complete module.
The ring conditions `hsurj` and elementwise `hnil` match 0CX4; `hc` retains the actual
inverse-limit cone. The scheme base, separatedness, finite presentation and all four
module conditions match their corresponding binders. The proper-support existential
retains G and its direct-image isomorphism, and `e` retains the actual reductions.
Checked the inverse term and transition definitions against their dependency source:
there is no arbitrary replacement tower. Checked `IsDerivedLimitTriangle`: its middle
arrow is exactly 1-shift and its products are in the type `X.DerivedQCoh`.
The certificates hq and HasProduct are supplied by the stated dependency, not an
extra restriction on the situations. Checked `perfectTensorTest` unfolds to the
normalized tensor and the actual A-valued derived sections functor; the conclusion
uses the whole derived object. Read `IsPerfectRingComplex`: bounded finite projective
terms and an isomorphism in D(A), precisely the node's final clause.
No mismatch found and no statement change needed. The repair replaces the theorem-node addition to stmt_deps with the actual
definition owner `def-sfb-space-perfect-tensor-test`. Explicit universes,
100-character lines, one named theorem with whole-proof sorry, and all source/proof
docstrings were checked. Independent maintainer review remains the delivery review.


## Repair of returned head 401e1dff652b

H2/H12: the previous delivery cited the theorem node
`lem-sfb-space-perfect-tensor-test-holim` in stmt_deps merely to use its helper
`perfectTensorTest`. Repaired by adding the definition node
`def-sfb-space-perfect-tensor-test`, with `lean.existing: true` naming that same
plain definition. Replaced that stmt_dep with the new definition id; the theorem
remains in proof_deps, where its products/holim conclusion is used in step 4.
Also added the optional existing definition owners
`def-sfb-space-derived-module-calculus` (DerivedQCoh) and `def-weil-derived-limit`
(IsDerivedLimitTriangle). The item's Lean signature and module are unchanged.
Compared the retained item with the current read-only main: only lean and stmt_deps
differ. The delivery wrapper rebases this concrete repair onto the current main.

## New nodes

`def-sfb-space-perfect-tensor-test` defines T_E(K) = RΓ_{X,A}(K tensor^L E), on
D_QCoh, with its functorial action a tensor id_E. It attaches the already existing
`AlgebraicGeometry.AlgebraicSpace.perfectTensorTest` in
`Sheaf.AlgebraicGeometry.SpacePerfectTensorTestHolim`, lines 37–44. The source is
Stacks 0CX6(1), expression and proof. Reading the complete declaration shows the
same objects S, A, Y with specified e, X and f, arbitrary derived universe w, and
arbitrary E. The predicate that E is perfect is imposed by the consumer, rather
than needed to define this composite. The function first includes D_QCoh, then
pairs with E, applies the normalized derived tensor, then applies the existing
A-valued derived sections functor. This exactly realizes the node, including its
map action and induced scalar action. No data is chosen or redeclared here.
The existing helper's source/docstring is retained in its owning published module;
its old theorem-node blueprint tag is not edited by this delivery.

Searched before creating the node: Mathlib via LeanSearch (ordinary global-sections
functors), LeanFinder (affine space and spectrum pullback constructions), and grep
(zero matches for perfectTensorTest, affineDerivedSections or DerivedQCoh).
Their exact outputs are recorded in the new node's mathlib_searches. Project and
DAG rg find the existing definition only in the holim module, recorded there as a
helper of the theorem; there is no separate definition node. Blueprint search for
“tensor test” returns zero nodes. A broader “derived tensor” search returns 135
nodes about other tensor constructions, not this scalar-valued test. The ancestor
command returns None for this inherited chain, so the new node retains a null
blueprint ancestor and prepends this item to the existing via path.
This new definition node was explicitly requested by the maintainer's immutable-head
review and avoids a duplicate declaration by existing:true.

Additional repair second reading: the new node's domain is exactly the full
D_QCoh subcategory and its codomain is the scalar ring's D(A). It introduces every
object and cites the definitions it uses. No properness, finite presentation,
compactness or perfectness condition was added to the functor itself. Zero rings,
empty X, and E=0 remain admitted. The main theorem retains every hypothesis and
clause already checked in the returned review. New-node proof and proof_deps are
empty. No dependency node or published Lean source was modified.

Repair validation: scompile.py again compiled the unchanged delivered theorem cleanly
(2.1 seconds per sandbox/library pass). deliver2.py --no-push compiled the existing
definition check and the delivered theorem, and returned OK (dry run) at
4830dfbda22. All H2/H12 field and new-definition checks passed.
