## Worker report

This delivery states `AlgebraicGeometry.Etale.vectorBundlePurity` in
`lean/Sheaf/Targets/VectorBundlePurity.lean`. Its proof is `sorry`. Its eight helper
declarations contain real constructions or the explicit proposition being asserted;
there is no postponed data, private coefficient category, arbitrary orientation,
or extra compactification hypothesis.

The statement of the node is unchanged. Its resolved stage-1 repair note was read:
that repair requests retaining the statement and expanding hidden proof arguments.
The theorem's docstring carries all nine current proof steps and their dependency
ids. The main-20261015 blueprint item and its containing unit were read as well.
The earlier upstream affine-space purity theorem was checked: it assumes a field
base, bounded constructibility and a normalized abstract twist, and asserts only
existence of an isomorphism. It is not this node's ordinary unbounded, normalized
vector-bundle statement.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Prime ell | `(ell : ℕ) [Fact ell.Prime]` |
| Finite extension F/Q_ell | `(F : Type u) [Field F] [Algebra (Padic ell) F] [FiniteDimensional (Padic ell) F]` |
| Positive quotient level | The binder `n : ℕ` indexes the level `n+1`, including level one. |
| A = O_F/(uniformizer^(n+1)) | The existing `Scheme.finiteTateCoefficient ell F n`, the canonical `ULift` of `Padic.coefficientExtensionRing ell F (n+1)`. |
| Finite coefficients | `vectorBundlePurityFiniteCoefficient` applies the recorded `Padic.finite_coefficientExtensionRing`; the lift inherits its instance. |
| Noetherian base | `(S : Scheme.{u}) [IsNoetherian S]`. |
| ell invertible on S | `(hS : IsUnit (ell : Γ(S, ⊤)))`. `vectorBundlePurityInvertiblePower` supplies the consequent invertibility of ell^(n+1). |
| Bundle of constant nonnegative rank | `(d : ℕ) (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d]`. Its scheme and projection are exactly `VectorBundleZeroSection.scheme` and `.π`. |
| Every S-scheme T | `∀ (T : Scheme.{u}) (f : T ⟶ S)`. No Noetherian, finite-type or nonempty hypothesis is imposed on T. |
| Any positive annihilating ell-power | `r : ℕ` indexes ell^(r+1), with the precise equality `hA : ((ell^(r+1) : ℕ) : Scheme.finiteTateCoefficient ell F n) = 0`. |
| Explicit etale descent by roots tensor A | `Scheme.finiteEtaleTateTwist T (ell^(r+1)) _ hA k`, at k=1, is the recorded root sheaf extended from Z/ell^(r+1) to A. |
| Comparison with the original pro-etale twist | The family `b` has source `ProEtale.comparisonUpperStar.obj` of that sheaf and target the existing `Scheme.finiteTateProSheaf ell F n T k`. This latter is the recorded `finiteCoefficientTwist` restricted to constant scalars, not a replacement twist. |
| Canonical comparison | `Scheme.IsFiniteTateSiteComparison ... (b ...)` fixes all root-limit pure tensors, including arbitrary pro-etale tests over an etale object. |
| Tensor powers | `k : ℕ` ranges over all nonnegative powers, including zero. Both sides are the published powers; root-tensor normalization fixes the tensor-power comparison. |
| Independence of the annihilator | `∃! t` with `Scheme.IsFiniteTateEtaleTransition` and `ν.mapIso t ≪≫ b_r = b_r'`. For two unordered exponents use their common maximum. |
| Canonical descent itself | For every etale G with comparison a to the specified pro sheaf, `∃! h` with `ν.mapIso h ≪≫ a = b`. Thus an arbitrary descent or comparison cannot be substituted. |
| A usable annihilator exists | `∃ hA : ((ell^(n+1) : ℕ) : A) = 0` is part of the conclusion. There is no assumption that the quotient is free over Z/ell^(n+1), or any condition on its ramification index. |
| A_E(d)[2d] | The existing `vectorIntegrationCoefficient A N hA S d M`, namely pullback of `affineLinearBaseCoefficient`: d ordered tensors of the actual finite Tate line shifted by two, with constant unit at d=0. |
| pi^* K(d)[2d] | `vectorBundlePurityTwistedPullback` is `ordinaryFinitePullback.obj K` derived-tensored on the right with that exact coefficient. Associativity and the standard tensor/shift comparison give precisely the displayed notation, without a new twist. |
| Unique integration from prescribed affine traces | The first conjunct of `VectorBundlePurityAtModulus` is `VectorIntegrationNormalization ... (vectorBundleIntegration ...)`. It uses the existing definition, hence its actual inverse-frame exchanges and normalized affine-space counits on every frame, rather than an arbitrary trace map. |
| Bounded coefficient | `DerivedCategory.TStructure.t.bounded (vectorIntegrationCoefficient ...)`, followed by an actual D+ representative C and isomorphism to that coefficient. |
| Bounded pro-etale realization of the object and map | For every C and representative isomorphism a, `∃! t` on the actual pro-etale compact support of `ν` of the coefficient. Its equation says that pro compact-support of `ν(a)` followed by t is the canonical `compactSupportSiteComparison.app C` followed by `ν(Rpi_!(a) ≫ vectorBundleIntegration)`. All factors are specified. This both defines the pro realization uniquely and identifies its actual map under the proper/open comparison. No site comparison of arbitrary unbounded K is asserted. |
| Ordinary compact-support functor | `vectorBundlePurityLower` is `rightDerivedLowerShriekOfCompactification (ModuleCat A)` with the very same canonical chosen compactification as `vectorIntegrationSource`. |
| Ordinary ambient adjunction | `vectorBundlePurityAdjunction` reuses `rightDerivedUpperShriekAdjunction`; the left functor is definitionally the preceding one. Its right functor is the specified ordinary `rightDerivedUpperShriek`, not a constructible exceptional functor. |
| Canonical PF | `vectorBundlePurityProjectionMap` is the symmetry K⊗B → B⊗K, then the recorded `projectionMapOfCompactification` (proper PF and inverse open tensor comparison), then compact-support image of the symmetry on E. These are the signed derived symmetries. |
| PF inverse | `p : Rpi_!(pi^*K(d)[2d]) ≅ K⊗Rpi_!A_E(d)[2d]` satisfies `p.inv = vectorBundlePurityProjectionMap ... K`. An inverse determines p uniquely, so p is not an unrelated isomorphism or a hypothesis. |
| 1 tensor t_pi and the final identification | `((derivedTensor ... S).obj K).map (vectorBundleIntegration ...)`, followed by the existing `derivedTensorRightUnitor ... K`. |
| gamma is an isomorphism | `IsIso ((vectorBundlePurityAdjunction ...).homEquiv _ K (p.hom ≫ (1⊗t_pi) ≫ unitor))`. It is the actual adjunct of the specified counit. |
| No restriction on K | `∀ K : DerivedCategoryModule A S`, without boundedness, constructibility, Tor, perfectness, or etale-origin hypotheses. |

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and the public original coefficient ring.
- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`:
  `VectorBundleZeroSection.scheme`, `.π`, and its locally free module convention.
- `Sheaf.Paper.IntrinsicCoefficientTwists`: its public original finite constructions
  from `Sheaf.Paper.CoefficientTwistsDetailed`, specifically `finiteCoefficientTwist`.
  The intrinsic rational repair is preserved by importing the recorded module;
  this theorem uses only its finite part.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, with `ProEtale.comparisonUpperStar` on fixed modules.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback` and the public concrete `finiteEtaleTateTwist`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded fixed-coefficient
  convention from its lean.note, namely `Etale.DerivedCategoryModule` and the ordinary
  `DerivedCategory.Plus`, `Bounded`, and standard t-structure.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
- `Sheaf.AlgebraicGeometry.VectorBundleIntegration`:
  `vectorIntegration_geometry`, `vectorIntegrationCoefficient`, `vectorIntegrationSource`,
  `VectorIntegrationNormalization`, and `vectorBundleIntegration`.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`:
  `exists_affineSpaceTopTrace`, its actual normalized `affineTraceCounit` and ordered tower.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification` and its canonical chosen-compactification form.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification` and the published ambient
  `rightDerivedUpperShriekAdjunction` to which it applies.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`; the live source was read through
  `scompile.py --source` because this migrated module is absent from the older source tree.
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`:
  `Etale.isIso_proper_projection_formula_reordered`, with both signed symmetries.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection`:
  `projectionMapOfCompactification`, with its proper/open construction read in source.
- `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure` and the recorded
  `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`:
  `derivedTensorSymmetry` and `derivedTensorRightUnitor`.
- `Sheaf.Paper.FiniteTateSiteDescent`: `Scheme.finiteTateCoefficient`,
  `finiteTateProSheaf`, `IsFiniteTateSiteComparison`, `IsFiniteTateEtaleTransition`,
  and `finite_tate_site_descent`. The node is now a statement dependency because its
  recorded constructions occur in this statement.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `ProEtale.compactSupportSiteComparison`. This already landed node is added as a
  statement dependency because the named comparison occurs in the conclusion.
- `lem-kun-tensor-sym` is added as a statement dependency for the existing signed symmetry.

All recorded non-Mathlib proof-dependency modules are imported without `public` unless
also statement dependencies. The Mathlib proof leaves use `Adjunction.comp`,
`DerivedCategory.instFullSingleFunctor` / `instFaithfulSingleFunctor`, the Noetherian-open
instances, `locallyOfFiniteType_of_isOpenImmersion`, and `DerivedCategory.isIso_iff`;
their modules are imported. No proof prerequisite is restated.

Edge-case reading:

- Internal n=0 is exactly the required positive level one; level zero of the quotient
  is not silently introduced. Likewise internal r=0 means the first positive ell-power.
- d=0 is allowed. The published coefficient is the constant unit and the local affine
  trace is the identity counit; no coordinate, determinant, or positive-rank choice occurs.
- The empty base and empty S-schemes are allowed. No point, section, affine trivialization,
  or nonempty cover is chosen by this statement.
- T can be arbitrary over S. Its invertibility of ell follows by the recorded pullback
  invertibility construction when applying the finite descent theorem.
- K=0 and complexes unbounded in either or both directions are included. The only
  boundedness assertion concerns the coefficient of the trace, not K or pi^times K.
- The choice of uniformizer is the recorded coefficient construction. No extra algebra
  action, arbitrary inverse image, or second module-category encoding is supplied.
- The standard common universe u contains both F and the scheme data; the coefficient
  lift is exactly the recorded u+1 fixed-module convention of the small sites.
- The pro-etale trace witness is uniquely determined by an equation whose left factor
  is an isomorphism, and the projection inverse is determined by its inverse. Neither
  witness replaces a canonical map by unconstrained existence.

Searches for existing notions/statements (msearch.py, group NX and this item):

1. LeanFinder: `Vector bundle integration counit gives purity on ordinary unbounded
   etale derived categories`. Eight generic condensed/adjunction hits; no exact match.
2. Loogle: `CategoryTheory.Adjunction, "homEquiv"`. Twelve generic adjunction-Hom hits;
   the ordinary homEquiv API is reused, but no bundle-purity statement exists there.
3. Mathlib grep: `vectorBundlePurity|vectorBundleIntegration|purity` in
   `AlgebraicGeometry`. Zero matching Mathlib declarations.
4. LeanSearch: `Purity for vector bundles on unbounded derived categories of etale
   finite coefficient sheaves, adjoint of integration counit`. Eight generic counit,
   derived-adjunction and sheafification hits; none states this result.
5. `rg` of `WeilConjectures` and `lean/Sheaf` for bundle-purity, integration and purity
   names, and the literal item id. Found the named integration and the upstream
   affine-line/affine-space bounded-constructible existence statements. The latter
   were opened and fail to match this theorem's hypotheses, scope and specified map.
6. `rg` of `dag/lean_names_upstream.json`, Mathlib, the source repository and `lean/Sheaf`
   for the introduced helper names: no existing definitions with those names.

No STATEMENT-DISPUTED issue, source correction, new independent notion, or dependency
interface repair is needed. The helpers are constructions belonging to this node's own
specified compactification, coefficient, projection and comparison statement.

Validation: the delivered report recorded only the generic projection/adjunction probe,
not a completed full-module result. The independent maintainer check below supplies the
full-file evidence and supersedes that unfinished validation sentence.

## Second reading by NX

Independent maintainer second reading, 2026-10-18, of immutable delivery
7e975a2a9fd8974bdbe24f8f74c9100125a8545c. This section is supplied by the external
second reader; it does not claim a second NX worker performed the review.

I read the item node and all sixteen statement-dependency nodes in the snapshot, the
single delivered module, its nine-step statement docstring and all eight helpers, and
the actual dependency declarations. I read the main-20261015 source item at order 1973,
the source definition of integration at order 1972, the affine trace at order 1970,
the coefficient/root-line sources, and the Stacks source passages identified below.

Independent clause checks:

- Prime and coefficient field: `ell`, `Fact ell.Prime`, `Field F`, `Algebra (Padic ell) F`
  and `FiniteDimensional` state exactly a finite extension of Q_ell. The existing
  `finiteTateCoefficient ell F n` is `ULift (coefficientExtensionRing ell F (n+1))`.
  Thus internal n=0 is positive level one, and every positive source level occurs.
  This is a reindexing, not an extra case or omitted level. Finiteness is supplied by
  the existing positive-level coefficient theorem. The annihilator is a conclusion.
- Base and bundle: `IsNoetherian S`, `IsUnit (ell : Gamma(S,top))`, natural d, and
  `M.IsFiniteLocallyFreeOfRank d` are exactly the stated hypotheses. The total space
  and projection are the recorded relative Spec Sym(M), not a chosen unrelated scheme.
  The chosen Nagata compactification is the same one used by `vectorIntegrationSource`.
  Affineness, finite type and qcqs of the base discharge its existence; no extra
  compactification or separated-base hypothesis enters the theorem.
- Descent: every `T : Scheme` with `f : T --> S` is quantified, with no Noetherian or
  finite-type hypothesis on T. Invertibility pulls back from S. The family b uses the
  actual finite roots sheaf extended from Z/ell^(r+1), and the target is the original
  finite pro-etale twist through constant-scalar restriction. The root-limit pure-tensor
  predicate fixes the comparison. The normalized exponent-transition equation and
  unique comparison-preserving descent give the canonical independence required.
  The natural k includes tensor power zero as well as the required positive powers.
- Trace and coefficient: `vectorIntegrationCoefficient` is inverse image of the
  ordered tensor of d Tate lines shifted by two, hence A_E(d)[2d]. Its boundedness
  and a D+ representative are conclusions, not assumptions on K. The normalization
  conjunct uses `vectorBundleIntegration`, whose defining uniqueness theorem fixes
  every local affine-space counit. It does not introduce an arbitrary orientation.
- Site realization: for every D+ representative C and identification a, the unique
  trace t is constrained by the displayed equation with `compactSupportSiteComparison`.
  The left factor is the pro compact-support image of the isomorphism nu(a), so the
  equation determines t uniquely. This realizes the same integration map through
  the canonical proper mate and open comparison; it asserts no unbounded comparison
  for arbitrary K. The ordinary purity conclusion is not replaced by pro-etale purity.
- Projection and adjunct: the first symmetry puts K second, the existing compactified
  projection map applies proper projection and inverse open-extension tensor comparison,
  and the final symmetry restores K first on E. The witness p has inverse equal to
  this exact map. Thus its hom is the specified inverse, uniquely determined. The
  composite then tensors the actual trace with K and applies the canonical right
  unitor. `homEquiv` has source Hom(Rpi_! X,K) and target Hom(X,pi^times K), so the
  `IsIso` assertion has the required direction and refers to the actual named mate.
  K ranges over the whole ordinary derived category without any finiteness condition.

Dependency interface checks:

- `CoefficientExtensionFinite` preserves the quotient coefficient ring and supplies
  finiteness at positive levels; `VectorBundleZeroSection.scheme` and `.pi` use the
  existing symmetric-algebra relative-spectrum construction.
- `IntrinsicCoefficientTwists` publicly retains `CoefficientTwistsDetailed`; the finite
  part is `finiteCoefficientTwist`, not its rational/common-stage interface. I followed
  `finiteTateConstantRestriction` and `finiteTateProSheaf` to this original finite line.
- `ProEtaleSiteComparison` and `ProEtale.comparisonUpperStar` use the same inclusion,
  left Kan extension and sheafification. `EtaleFiniteTwistPullback` uses the root-power
  normalization and the constant coefficient action, including signed tensor powers.
- `DerivedCategoryModule` is the ordinary localization of fixed-A module sheaves;
  `derivedTensor` is its existing K-flat derived tensor. No second category or tensor
  construction is defined by this file.
- `VectorBundleIntegration` defines its trace by the uniquely normalized truncation
  identification and glued sheaf map. `AffineSpaceTopTrace.affineTraceCounit` is the
  actual ordered composite counit, with identity adjunction at rank zero.
- `rightDerivedLowerShriekOfCompactification` is D(j_!) followed by R(r_*).
  `rightDerivedUpperShriekAdjunction` is the specified adjunction to that left functor.
  The exceptional-adjoint node and upstream ordinary adjoint supply its existence by
  the ordinary coproduct/Brown route at finite coefficients.
- `etaleInverseImageModulesExact` gives the constant-ring identification, action,
  exactness and adjunction. `ProperProjectionFormula` and `derivedTensorSymmetry`
  expose the canonical signed projection and braiding, not a bare Nonempty isomorphism.
- `CanonicalCompactSupportSiteComparison` uses the specified proper direct-image mate
  and `properOpenSiteExtensionIso`. I also read the exact server finite-coefficient
  comparison source because that migrated module is absent under that path locally.

Proof-route checks: the main docstring retains all nine immutable proof steps: finite
Tate descent; bundle compactification; local normalized trace and bounded realization;
proper/open tensor projection; normalized projective-line then affine-line adjunction;
ordered affine-space induction; base-open restriction through extension/composition Hom
bijections; compatibility of the two mates; and detection on cohomology stalks. The
locality argument uses sheaf maps for degree-zero gluing and tests only isomorphy of
general derived maps. It does not assert equality detection for arbitrary derived maps.
All listed non-Mathlib proof dependencies have imports; Mathlib leaves use their recorded
ordinary APIs. No direct statement or proof citation is on the route-pivot dropped list.
The current repair note is a resolved stage-1 re-splitting note, not a route-pivot note.
No infinity, dg, Quillen, model-category or enhanced descent construction is introduced.

Edge cases: rank zero, empty base, empty test scheme, tensor exponent zero, positive
coefficient level one, ramified extensions and annihilating exponents larger than needed,
K=0 and complexes unbounded in both directions are retained. The standard common ambient
universe u for schemes and F and the existing u+1 coefficient/module lift are explicit;
no new site-universe equality or small-test-universe restriction is imposed.

Independent searches: rg over Mathlib, upstream WeilConjectures and side Sheaf for
vector-bundle/affine-space purity and integration, and msearch grep for exceptional
adjoint/inverse-image/integration/vector-bundle vocabulary. The upstream
`nonempty_iso_rightDerivedUpperShriek_affineSpace` was opened: it assumes a field base,
bounded constructible finite-Tor K and a normalized abstract twist, and states only
existence. It is not this general bundle theorem or its normalized mate. The new helpers
are specializations/composites of the existing constructions, not second definitions of
coefficients, tensor, compact support or integration.

Pilot checks: only the two named theorem bodies contain sorry. All definitions contain
real terms. No local mathematical proof beyond sorry was added. Source and blueprint
docstrings are present, the main proof plan is complete, every variable/universe is bound,
all Lean lines are at most 100 characters, and lean.statement is verbatim the signature
before `:= by`. No new nodes or dependency modules are delivered; no statement correction
or citer audit is required.

Findings and repair: H11, the delivered second-reading section was only a disclaimer and
contained no reading. Replace it by this independent clause-by-clause audit. The unfinished
full-module validation sentence is replaced by the compiler evidence below. No theorem,
definition, node statement, dependency edge, or Lean record is changed by this fix.

Compiler evidence: on 2026-10-18 I ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NX thm-amb-vector-bundle-purity snapshot/lean/Sheaf/Targets/VectorBundlePurity.lean`
from the immutable review directory. The wrapper returned exit code 0, with no Lean
errors or warnings in either view. Its complete result was:

```text
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-sghssm53/.lbuild) [27.7 s]
library Sheaf/Targets/VectorBundlePurity.lean

[145.6 s]
```

The current prescribed wrapper is the 2026-10-17 server/persistent-side-overlay version;
these are its reported timings, including wrapper/server work, not a request to increase
its 60-second Lean invocation limit. No lake/global build or live Lean write was performed.
The checked immutable module SHA-256 is `ee383376b975c46f9faf23b5d64a149e4f828ad82730f76ca7e0a033766f27c5`.
The replacement report is the only fix. The immutable snapshot and all repository heads
were left untouched.
