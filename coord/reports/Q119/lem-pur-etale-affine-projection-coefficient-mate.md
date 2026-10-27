## Worker report

The module `Sheaf.Paper.EtaleAffineProjectionCoefficientMate` states
`AlgebraicGeometry.Etale.etaleAffineProjectionCoefficientMate`, with one postponed
proof. Three real helper definitions package its normalized purity identification,
ordinary assertion, and specified site-transport equation. They introduce no new
geometric, tensor, coefficient or site construction. No dependency is redefined,
no source statement is corrected, and no new node is needed.

Hypothesis and clause correspondence:

- `ell pchar : ℕ`, `[Fact ell.Prime]`, `hp : 0 < pchar`,
  `hell : ell ≠ pchar`, `[Field k]`, `[CharP k pchar]` express the characteristic
  and prime assumptions without imposing a chosen finite field or perfection.
- `V.Over (Spec (.of k))` and the `LocallyOfFiniteType`, `QuasiCompact`, and
  `IsSeparated` instances on its structure morphism express separated finite type.
  Noetherianity and invertibility of the common annihilating modulus are concluded
  as `hV` and `hN`, rather than required as additional hypotheses.
- `d : ℕ` includes every rank, including zero. `affineTraceTower V d` and
  `affineTraceProjection V d` are the existing ordered-coordinate model of the
  affine projection. `affineTraceAffineSpaceIso V d` identifies this model with
  `AffineSpace (ULift (Fin d)) V` by its explicit coordinates and structure map.
  The model is the one used by the source's specified iterated affine integration.
- `E F`, their field, Padic algebra and finite-dimensional instances are precisely
  the two finite extensions of Q_ell. The small coefficient rings are the recorded
  `Padic.coefficientExtensionRing ell E (m+1)` and the corresponding F ring.
  Indexing positive levels by predecessors covers exactly all m,n at least one.
  Their sheaf presentations are `ULift.{u+1,u}` of these same rings. `φ` is an
  arbitrary unital map of the small rings, and `RingHom.ulift φ` is its exact
  presentation in ordinary etale module categories. There is no map of coefficient
  fields, flatness, ramification or projective-dimension condition.
- `hA`, `hB` conclude annihilation by the common power
  `ell ^ max (m+1) (n+1)`. Finiteness comes from the dependency's
  `Padic.finite_coefficientExtensionRing`, via the existing lifted instance
  `vectorBundlePurityFiniteCoefficient`.
- `DerivedCategoryModule A V` is the dependency's ordinary, unbounded small-etale
  derived category. `scalarExtension` is the actual derived extension of scalars.
  Compact support uses `rightDerivedLowerShriekOfCompactification`, with exactly
  `HasCompactification.compactification (affineTraceProjection V d)`.
- `AffineProjectionCoefficientAssertion` quantifies over `L` with
  `DerivedCategory.isBoundedConstructible A V L` and an interval
  `∃ a b, DerivedCategory.hasTorAmplitudeIn A V a b L`. Thus every bounded
  constructible finite-Tor input is included, not just a degree-zero or flat input.
- Its first conjunct says the actual `ExceptionalCoefficients.compactSupportMap`
  at the ambient right-adjoint value is invertible. Its second is `IsIso` of the
  actual `ExceptionalCoefficients.mateMap`. The latter definition is precisely the
  B-adjunction transpose of `comparisonInverse` followed by scalar extension of
  the A-counit. The first conjunct makes the existing total inverse equal to the
  true inverse, so the zero fallback in that shared definition is irrelevant.
- `affineProjectionPurityIso` is constructed by `rightAdjointUniq` from the
  integration-normalized `affineTraceAdjunction`, transported along
  `reductionEtaleAffineLeftIso` for that same compactification, to the actual
  ambient `rightDerivedUpperShriekAdjunction`. Therefore its counit is preserved;
  it is not an unspecified objectwise isomorphism. The ordinary assertion's last
  equation says `T(gamma_A) ≫ b = a ≫ gamma_B`, where `a` is exactly the published
  `reductionEtaleAffineScalarIso`. Conjugating is precisely the requested canonical
  coefficient/pullback/Tate/shift reassociation. The normalized P1 data are
  universally quantified: their structure fields fix the actual Kummer maps,
  decomposition and counit. Existence is the existing
  `exists_ordinaryFiniteP1Adjunction`, so these are presentations of the specified
  data, not extra mathematical hypotheses or free orientations.
- `AffineProjectionCoefficientSiteAssertion` is instantiated at the SAME chosen
  compactification. The arbitrary constructible adjunctions `adjA`, `adjB` and
  their `ReductionExceptionalRealization`s retain their actual ordinary origins,
  site/scalar comparisons and counits. The origin isomorphism `o` must obey the
  published actual site/scalar equation. A transformation `c` with invertible
  `reductionDirectImageComparison` is constrained by exactly the defining counit
  equation of `det-sp-reduction-exceptional`. The conclusion identifies its actual
  underlying component, through `RB.rightIso`, with the scalar image of
  `RA.rightIso`, followed by `reductionSiteScalarIso`, followed by the site image of
  the ordinary B-adjunction transpose. Thus it identifies the specified smooth
  mate, and covers every input and every canonically isomorphic ordinary origin.
  It does not invoke the invertibility conclusion of reduction-exceptional.

Dependency declarations read and used:

- Scheme convention node: Mathlib `Scheme`, structure morphisms,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its public coefficient constructions
  supply the actual quotient ring and chosen uniformizer.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule` and the ordinary derived category convention.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` and its public upstream
  `Coefficients` import: `Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.Targets.VectorBundlePurity`: the integration-normalized purity statement
  and `vectorBundlePurityFiniteCoefficient`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, its structure map,
  and the empty-coordinate convention; used through the canonical ordered model.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`,
  through the existing coefficient and affine-twist functors.
- `Sheaf.SecSmoothPurity.ReductionExceptional`:
  `reductionEtaleAffineScalarIso`, `reductionEtaleAffineLeftIso`,
  `ReductionExceptionalRealization`, `reductionSiteScalarIso`,
  `reductionCtfCompactSupport`, `reductionCtfScalar`, and the defining transpose
  interface recorded by `det-sp-reduction-exceptional`.
- Its public `Sheaf.Paper.ExceptionalCoefficientMaps`:
  `ExceptionalCoefficients.compactSupportMap`, `comparisonInverse`, `mateMap`.
- `Sheaf.Paper.EtaleCompactScalarCoherence`: `etaleCompactScalarCoherence`.
- Proof-only imports: `Sheaf.CategoryTheory.NormalizedMateScalarSiteTransport`,
  `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`,
  `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`, and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
  Their recorded declarations and signatures were read. The remaining proof
  dependency `lem-pur-etale-affine-integration-coefficient-equation` had no Lean
  record at the time of writing; it is a proof ingredient, not a missing notion
  or statement interface, so there is no module to import yet. Its argument is
  retained explicitly in the theorem's proof docstring.

Edge cases checked mathematically: rank zero (identity tower and identity scalar
reassociation); empty V; zero L; level one on either side; identity coefficient
map; non-flat maps such as Z/ell² to F_ell; ramified extensions and unrelated
unital stage maps. The annihilator max includes both levels. No positive rank,
nonempty scheme, flat scalar change or smoothness of V is required. Site object
universe u+1 and morphism universe u are retained; coefficients alone are lifted.

Searches before writing (all prescribed semantic searches used msearch.py):

- LeanFinder: "Affine space exceptional pullback coefficient mate normalized by
  integration is canonical Tate twist reassociation". Eight hits, headed by
  `AffineSpace.isPullback_map`, `Proj.pullbackAwayιIso_hom_awayι`, and
  `AffineSpace.homOfVector`; no matching sheaf-theoretic theorem.
- Loogle: "CategoryTheory.mateEquiv, CategoryTheory.Adjunction". Twelve generic
  mate-calculus hits including `mateEquiv_counit`, `mateEquiv_vcomp` and
  `iterated_mateEquiv_conjugateEquiv`; no geometric specialization.
- Mathlib grep through msearch.py:
  `affine.*(upperShriek|exceptional)|coefficient.*mate`, CategoryTheory: zero hits.
- Local rg on both `lean/WeilConjectures` and `lean/Sheaf` for affine coefficient
  and scalar constructions found `reductionEtaleAffineScalarIso` and the existing
  projection/coefficient interfaces, which are reused. The exact item-id search
  found no existing theorem. The upstream coefficient comparison theorem handles
  Z/ell^r quotient maps, not arbitrary unital maps between finite-extension stages,
  and its statement does not supply this normalized affine/site identification.

Validation: the delivered module compiled cleanly through scompile.py both as a
sandbox module and under its final module name. All theorem proofs are `sorry`;
the helper definitions have real data. No disputed statement or dependency repair.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
