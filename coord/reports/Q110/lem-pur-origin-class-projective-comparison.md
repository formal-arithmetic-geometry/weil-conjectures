## Worker report

Q110 states `lem-pur-origin-class-projective-comparison` in
`Sheaf.AlgebraicGeometry.OriginClassProjectiveComparison`. The only postponed proof
is `origin_class_projective_comparison`; all definitions contain actual data.
`OriginProjectiveComparison` is a record containing the full conclusion over a fixed
base. Its Nonempty assertion is precisely existence of those same normalized witnesses.
The five actual-arrow equations are written out in the generic `originComparisonEquations`. Its theorem specializes the
base to `Spec (.of Ω)`.

Hypothesis and clause correspondence:

- `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` is the algebraically closed field.
- `N : ℕ`, `hN : 0 < N`, `hΩ : IsUnit (N : Ω)` are exactly positivity and invertibility.
- `A : Type (u + 1)`, `[CommRing A] [Finite A]`, `hA : (N : A) = 0` encode finite
  commutative coefficients annihilated by N, including the zero ring.
- S is literally Spec Ω. X is `AffineSpace PUnit S` and P is `ProjectiveLine S`.
  The existing `infinityChart S` is [1:t], D(x₀), despite its name; `affineChart`
  would give the wrong coordinate order. `zeroSection PUnit S` is i₀, and its
  composite with j is definitionally `ProjectiveLine.infinity S`, namely [1:0].
- The ordinary small-etale module category and its unbounded derived category
  are the existing `DerivedCategoryModule A T`. `ordinaryFiniteLine` places the
  actual finite-etale roots-of-unity tensor A in degree zero; [2] is explicit.
- hX, hP, hIX, hIP are existential conclusions establishing invertibility of N
  on these fixed schemes and the Cartier property of the actual origin ideals;
  they add no assumptions. The existing normalized transport t specifies the
  root and pure-tensor comparisons, so is not an arbitrary twist isomorphism.
- κX and κP satisfy the existing `SupportedKummerBoundary` for the two actual
  origin immersions. `originBoundaryArrow` is exactly their `Ext.hom` realization
  on the exact closed direct-image sheaf. Under the canonical single-object
  comparison this is the recorded supported derived Kummer morphism.
- r is required to have exactly the canonical `supportedConstantExchange` hom,
  using the identity on S. The supported counit uses this very sheaf isomorphism before exact termwise
  localization, not a choice of an unrelated derived restriction isomorphism.
- `originSheafSupportCounit` is the original sheaf counit after j_!(r⁻¹).
  `originSupportCounit` is its exact termwise localization, composed with the
  canonical single-object comparison. This is the actual localized counit. `IsIso` asserts precisely invertibility
  of e. `originTwistCounit` uses the actual sheaf counit after the normalized twist
  comparison, then its exact single and shift comparisons. It is precisely the
  termwise-localized counit at L_P[2].
- The first equality is `j_!.map cX ≫ epsilon = e ≫ cP`, exactly the node's
  counit square, using Lean's left-to-right composition convention.
- The divisor line is `Scheme.Modules.dual (ProjectiveLine.infinity S).ker.toModules`.
  Its isomorphism with the existing twist O(1) is asserted. The recorded
  `ProjectiveLine.TwistData S 1` supplies the actual standard-chart frames and
  transition g₀=t⁻¹g₁; it does not leave the sign or transition unspecified.
- c₁ satisfies `ordinaryFiniteP1ChernSpec`, the actual positive Kummer class of
  the recorded O(1). The following closed-unit equation identifies forgetting
  support of κP with this very Chern arrow.
- `originConstantSectionsUnit` is the derived original constant-sheaf/global-
  sections adjunction unit, transported by its exact single-object comparison.
  It sends one to one, and fixes the generator independently of the last equation.
- `originCompactSections` is the specified projective-compactification model
  `Dj_! ⋙ RΓ(P,-)` of ordinary compact support, under proper Leray. It is never
  replaced by supported cohomology.
- lambda is an isomorphism A[0] to these compact sections of i₀*A. Its equation
  `lambda ≫ RΓ(e) = eta ≫ RΓ(u)` fixes the canonical section-one normalization.
- The final actual-arrow equality expands tau as `lambda ≫ RΓc(cX)`, a as the
  global-sections image of `originTwistCounit`, and h as `eta ≫ RΓ(c₁)`. It is
  precisely a tau = h, coefficient +1. No supported/compact identification is assumed.

Dependency declarations read and used (including their full signatures/docstrings):

- Mathlib Scheme, Hom and AffineSpace; upstream ProjectiveSpace and ProjectiveLine.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line`: infinityChart, infinity;
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`: zeroSection.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: DerivedCategoryModule.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: etaleFiniteTwistPullback;
  `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`: OrdinaryFiniteTwistTransport.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  rightDerivedLowerShriekOfCompactification and rightDerivedGlobalSections.
- Upstream Etale.LowerShriek.OpenImmersion.Defs: openImmersionLowerShriek and
  openImmersionLowerShriekUpperStarAdjunction; Etale.UpperLowerStar.Defs: upperStar, lowerStar.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`: ordinary_supported_kummer
  and ordinary_supported_kummer_uniqueBoundary; OrdinarySupportedKummerBoundary:
  SupportedKummerBoundary, supportedConstantExchange, supportedConstantUnit.
- Upstream EffectiveCartier: the ideal module, its dual and invertibility;
  ProjectiveSpace.Twist: twist; TransitionUnits: transitionUnit and TwistData.
- `Sheaf.SixFunctors.OpenTensorNormalizationData`: exactDerivedAdjunction.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: ordinaryFiniteP1ChernSpec,
  ordinaryFiniteLine, ordinaryFiniteUnit, ordinaryFiniteConstant.
- Mathlib Ext.hom, mapDerivedCategorySingleFunctor, constantSheafΓAdj and its
  mapDerivedCategoryRightDerivedAdjunction.

The statement dependency list adds the already landed `def-sc-p1-standard` and the
new definition `def-pur-origin-comparison-arrows`. All original dependencies and
proof-plan imports remain. No dependency repair or statement correction is required.

Edge cases: N=1 forces A to be the zero ring, and all the arrows remain meaningful.
The zero ring is allowed for any N. Arbitrary finite commutative A is allowed,
without field or flatness assumptions. Positive characteristic is allowed when N
is invertible. Ω is a field, so S is nonempty. All universes and variables are bound;
the u+1 coefficient universe follows the recorded ordinary small-site convention.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: "The supported Kummer class of the affine origin maps under extension
  by zero to the positive first Chern class of O(1) on projective line": eight
  unrelated Proj section/basic-open results; no comparison theorem.
- Loogle: `"Kummer", "Chern"`: zero hits.
- Mathlib grep `Chern|chern|Kummer.*support|origin.*class` in AlgebraicGeometry:
  zero hits.
- LeanSearch: "Naturality of extension by zero counit compares the supported Kummer
  class of an affine origin with the positive projective Chern class": eight
  unrelated exterior-power/projective-resolution results.
- rg in upstream WeilConjectures and project Sheaf for supported Kummer, origin/Chern
  and origin/projective found the reusable interfaces above but no exact theorem.
- grep -rn of the node id in WeilConjectures and search of lean_names_upstream
  found no existing declaration for the item.

The first draft's slow derived-instance comparisons were diagnosed with temporary
profiling and #check probes; no such probes are part of the final module. An external
sandbox disappearance during the interrupted run required restoring the draft from
its recorded contents; no delivery was repeated, and no live file was edited.

## Second reading by Q110

The dispatcher explicitly forbids spawning another agent; the maintainer performs
independent delivery review. This is a fresh in-thread reading, not a claim to a
second worker's review. The chart order, boundary normalization, actual counit,
positive transition, source-one identification and final arrow equality were checked
against the node. The record and equation-predicate packaging is purely definitional; no hypothesis or
clause is discarded. The theorem has one sorry and its complete six-step proof plan.

## New nodes

`def-pur-origin-comparison-arrows` defines the previously missing specialized
canonical maps for the fixed chart: closed restriction exchange, the actual supported
and twist counits with their exact single/shift comparisons, constant sections,
compact sections and Ext realization. It also writes out the five categorical
equations as a generic predicate. These constructions are data and contain no sorry;
no comparison property is asserted by the definition node. It follows the same
blueprint Step 2 and is used by the theorem. The LeanFinder search returned eight
unrelated Weierstrass/projective-point results; LeanSearch returned eight unrelated
extend-zero results; Loogle returned zero with an unknown identifier; Mathlib grep
returned zero. Project/upstream rg found no specialized names; blueprint_refs and
DAG grep found the theorem's source but no separate owning definition node. Exact
queries and results are recorded in the new node. The module uses existing generic
functors and canonical comparisons and adds no alternate notion of compact support.

The record fields are hX/hP/hIX/hIP, transport, restriction, affineClass,
projectiveClass, chern, sourceIso, restriction_normalization, affine_boundary,
projective_boundary, divisor_iso, divisor_transition, chern_normalization and
equations. The last field expands via `originComparisonEquations` to the five
listed actual-arrow assertions. Its generic definition permits independent
categorical instances and imposes no extra condition. Public map result types
use the exact existing derived objects, avoiding repeated kernel normalization.

Validation: the prescribed scompile.py compiled both delivered modules cleanly,
including their separate library phases (canonical maps approximately 35 seconds,
statement approximately 6 seconds). The first delivery dry run found two new-node
citations requiring separate brackets; these were repaired without changing content.
