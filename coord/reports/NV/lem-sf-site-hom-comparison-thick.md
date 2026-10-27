## Worker report

Item: lem-sf-site-hom-comparison-thick. Module:
`Sheaf.AlgebraicGeometry.SiteHomComparisonThick`. This is a stage-2 statement delivery:
the two theorem proofs are `sorry`; all supporting definitions have actual data.
No mathematical statement correction, new node or dependency replacement is needed.
The previous worker's stage-1 reviewed/split finding does not constitute a stage-2
Lean statement: the live item has no `lean` record.

The source is the current blueprint's
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`,
paragraphs 1--2, read with its statement file, and Stacks
`literature/stacks-project/sites-cohomology.tex`, Tags 08J9, 08JB and 08JC.
The node retains its original source record; the current blueprint places the same
comparison argument under smooth purity. Its arbitrary-etale-object restriction is
supported by 08JB, which concerns slice restriction, rather than just open restriction.

Clause correspondence:

- Scheme T is `X : Scheme.{u}`; the coefficient hypotheses are exactly
  `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`. The size convention is the existing
  small-site `ModuleCat.{u + 1} A` convention, allowing every finite commutative ring.
- The ordinary unbounded categories are the recorded `Etale.DerivedCategoryModule A X`
  and `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat A))`.
  The Hom bifunctors are the existing `Etale.derivedHom` and `ProEtale.derivedHom`,
  definitionally the existing closed derived-tensor internal Homs. No Hom or derived
  category is reconstructed.
- F is exactly `(comparisonUpperStar (ModuleCat A) X).mapDerivedCategory`.
  The specified beta is exactly `siteComparisonEvaluationHom (ModuleCat A) X K M`.
  The fixed-coefficient source and target functors are named by `siteHomComparisonSource` and
  `siteHomComparisonTarget`, with source the opposite of the etale derived category.
- For each arbitrary M, `siteHomComparison_exact_thick` supplies coherent `sB`, `sE`
  and an actual natural transformation beta. Its component equality fixes EVERY
  component to the recorded evaluation transpose, excluding arbitrary isomorphisms.
  The transparent definitions `siteHomSiteExactThick` and
  `siteHomExactThickAssertion` spell out these quantifiers and every following
  exactness clause before specialization to `ModuleCat A`. Under those shift
  structures both functors satisfy `Functor.IsTriangulated`.
  That class also yields their additivity; it is the exact-functor assertion.
- `NatTrans.CommShift beta ℤ` is compatibility with ALL signed shifts. The following
  two component equations specify the shift structures themselves, using the
  adjunction-mate `siteHomSourceShift` (with its explicit opposite-integer
  transport `siteHomOppositeSourceShift`) and the exact comparison functor's shift.
  The common scalar `(n * (n + 1) / 2).negOnePow` is the coherent opposite-category
  normalization of `signedDerivedInternalHom_exact`: at n=1 the raw source shift
  at -1 has a minus sign; at n=-1 the raw source shift at 1 has no correction.
  Thus the existential shift structures cannot be arbitrary structures selected
  solely to make the transformation exact. `siteHomTensorParameterShift` uses
  the existing derived tensor shifts, and `siteHomSourceShift` is their unique
  right-adjoint mate, not a separately chosen Hom shift.
- For EVERY distinguished triangle T, the theorem explicitly supplies a triangle
  morphism between the B and C images of `triangleOpEquivalence.functor.obj (op T)`.
  Its vertices are beta at T.obj3, T.obj2, T.obj1 in that order. A `Triangle` morphism
  includes the boundary square to the shifted first vertex, not just two squares.
  Both rows are distinguished by the two exactness assertions and the standard
  distinguished-triangle structure on the opposite category.
- The locus is exactly `fun K => IsIso (siteComparisonEvaluationHom ... K M)`.
  `ObjectProperty.IsTriangulated` says it contains zero, is shift stable and is
  extension closed up to isomorphism. `IsStableUnderRetracts` additionally implies
  closure under isomorphism. The standard rotation/shift consequences give cone
  closure and all triangle two-of-three statements. These properties imply closure
  under finite biproducts, including the empty sum, by the split triangle. Together
  they express exactly all the thick-closure clauses of the node.
- The second theorem quantifies over `U : X.Etale`, with no open immersion condition,
  and arbitrary unbounded K,M. The exact restrictions are the native derived
  `Etale.upperStar U.hom` and `ProEtale.upperStar U.hom`. Existing
  `upperStarIsoLocalizationRestriction` on each site identifies these with slice
  restrictions. `siteHomEtaleObjectHom X U` is exactly U.hom, with the source and target
  explicit so derived functor parameters do not retain slice-object wrappers.
  `siteHomRestrictionSquare` specializes the generic arrow construction
  `siteHomRestrictionSquareFor` and is the localization of the recorded
  ordinary adjunction-mate comparison, conjugated by the exact composition isos.
- The two `siteHom*RestrictionHom` maps are defined using `ihomComparison`, the
  transpose of evaluation with the canonical strong monoidal pullback structure.
  The structures derive the ORDINARY tensor comparison with `residueDerivedMonoidal`
  and transport along `leftDerivedFunctorIsoMapDerivedCategory`. No arbitrary
  `Nonempty` monoidal data or map is used. The generic helper caches this existing
  construction to prevent expensive repeated elaboration. The generic
  `siteHomEtaleRestrictionEvaluation` and `siteHomProEtaleRestrictionEvaluation`
  assemble its evaluation transpose before finite-coefficient specialization;
  their explicit monoidal argument is instantiated by the canonical constructions,
  and is never an extra hypothesis of either theorem.
- The transparent definition `siteHomRestrictionAssertion` is specialized by
  `siteHomComparison_restriction` at the finite coefficient category and the
  two canonical monoidal structures.
  `siteHomRestrictionSquareAssertion` spells out the equation over four categories
  with their four actual Hom bifunctors. `siteHomRestrictionAssertion` works over an
  abstract scheme arrow and instantiates every functor, comparison and component
  with the canonical site declarations. It asserts invertibility of the two canonical Hom
  restriction maps and the full comparison equation. Its left route applies local F
  to the etale Hom restriction, then local beta, then the contravariant first-variable
  and covariant second-variable transports by the canonical square. Its right route
  is the square at global Hom, restricted global beta, and proetale Hom restriction.
  The Hom restriction maps are evaluation transposes by definition, so this equation
  expresses compatibility with restricted evaluation as well as beta.
- No boundedness, finite Tor, constructibility, nonemptiness or nonzero-ring
  hypothesis occurs. Each variable and universe is explicit (`autoImplicit false`).

Dependency declarations read and used (all recorded statement-dependency modules are
imported; the additional landed definition node records the canonical square data):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  the finite fixed-coefficient realization and `FiniteCoefficientEtaleDerivedCategory`;
  these identify the native sheaf encoding used here with the ringed coefficient model.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  the native `Etale.derivedHom` and `ProEtale.derivedHom` internal-Hom interfaces.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `CategoryTheory.ringedDerived_closed_symmetric_monoidal` and the closed tensor data.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, `proEtaleSiteComparisonModules`, canonical adjunction.
- `Sheaf.Paper.ComparisonPullbackExact`: `AlgebraicGeometry.comparisonPullbackExact`;
  native exact `comparisonUpperStar` is its fixed-coefficient encoding.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison`:
  `AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom`, with its derived
  monoidal normalization and canonical tensorator.
- Mathlib triangulated-category node: `Pretriangulated`, `IsTriangulated`,
  `Functor.IsTriangulated`, `NatTrans.CommShift`, `ObjectProperty.IsTriangulated` and
  `ObjectProperty.IsStableUnderRetracts`, and the standard opposite triangle equivalence.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`:
  `CategoryTheory.RingedHomUniverses.sourceShift`, `homCommShift`, `hom_isTriangulated`.
- `Sheaf.CategoryTheory.SignedDerivedInternalHomExact`:
  `signedDerivedInternalHom_exact`, whose coherent source-shift normalization is used.
- Additional landed stmt_dep `def-per-site-comparison-pullback-data`, module
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `AlgebraicGeometry.ProEtale.supportSiteComparisonCoefficientPullbackIso`, whose
  ordinary canonical comparison is localized by `siteHomRestrictionSquare`.
- `Sheaf.Paper.IntegralResidueDerivedMonoidal`:
  `CategoryTheory.Functor.residueDerivedMonoidal`, and the native etale/proetale
  flat-preserving strong monoidal inverse images. Etale flat preservation holds
  for finite coefficients; proetale flat preservation here is the recorded theorem
  `preservesFlat_upperStar_of_weaklyEtale U.hom`, since U is etale.

The full seven-step node proof is rendered in the two theorem docstrings: K-injective
models and chain-map comparison, identification with the specified evaluation transpose
on K-flat tensors, signed shifts and the third triangle square, thick closure and the
explicit retract inverse, and slice evaluation/mate normalization. These are explanations
of the postponed proofs, not new proof axioms or additional hypotheses.

Edge cases checked before writing: M=0, K=0, the zero coefficient ring, the empty scheme,
the identity etale object, an empty etale object, and etale objects which are not open
immersions. No construction excludes them. At n=0 the scalar is 1; at n=1 and n=-1 the
opposite-category normalization agrees with the recorded signed exactness convention.
Retracts need not split globally in an idempotent-complete hypothesis: the assertion
only uses an actual given retraction. Finite sums follow from split triangles, not an
infinite-sum or compactness assumption. No statement is disputed.

Searches for reuse:

- `msearch.py NV lem-sf-site-hom-comparison-thick leanfinder` with query
  "The evaluation derived internal Hom comparison for etale to proetale pullback
  commutes with shifts and has a thick isomorphism locus": eight ordinary module
  pullback results; no statement of this comparison's exactness/thick locus.
- `msearch.py ... loogle` query
  "CategoryTheory.NatTrans.CommShift, CategoryTheory.ObjectProperty.IsTriangulated":
  zero results.
- `msearch.py ... grep` query `ihomComparison|NatTrans.CommShift` in CategoryTheory:
  25 generic closed-functor and signed-shift declarations; no site theorem.
- `msearch.py ... leansearch` query
  "The internal Hom comparison of the etale proetale inverse image is an exact
  natural transformation with a thick isomorphism locus": eight results including
  generic expComparison/sheaf Hom; none states this item.
- `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the item, proposed declaration names,
  `siteComparisonEvaluationHom`, `derivedHom`, source shifts and exactness. No
  existing declaration states this item. Native source-Hom shifts and ringed signed
  shifts are reused through their common adjunction-mate construction. No copied Hom,
  category or evaluation comparison is introduced. The final `grep -rn` of the item id
  in `lean/WeilConjectures` also returns no declaration.

Validation uses only the authorized `scompile.py` per-file server compiler. Temporary
probes in scratchpad are not delivered. Compiler checks and delivery preflight results
are recorded below once complete.

Final validation: the delivered module passed `scompile.py` on 2026-10-22,
with no errors or warnings: sandbox 13.9 seconds; published-library module
23.6 seconds. No heartbeat increase, warning suppression or global build was used.
The only postponed proofs are the two named node theorem declarations.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
