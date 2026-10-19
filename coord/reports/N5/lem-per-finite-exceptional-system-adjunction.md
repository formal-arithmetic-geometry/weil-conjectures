## Worker report

The item is stated in `Sheaf.Paper.FiniteExceptionalSystemAdjunction`, namespace
`AlgebraicGeometry.FiniteExceptionalSystems`. It asserts `Nonempty (Family l E f)`:
actual finite adjunctions and actual adjunction functors on full subcategories of the
ordinary derived categories of strict semilinear systems, together with comparison
maps and equations. Every theorem has proof `sorry`; definitions contain real data.

Sources read: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 6.7.18,
printed pp. 57--58 (including its proof and both coefficient squares), and the current
blueprint `main-20261015`, `lem-per-artin-gabber-affine-curve.md`. The node explicitly
identifies its normalized-system assertion as an agent-formulated strengthening,
not a quotation of Lemma 6.7.18. Its fifteen-step proof plan is carried in the main
Lean declaration's docstring.

Hypotheses and clauses:

| Node | Lean rendering |
| --- | --- |
| Arbitrary field k | `(k : Type u) [Field k]`; no finite-field datum, algebraic closedness or cohomological-dimension assumption |
| Prime l invertible in k | `(l : ℕ) [Fact l.Prime]`, `_hl : IsUnit (l : k)` |
| Finite extension E/Q_l | `E : Type (u + 1)`, `Field E`, `Algebra (Padic l) E`, `FiniteDimensional (Padic l) E` |
| Its valuation ring and chosen uniformizer | The existing `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`; no replacement valuation ring |
| Positive finite quotients | `Coeff l E n = coefficientExtensionRing l E (n+1)`, with finiteness from the recorded dependency theorem |
| Separated finite-type k-schemes | The `Over (Spec (.of k))`, structure-morphism `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` binders on X and Y |
| Separated finite-type k-morphism | `f`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` |
| Chosen compactification f=pj | `Family` supplies data for every `c : Compactification f`; this packages the chosen compactification and the statement's compactification comparisons simultaneously |
| Ordinary small-etale compact support F_n | `F l E c n` is exactly `Etale.rightDerivedLowerShriekOfCompactification (ModuleCat (Coeff l E n)) c` |
| Bounded constructible and finite Tor amplitude | `Ctf` combines recorded `isBoundedConstructible` with `∃ a b, hasTorAmplitudeIn ... a b`; the latter tests every module sheaf in degree zero |
| Ambient exceptional adjoint and its restriction | `FiniteData.right`, `adjunction`, `leftCtf`, `rightCtf`; the same finite unit/counit restrict to the full Ctf subcategories |
| Exact A_n-linear finite exceptional functor | `rightAdditive`, `rightShift`, `rightExact`, `rightLinear` |
| Actual coefficient quotient functors | `quotient` is `Ideal.Quotient.factor` for the inclusion of powers; `Q` is the published `Etale.scalarExtension` |
| Canonical projection q | `FiniteData.projection`, normalized componentwise to the existing `ExceptionalCoefficients.compactSupportMap` |
| Counit transpose b | `comparison` and `counit`; the displayed equation fixes the transpose since q is invertible and `adjunction` gives a Hom bijection |
| b invertible on Ctf | `comparison_isIso`, with exactly the `Ctf` domain |
| Identity and quotient cocycles | `projection_id`, `comparison_id`, `projection_comp`, `comparison_comp`, with the canonical `self` and `assoc` scalar comparisons |
| Preserve finite units and counits | `FiniteData.unit` and `counit` |
| Commute with shifts | `projection_shift`, `comparison_shift`, and the adjunction-compatible `unit_shift`, `counit_shift` |
| Strict semilinear module systems, componentwise exactness | Existing `strictEtaleCoefficientSystem` and its ordinary `DerivedCategory`, via `StrictEtaleCompactSupport` and `StrictEtaleEvaluation` |
| Normalized, levelwise Ctf systems | `NormalizedCtf`, using existing `IsNormalizedCoefficientSystem`, followed by `∀ n, Ctf ...` |
| No bound uniform in n | Boundedness and the Tor interval are inside the `∀ n` clause of `NormalizedCtf` |
| Actual simultaneous compact support | `Support` reuses `StrictEtaleCompactSupport`; `systemLeft` is its actual `functor`, restricted using `ObjectProperty.lift` |
| Preservation of normalized subcategories | `SystemData.preserves` |
| Exact system right adjoint | `SystemData.right`, `adjunction`, `rightAdditive`, `rightShift`, `rightExact` on the induced triangulated full subcategories |
| R-linearity | `actionX` and `actionY` use the existing section-normalized `StrictEtaleScalarAction`; `linear` asserts preservation of that actual R-action |
| Natural evaluation isomorphisms | `leftEvaluation_pinned` fixes the left iso to `S.evaluation n` and `levelRealization`; the unit and counit then fix `rightEvaluation` |
| Evaluated system units/counits are finite ones | `SystemData.unit`, `counit` |
| Actual transition compatibility | `Presentation` fixes the scalar-restriction presentation comparison on sections and on complex representatives; `reduction` transposes the actual derived transition; `right_transition` is precisely b followed by the finite right adjoint of the input reduction; `left_transition` is its q counterpart |
| Both system triangle identities before evaluation | `SystemData.adjunction` is a genuine Mathlib `Adjunction` on the full derived-system subcategories, not a levelwise collection of Hom bijections |
| Compactification independence | `Family.leftComparison`, `rightComparison`, identity/cocycle fields; `left_evaluation` uses the existing ordinary canonical compactification iso, `right_counit` fixes adjunction conjugation, and `right_evaluation` identifies its finite counit-preserving conjugate |
| No integral inverse limit or integral exceptional operation | The only objects in the statement are finite derived categories and ordinary derived categories of strict systems |

The auxiliary `levelRestriction` changes the presentation of a finite coefficient
module by the existing canonical `realizationRingIso` and
`constantRingModuleRestriction`, rather than defining another scalar action or another
module-sheaf category. Its derived functor is `realization`. Its exactness/equivalence
interface and the stability of `NormalizedCtf` are named postponed theorems with source
and proof docstrings. The coefficient identity and composition theorems are the two
quotient induction facts needed to instantiate the existing canonical scalar unit and
associator. They are part of the item's identity/cocycle clauses.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and the imported coefficient constructions.
- `WeilConjectures.Compactification.Refinement`:
  `AlgebraicGeometry.Compactification`, `Compactification.Refinement` and its category.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification` (ordinary unbounded interpretation).
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` and its upstream imports:
  `Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.Paper.SemilinearDerivedSections`:
  the ordinary simultaneous system calculus, `SemilinearDerivedSectionsData`.
- `Sheaf.Paper.EtaleCoefficientSystemAdjoint`:
  `StrictEtaleCompactSupport`, `StrictEtaleEvaluation`, `strictEtaleCoefficientSystem`,
  `strictEtaleLevel`, and the section-normalized `StrictEtaleScalarAction`.
  Its finite-field existence theorem is not used as the arbitrary-field assertion.
- `Sheaf.Paper.ExceptionalCoefficientComparison`:
  `Etale.ExceptionalCoefficients.compactSupportMap`.
- `Sheaf.Paper.NormalizedEtaleOriginWitnesses` and its imports:
  `ProEtale.normalizedOriginScalarUnit`, `ProEtale.pbcFixedScalarExtensionComp`.
- `Sheaf.CategoryTheory.ConstantRingModuleSheaves` and
  `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `constantRingModuleRestriction`, `realizationRingIso`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded`:
  `Etale.rightDerivedLowerShriekOfCompactificationIso`.
- Mathlib `ObjectProperty.FullSubcategory`, `ObjectProperty.lift`, its induced
  triangulation, ordinary `Adjunction`, and `NatTrans.CommShift`.

The definition ownership nodes used by these helpers are added to `stmt_deps`; no
natural-language statement, proof step or proof dependency was changed.
The existing `strictEtaleLevelDerived` and `strictEtaleSystemDerived` instances
are assigned higher synthesis priority in this module so that geometric proof
imports cannot replace the localizations stored in `StrictEtaleEvaluation`.
No new derived-category instance or category is constructed.

Edge cases checked in the statement: n=0 indexes the first positive quotient, not the
zero quotient; equal quotient indices use the canonical scalar identity; triple indices
include equalities; quotient maps are never assumed flat; the zero complex and empty
scheme are allowed; k need not be finite or algebraically closed; bounds may vary with n;
no smoothness or regular-immersion assumption is imposed on f. The site object universe
is u+1, morphisms u, coefficient carriers u+1, and derived Homs u+2; they are not forced equal.

Searches for existing statements and notions:

- `msearch.py ... leanfinder "exceptional right adjoint finite Tor constructible coefficient normalized derived systems"`:
  eight generic Tor/derived-adjunction results, no match.
- `msearch.py ... loogle "Adjunction, mateEquiv"`: no hits (unknown short identifier
  `Adjunction`); source inspection supplied the fully qualified categorical APIs.
- `msearch.py ... grep "exceptional|Normalized" CategoryTheory`: two unrelated bicategory
  coherence hits, no exceptional-system statement.
- `msearch.py ... leansearch "right adjoint exceptional pullback normalized coefficient systems derived category"`:
  eight generic right-adjoint results, no match.
- `rg` on upstream `WeilConjectures` and the shared `lean/Sheaf` for the item id,
  `finiteExceptional`, and normalized-system names: the existing intrinsic pro-etale
  exceptional functor has different categories; the strict etale coefficient adjunction
  is a finite-field statement with a different domain. Both were read and not rebound.
- The recorded constructibility and Tor declarations were read in full. The older
  upstream `boundedConstructibleFiniteTor` uses another constructibility presentation;
  `Ctf` uses the exact recorded dependency predicates instead.

## Return repairs

R1: Removed all four erroneous theorem statement dependencies:
`lem-pur-etale-coefficient-system-adjoint`,
`lem-pur-exceptional-coefficient-comparison`,
`lem-weil-pbc-normalized-etale-origin-witnesses`, and
`lem-cbc-constant-ring-module-sheaves`. Their plain definitions are now owned by
`def-per-strict-etale-system-interfaces`, `def-per-exceptional-coefficient-maps`,
`def-per-scalar-extension-unit`, and `def-sfb-constant-ring-module-restriction`.
`def-weil-pbc-witness-compatibility` is cited for `pbcFixedScalarExtensionComp`.
Neither new definition record extracts data from a theorem; both reuse existing
published definitions, with `existing: true` and no duplicate Lean module.

R2: `Family.support_evaluation` identifies the common PX/PY with each support
record's endpoints. `SystemData` takes these equalities explicitly. Its
`leftEvaluation_pinned` equation is componentwise composition of the endpoint
identifications, the existing `S.evaluation`, realization, and `levelRealization`.
The latter is an actual composite definition, not a free isomorphism.
`GeometricComparison.sections` fixes the ordinary direct comparison to the exact
underlying-set comparison in `StrictEtaleOrdinaryImage.rightUnderlying` on every
section. Its ordinary inverse is fixed by `transpose`, its derived inverse by the
localization `representative` equation on every complex, and its derived direct by
`counit`. `LevelComparison.open_counit` fixes the open comparison as the adjunction
mate. `levelRealization` composes proper then open comparisons. Thus simultaneous
unit twists of the left/right evaluation isomorphisms no longer satisfy the
left-evaluation pinning equation. Unit and counit equations uniquely determine the
right comparison once the left one is fixed.

The advisory shift issue is repaired too: `quotientShift` is the canonical shift
induced by the scalar adjunction to exact restriction. `supportOpenShift` and
`supportInverseShift` localize the existing termwise shift via their recorded
factorizations; `supportDirectShift` is induced by the proper adjunction;
`supportShift` composes these, and `systemLeftShift` uses Mathlib's full-subcategory
lift shift. No free leftShift or scalarShift field remains. The right functors
still carry their shift structure together with the adjunction-compatibility
equations, as required by the exact right-adjoint assertion.

R3: Dropped both the stale SemilinearSystemModels module and its dependency-node
copy, and removed the extra `def-coef-semilinear-system-models` statement edge.
The item uses the published Q03 interface through its existing imports.

## New nodes

`def-per-strict-etale-system-interfaces` records the exact existing definitions in
`Sheaf.Paper.EtaleCoefficientSystemAdjoint`: strict systems, finite levels,
evaluations, scalar action, and the specified open/proper compact-support package.
Its source is Zheng, Constructions 4.1 and 5.14–5.15. The finite-field existence
theorem in that module is not part of this definition. The DAG grep and blueprint
search found no separate general definition node; the clopen comparison node is
a different specialized comparison. LeanSearch (eight unrelated scalar/support
hits), LeanFinder (eight ordinary ModuleCat scalar-unit hits), and Mathlib grep
(no hits) found no matching interface. Project grep found these exact definitions;
upstream WeilConjectures grep found none. Raw search results are in the node.

`def-per-scalar-extension-unit` records the exact existing
`normalizedOriginRestrictionUnit` and `normalizedOriginScalarUnit` in
`Sheaf.Paper.NormalizedEtaleOriginWitnesses`: identity on sections, followed by the
derived adjunction mate. Its source is Stacks 06YY, identity scalar extension.
It does not assert the etale-origin witness theorem. The same three Mathlib
searches and DAG/blueprint/upstream/project searches distinguish it from the
existing theorem node and locate its two existing definitions.

## Self-check of the repaired packet

The delivered statement has the original arbitrary-field hypotheses and all
finite/system/refinement clauses mapped above. No natural-language correction is
needed. I checked the endpoint casts for both directions; the pinning equation
starts at evaluation of the actual system compact support and ends at the finite
compact support of evaluation. The geometric transpose and derived representative
equations are correctly oriented, and the open counit equation determines its
mate. Identity quotients, equal triple indices, the first positive level, empty
schemes, and varying Tor/cohomological bounds remain covered. All universes and
variables are bound; no site/coefficient universe equality was added.

This is the worker's own check; independent maintainer review is still required.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
