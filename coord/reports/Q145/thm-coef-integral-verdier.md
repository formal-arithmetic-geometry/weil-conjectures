## Worker report

Q145 states `thm-coef-integral-verdier` in
`Sheaf.SixFunctors.IntegralVerdier`, declaration
`WeilConjectures.integral_verdier_biduality`. The theorem has only `sorry` as its proof.
Its docstring follows all eight proof steps of the DAG node. Definitions have actual
functor, morphism, tensor-generator, or scalar-adjunction data. No integral dual is
constructed by choosing a limit.

The node and its source were read together: blueprint
`sec-six-functors/sk-prop-sf-biduality-general/thm-coef-integral-verdier.md`, order 2146.
This node has no main-20261015 blueprint_update; its recorded master source is followed.
The natural-language statement is retained.

Hypotheses and objects, in source order:

- `D : FiniteFieldDatum` is the global finite-field datum, with its algebraic closure `D.k`.
  `[Fact l.Prime]` and `hl : l ≠ D.p` impose precisely the coefficient characteristic
  conditions. `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]`
  give the finite extension. All coefficient rings and uniformizers are the recorded
  `Padic.coefficientExtensionRing` construction, never a new ring or selected ideal.
- `X : Scheme`, `[X.Over (Spec (.of D.k))]`, locally finite type and quasi-compactness
  of `X ↘ Spec (.of D.k)`, and its `IsSeparated` instance render separated finite type
  over the stated field. No properness or smoothness is assumed.
- `Ambient l E X` is the unchanged ordinary derived category of
  `scalarReductionSource.{u,u} l E X`. The small pro-etale site retains object universe
  u+1 and morphism universe u. The coefficient sheaf is
  `completedIntegralCommRingSheafUnrestricted`; the D/hl spelling used by the Hom
  presentation is its definitionally identical recorded spelling.
- The input `ω : sfIntegralConstructibleCategory l E X` and its family of specified
  reduction isomorphisms `r` express the dualizing object with reductions supplied by
  `prop_coef_integral_dualizing`. The finite object is the existing
  `integralDualizingFiniteTerm l E D X n`, the exceptional image of the coefficient unit.
  This theorem does not assume any conclusion of integral Verdier biduality about ω.
- `dual` and `finiteDual` are the curried ambient K-injective internal Hom
  `IntegralHom.hom` into those objects, respectively. The object K is never replaced
  by its reduction tower or assumed site-perfect. Positive level n+1 is indexed by n:ℕ;
  every positive quotient, including the residue quotient at n=0, is covered.

The conclusion is an existential package of normalized tensor presentations and proofs
of the following clauses. Existence of the presentations is a conclusion, not a hypothesis.
Their K-flat/K-injective and homogeneous-generator normalizations are those of
`IntegralHom.TensorPresentation` and `IntegralHom.ReductionPresentation`.

- `categories_equal` is the equality of the two recorded object properties
  `sfIntegralConstructible l E X = finiteTorConstructibleIntegral l E X`, hence of their
  full subcategories.
- `preservation` says the actual ambient dual of every member again satisfies the same
  object property. `restrictedDual` uses `ObjectProperty.lift` on that very functor.
  `anti_equivalence` states `IsEquivalence` of this restriction from the opposite category.
- `exact` supplies a `CommShift ℤ` for the ambient contravariant dual and sends each
  distinguished opposite triangle whose three vertices are constructible to a
  distinguished triangle, including its actual connecting arrow under that shift.
  The opposite uses Mathlib's reversed integer shift. This is exactness on the inherited
  triangulated full subcategory, without choosing another triangulation.
- `comparison` is the recorded evaluation-defined `IntegralHom.comparison`, followed by
  internal Hom covariantly applied to the specified `r n`. `comparisons` asserts
  invertibility for every K and every positive level.
- `evaluation` is the commuting reduced-evaluation equation, with the canonical
  reduction tensor comparison `mu`, the actual adjunction counits, and `r n`.
  `transposes` is its adjunction equation for every ambient object V and every map
  V → DK, so it preserves all transposes rather than only an unspecified pairing.
- `finiteTerms` uses actual derived restriction of scalars applied to the finite duals.
  `finiteTransition` is the quotient transition of DK conjugated by its comparison
  isomorphisms. `finiteEvaluation` explicitly reduces K and uses the scalar
  extension/restriction counit before finite evaluation. `dualizingTransition` is the
  corresponding actual dualizing reduction map transported by r.
  `transition_evaluation` states the equation characterizing the finite evaluation
  transition. Thus reconstruction is on the indicated tower with its specified maps.
- `finiteLeg` is the actual reduction unit followed by the comparison. `reconstruction`
  supplies the product and the connecting arrow of `IsDerivedLimitTriangle`, with
  `Pi.lift finiteLeg` as the first map. Its middle arrow is therefore the recorded
  Roos `1-s`, not an ordinary inverse limit or an isomorphism to an independent model.
- `tor_bound` quantifies over each d:ℕ with
  `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, every integer a≤b, and all input reductions
  with recorded `HasProEtaleTorAmplitude` [a,b]. Its output is exactly [-b-2d,-a] at
  every reduction. The source's numerical bound is not replaced by mere boundedness.
- `SignedSymmetry` fixes tensor interchange on every homogeneous local generator by
  (-1)^(ij). `delta` transposes actual evaluation with these interchanged factors.
  `reduction_delta` includes both Hom comparisons, with the inverse of the first in
  the contravariant argument, and equals the finite evaluation-defined delta.
  `biduality` makes this actual map invertible. `naturality` is its commuting square
  for every morphism in the full constructible subcategory.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient module:
  `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing`, the valuation
  ring, uniformizer and quotient construction.
- Mathlib finite type/proper morphisms: `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
  Properness is not used as an input, since the node assumes only separatedness.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and completed coefficients:
  the recorded completed coefficient sheaf, with no universe identification.
- Mathlib pro-etale site: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`; `Sheaf.Paper.FiniteTorAmplitude`:
  `finiteTorConstructibleIntegral` and `HasProEtaleTorAmplitude` from its imports.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionSource`, `scalarReductionTarget`, `scalarReductionDerivedExtension`,
  `scalarReductionDerivedRestriction`, `derivedScalarExtensionRestrictionAdjunction`.
  Restriction is the recorded `Functor.mapDerivedCategory` of exact scalar restriction.
- `Sheaf.SixFunctors.IntegralDualizing`: `prop_coef_integral_dualizing`;
  `Sheaf.SixFunctors.FiniteDualizing`: `integralDualizingFiniteTerm` and its finite
  exceptional functor, supplied through the recorded finite exceptional interface.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `derivedInternalHomOfUniverses`, used by the recorded `IntegralHom.hom` specialization.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`;
  the sf constructible category's completeness uses the actual same reduction units
  and quotient transition maps from `Sheaf.Paper.SfIntegralReductionTower`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `IsDerivedLimitTriangle`;
  Mathlib: `topologicalKrullDim`, `WithBot ℕ∞`, products, opposite triangulation.
- `Sheaf.Paper.DualityPairing`: `Etale.ambient_duality_pairing`, its generic double-dual
  functor and pro-etale evaluation-transpose interface, read alongside the intrinsic
  tensor/Hom normalizations. The finite double-dual arrow is the same Koszul evaluation
  transpose in the ordinary module-sheaf presentation.
- `Sheaf.Paper.IntegralHomReduction`: `IntegralHom.TensorPresentation`,
  `ReductionPresentation`, `comparison`, `totalTensor`, `totalPair`, and `integralHomReduction`.
  These presentations avoid a private replacement tensor or Hom construction.

Edge cases were checked before and after writing. The empty scheme is permitted and has
Krull dimension ⊥, so d=0 is admitted. K=0 and the zero morphism remain included. There is
no positive-dimension, nonempty-support, positive cohomological degree, or nondegenerate
interval assumption: a=b and negative a,b are included. Every n≥1 is represented exactly
once by n+1. The ramified coefficient case uses the existing uniformizer quotients, not
quotients by powers of l. l=p is excluded precisely by hl; l=2 and dimension zero are
included. The actual unbounded ambient categories are retained, and the integral domain
is exactly the recorded bounded, derived-complete category; no condensed or site-perfect
substitute is introduced.

Searches for an existing complete statement:

- msearch LeanFinder: “Verdier biduality for derived complete integral constructible
  sheaves with reduction comparison”; eight unrelated hits, including general derived
  category bounded-model existence and LightCondensed closed structures; no match.
- msearch Loogle: `"dualizing"`; no results.
- msearch Mathlib grep: `integral.*[Vv]erdier|verdier.*[Ii]ntegral|biduality`; no result.
- msearch LeanSearch: “Integral Verdier biduality for constructible derived complete adic
  sheaves”; eight unrelated hits (module-sheaf pullback adjunction, locally constant
  condensed functors, adic completion equivalences and sheafification comparisons);
  no integral Verdier statement.
- rg of the named upstream `WeilConjectures` tree, the upstream-name index and this
  project's `lean/Sheaf`, plus the exact node id in the upstream tree: no declaration
  with all these integral, reduction, Roos, Tor-bound and actual-delta clauses. Existing
  finite duality, integral Hom reduction and dualizing interfaces were read and reused.

## Second reading by Q145

The dispatcher explicitly forbids starting another agent. This is a fresh self-reading
of the node and module; independent acceptance remains the maintainer's review.
I checked the field assumptions, each category, both coefficient rings, each variance,
all positive levels, the Roos legs and transition, the interval endpoints, and the two
comparisons in the reduced double-dual square. During this reading I made the finite
transition's evaluation equation explicit, retained arbitrary-transpose compatibility,
and used the inverse comparison in the contravariant Hom argument. I replaced a large
structure of dependent fields by the logically identical existential package to avoid
expensive generated recursors. Exactness is expressed on ambient triangles with
constructible vertices, avoiding a second full-subcategory shift instance. No source
hypothesis or conclusion was changed.

## Dependency modules

`lem-weil-delta-restriction`: the recorded `Sheaf.Paper.DeltaRestriction` module is
unusable with the integral finite-coefficient framework: its pro-etale theorem refers
to absent `derivedHom` and `derivedTensorHomAdjunction` wrappers, and its legacy
`UpperLowerStar.Iso` import duplicates names from the finite-coefficient `Iso` module.
A first wrapper-unfolding compile exposed the second problem, so the delivery repairs
both. The module retains its complete etale statement, jointly surjective-cover
criterion, arbitrary-Omega pro-etale statement, all coefficient/field/finite-type
hypotheses, canonical dualizing map, and evaluation/transposition equations. Only the
pro-etale tensor, Hom and adjunction wrappers are unfolded to their native definitions.
The ordinary inverse image is the definitionally identical finite-coefficient interface.
The derived tensor comparison is supplied by the named
`deltaRestrictionTensorComparison_normalized` theorem: its square with localization
lax tensor and the ordinary oplax tensor map holds on all homotopy complexes. The ordinary cochain comparison first passes through
the homotopy quotient, exactly as in the upstream tensor derivation. This universal
normalization determines the natural isomorphism, so its extraction is not data chosen
from mere existence. Its proof docstring explains K-flat derivation and uniqueness.
All proof obligations remain named sorry-only theorems attached to this same DAG notion.

The item's statement dependencies gain this already-existing node because its actual
`CategoryTheory.restrictionDualDelta` is now used to define the main theorem's delta.
There is no new definition node. The dependency copy changes only its lean record;
no statement, source, proof or other field changes. Its original main declaration
`AlgebraicGeometry.Etale.delta_restriction` remains the main declaration, with the exact
signature from the delivered file; the normalized comparison helper is added to the
recorded declarations.

Second reading of this dependency: I compared its two site clauses against the node,
including arbitrary Omega on the pro-etale site, the etale-cover iff, all inverse-image
variances, and the canonical tensor/Hom transpose. The new comparison square uses the
ordinary degreewise inverse-image map, its homotopy quotient, and the actual localization
tensor arrows. No
exceptional adjoint on the ambient pro-etale site is asserted, no boundary-duality
hypothesis is introduced, and no site comparison equivalence is assumed.

The main module also retains the stated proof-dependency imports. The DAG proof node
`lem-weil-finite-duality-site-comparison` currently has no recorded Lean declaration;
its mathematical use remains fully documented in the proof plan, without inventing a
replacement comparison as a hypothesis of this theorem.

The repair exposes the existing native tensor, internal Hom and their exact adjunction
through plain functor signatures (`deltaRestrictionNativeTensor`,
`deltaRestrictionNativeHom`, `deltaRestrictionNativeAdjunction`). These aliases have
actual data and reuse the existing native structures; they introduce no alternative
tensor construction, adjunction, or double-dual arrow. The normalization equation is
the named predicate `IsNormalizedDeltaRestrictionTensor`, so later declarations can
use the canonical comparison without re-elaborating its representative square.

The normalization predicate and comparison type are generic in the coefficient category;
the existence theorem specializes them to the finite coefficient module category of the
node. This keeps every structure instance shared rather than re-elaborating concrete
ModuleCat instances at each occurrence. The full repaired import closure, including
EtaleGeometricBiduality and FiniteStageVerdierBiduality, compiles through scompile.py.
The new helper names were checked by rg against the upstream-name index, the upstream
source tree and the existing Sheaf tree; there were no collisions.

Validation: `scompile.py Q145 thm-coef-integral-verdier
lean/Sheaf/Paper/DeltaRestriction.lean lean/Sheaf/SixFunctors/IntegralVerdier.lean`
completed successfully for both delivered files, separately and in dependency order.
There were no errors or warnings. The repaired import closure also compiled the
existing EtaleGeometricBiduality and FiniteStageVerdierBiduality modules successfully.
The final library checks reported 43.5 s for DeltaRestriction and 40.4 s for
IntegralVerdier; the wrapper retains the prescribed per-file limit and resource settings.
