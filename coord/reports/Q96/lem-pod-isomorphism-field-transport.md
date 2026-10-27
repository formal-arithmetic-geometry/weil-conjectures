## Worker report

The module `Sheaf.Paper.IsomorphismFieldTransport` states
`WeilConjectures.isomorphismFieldTransport`, with its sole proof `sorry`.
`IsomorphismFieldTransportStage`, `isomorphismFieldTransportScalarLaw`,
`isomorphismFieldTransportRationalScalarLaw`, and `IsomorphismFieldTransportCommon`
are transparent clause packages for this same node. They introduce no new coefficient
object, category, pullback, scalar map, counit or inverse functor. The theorem docstring
contains the six-step DAG proof. No definition data is postponed.

Hypotheses, matched individually:

- The fixed tuple is `D : FiniteFieldDatum.{u}`. Its fields include p prime, a positive,
  q = p^a, the finite field k0 of that cardinality, k, and its algebraic closure structure.
- The coefficient prime and its inequality are `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- The chosen closure is `(Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
  [IsAlgClosure ℚ_[l] Ω]`. Its universe v is independent of u.
- The two k-schemes are `{X Y : Scheme.{u}}` with their separate `Over (Spec (.of D.k))`
  structures. Each structure morphism has `LocallyOfFiniteType` and `QuasiCompact`.
  Neither has an `IsSeparated` assumption. They need not descend to finite-field models.
- `(g : X ⟶ Y) [IsIso g]` is an underlying scheme arrow; there is no `IsOver` binder.
  Its specified inverse is Mathlib `inv g`; thus g need not respect either k-structure.
- A finite coefficient field is quantified by `E : Type u`, `Field E`, `Algebra ℚ_[l] E`,
  and `FiniteDimensional ℚ_[l] E`. The Ω subfields use the dependency's small models
  `Coefficient.{u} l Ω E` for `E : Index l Ω`. This does not identify u with v.
- Residue-field inverse structures `iX`, `iY` and stalk units `hX`, `hY` are existential
  conclusions, not added hypotheses. Their only purpose is to supply the published
  pullback API with the invertibility already implied by l ≠ p on k-schemes.
  The explicit instance-lambda application keeps their scope visible without a let.

Clauses, matched individually:

1. The integral category is exactly `sfIntegralConstructibleCategory`, the derived-complete
   full subcategory with constructible positive reductions and a uniform amplitude.
   The rational category is exactly `sfRationalConstructibleCategory`, its raw scalar
   localization, and the closed-coefficient category is exactly
   `generalAlgebraicallyClosedConstructibleCategory`, the actual StageSystem quotient.
2. The completed coefficient map is the recorded `inverseImageCompletedCoefficientMap`.
   `coefficient_projection` says its nth projection is
   `inverseImageCompletedCoefficientComponent`: inverse image of the Y projection,
   followed by the normalized constant coefficient map. This is the displayed limit
   comparison; the tower indexes positive powers by n+1.
3. `moduleEquivalence`, `moduleAdditive`, `moduleLimits` and `moduleColimits` assert exact
   completed-module inverse image. `moduleEpsilon` is a natural isomorphism between its
   actual composite and identity. `module_epsilon_formula` fixes it to the existing
   section-normalized `pullbackIdentityModuleCounit`.
4. `integralEquivalence` and `integralExact` apply to the prescribed
   `constructibleIntegralPullback`. `lambda_formula` fixes the natural lambda to
   `pullbackIdentityLambda`, the inverse of the specified quotient-cone kappa.
   `lambda_shift` transports precisely the termwise inverse-image shift.
   `integralShift` and `integralExact` express shifts and distinguished triangles.
   `integralLinear` retains the constant O_E action needed for rationalization.
5. `epsilon` is a natural isomorphism P_g then P_inv_g to identity; its underlying component
   is fixed by `epsilon_formula` to `pullbackIdentityEpsilon`. That declaration is exactly
   lambda for inv g, inverse image of lambda for g, then reindexing counit.
   The main theorem supplies the whole record for g and for inv g, so both composites
   and both exact inverse functors are asserted.
6. `rational_object` keeps the integral object formula. `rational_tensor` is the
   scalar-first presentation c tensor f ↦ c tensor P_g(f); `sfRationalHomCoordinates`
   identifies it with the source's f tensor c coordinates and identifies localized
   coefficients with E. `rationalAdditive` extends it to all finite sums.
   `rationalShift` is normalized to localized integral shift by
   `rational_shift_formula`; `rationalExact` gives distinguished-triangle preservation.
7. `rationalEpsilon` is a genuine natural isomorphism on the full localized category,
   so its naturality quantifies over every localized arrow, not only integral images.
   `rational_epsilon_formula` fixes its components to localization of integral epsilon.
8. `isomorphismFieldTransportScalarLaw` is the displayed integral inverse/scalar equation,
   in Lean's left-to-right composition order, using `integralPullbackScalarComparison`
   and `integralScalarExtensionOfUniverses`. The main theorem asserts it for g and inv g
   and every finite coefficient algebra embedding, including the identity embedding.
   It uses HEq only to reconcile the published equivalent endpoint encodings.
9. `isomorphismFieldTransportRationalScalarLaw` states the localized equation for the
   chosen stage epsilon and the actual natural `rationalPullbackScalarComparison`.
   Both directions are asserted for every finite inclusion in Ω.
10. `IsomorphismFieldTransportCommon.object_formula` is literally (E,P_g,E K).
    `arrow_formula` is the actual `ofHom` quotient class at L of alpha_source,
    P_g,L(u), alpha_target inverse, with the dependency's transition identifications.
    It is asserted for every representative and common field of a fixed quotient
    functor, so representative/field independence and composition are part of the
    actual functor's action, not an arbitrary separately supplied map.
11. `epsilon` on the common category is a natural isomorphism between the actual
    composite functor and identity. `epsilon_formula` fixes its component to inclusion
    of the same finite-stage rational epsilon at P.stage. The record for inv g gives
    the opposite composite. `equivalence`, `shift`, `exact`, and `additive` give the
    asserted exact inverse equivalence on actual common-stage arrows and triangles.
    `stageComparison` is normalized to identity on literal pairs, and `stage_shift`
    identifies the common shift with the localized finite-stage shifts. Thus the
    fourth arrow of a triangle uses the specified finite-stage realization.
12. No Karoubi carrier occurs anywhere. All comparison targets are whole derived
    objects or functors, never just their cohomology groups.

Dependency interfaces read and used (namespace WeilConjectures unless indicated):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, its category.
- `Sheaf.Paper.SfRationalizationKaroubi`: the raw category, localization,
  scalar extension, and Hom coordinate equivalence.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the category,
  `GeneralAlgebraicallyClosedCoefficients.ofHom`, `inclusion`, `inclusionCommShift`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `integralPullbackScalarComparison`,
  `rationalPullbackScalarComparison`, `commonStageDerivedPullback`,
  `commonStagePullbackObject`, `commonStagePullbackComparison`.
- `Sheaf.Paper.PullbackIdentitiesScalarExtension`: `pullbackIdentityLambda`,
  `pullbackIdentityEpsilon`, `pullbackIdentityModuleCounit`.
- `Sheaf.Paper.IsomorphismDerivedPullback`: its coefficient limit comparison and
  termwise module/derived comparison are the proof route.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`: the exact sectionwise
  transport used by `AlgebraicGeometry.ProEtale.inverseImageIntegralModules`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: the specified completed scalar map.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`
  and the reexported valuation ring, chosen uniformizer and quotient rings.
- Mathlib `CategoryTheory.NatTrans.CommShift` and
  `CategoryTheory.Functor.CommShift.comp`: `stage_shift` states the shift square
  directly with both composite shift structures explicit. The inclusion shifts are
  `GeneralAlgebraicallyClosedCoefficients.inclusionCommShift`; the other two are
  the record's `shift` and `(S E).rationalShift`.
- `Sheaf.Paper.IsomorphismPullbackTExactCoefficients` is imported only for the
  existing proof route. Its theorem is in `proof_deps` only, not `stmt_deps`.
- `def-weil-scheme-morphism-properties` is a convention record with no declaration;
  the actual scheme, finite-type properties and `IsIso` are Mathlib's.

All recorded proof modules are imported. The exact-functor and Noetherian leaves use
Mathlib's `Functor.mapDerivedCategory` and its exact/shift instances and the Noetherian
scheme interfaces; finite dimension uses upstream
`AlgebraicGeometry.exists_topologicalKrullDim_le`. Semilinear localization and
StageSystemFunctorDescent provide the remaining prescribed proof route.

Edge cases checked: X and Y empty, zero objects, identity g, X distinct from Y,
non-k-linear isomorphisms, nonseparated finite-type schemes, E = Q_l, E = L,
ramified coefficient embeddings, quotient exponent 1 (tower index 0), torsion
integral arrows, sums of localized fractions, distinct common representatives and
larger common fields. No cohomological bound is imposed beyond the recorded integral
category. Universes of Ω and the scheme remain independent. The small finite-field
models already lift any finite subfield into the site universe.

Searches (all ran for this item):

- msearch leanfinder: "Scheme isomorphism exact inverse equivalences integral
  constructible derived sheaves raw scalar localization common finite coefficient fields".
  Eight hits, starting with `AlgebraicGeometry.IsFinite.instOfIsIsoScheme`; remaining
  hits concerned normalization, Spec, stalkwise isomorphisms or affine properties.
  No exact match.
- msearch loogle: `"mapDerivedCategory", "IsEquivalence"`: zero hits.
- msearch grep: `commonStageDerivedPullback|pullbackIdentityEpsilon|rationalDerivedPullback`
  in Mathlib/CategoryTheory: zero hits.
- msearch leansearch: "A scheme isomorphism induces exact inverse equivalences on
  constructible completed integral derived categories and rationalized common finite
  coefficient fields": eight hits about scheme isomorphisms, stalks, homeomorphisms
  and closed immersions; no match.
- rg in WeilConjectures for the item ID and `isomorphismFieldTransport`: zero hits.
  rg for the exact declaration in Mathlib and dag/lean_names_upstream.json: zero hits.
- rg in Sheaf found the recorded operation functors and normalized epsilon. These
  are used, not redefined. `AutomorphismConstructibleStageEquivalence` was read:
  its theorem assumes separatedness and an automorphism of one scheme, so is not
  this item. It is deliberately not imported. The node's reviewed note likewise
  identifies that specialization as unusable here.

No statement correction, disputed statement, new independent notion, dependency
repair, or node fault was needed. The old CompactObject example is now a withdrawn
module with no declarations; the current module/header conventions are followed
using the live neighboring statement modules.

Validation: scompile.py is the only compiler used. The repaired module passed
both sandbox and library module modes with no diagnostics. Self-check confirms
that the node differs from the current base only in `lean`, the original 12
statement dependencies are restored exactly, the recorded theorem signature is
verbatim, all Lean lines are within 100 columns, and the sole postponed proof is
the named theorem. Delivery preflight and compilation are run again by the wrapper.


## Repair of returned delivery

H2 (immutable head `514e94797d15`): removed the extra theorem node
`lem-pod-isomorphism-pullback-texact-coefficients` from `stmt_deps`, restoring
exactly the original 12 entries. It remains in `proof_deps`, and its module is now
an ordinary proof import. In `IsomorphismFieldTransportCommon.stage_shift`,
expanded the transparent predicate `isomorphismPullbackShiftSquare` to its body:
`@NatTrans.CommShift (stageComparison E).hom` with both
`Functor.CommShift.comp` instances explicit. The source composite uses the
specified inclusion shift and common pullback shift; the target composite uses
`(S E).rationalShift` and the specified inclusion shift. This is precisely the
returned review's second repair option. No new definition node is needed.

## Second reading by Q96

Read the node and module together after the H2 repair. All hypotheses and clauses
remain as matched individually above: finite-type schemes with no separatedness,
an underlying scheme isomorphism with no k-linearity, an independent universe for
Ω, the normalized completed maps, the integral and rational inverse comparisons,
scalar equations in both directions, and actual common-stage arrows and triangles.
The changed `stage_shift` is definitionally the old predicate's body, including its
four shift structures in their original order, so the triangle's last-arrow square
is unchanged. The generic shift-square wrapper was the only use of the theorem
module in a statement; removing it restores the original statement dependencies.
Checked identity field inclusions and identity isomorphisms: the same inclusion
shifts and chosen finite-stage shifts remain specified. No hypothesis, conclusion,
coefficient object or canonical map changed; the H2 dependency mismatch is repaired.
