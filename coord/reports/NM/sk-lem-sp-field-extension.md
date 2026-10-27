## Worker report

Item: sk-lem-sp-field-extension. Module:
`Sheaf.Paper.SmoothPurityFieldExtension`; main declaration:
`WeilConjectures.SmoothPurityFieldExtension.fieldExtension`.
This is a statement-only delivery: the main theorem has `sorry`; the three
coordinate helpers have actual data and introduce no replacement coefficient
category, scalar extension, pullback, twist, or compact-support construction.
The node's mathematical statement and proof are unchanged.

### Hypotheses and clauses

* The global finite-field setting is `D : FiniteFieldDatum.{u}` and
  `C : D.CoefficientDatum`. These include the algebraic closure of the finite
  field, the prime `C.l`, `C.different : C.l ≠ D.p`, and a fixed algebraic closure
  `C.Qbar` of `Padic C.l`.
* `X Y : Scheme.{u}`, their `Over (Spec (.of D.k))` instances, and
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on their structural maps
  express separated finite-type k-schemes. `f.IsOver` expresses a k-morphism;
  the analogous three properties on `f` express separated finite type.
  `d : ℕ` and `[SmoothOfRelativeDimension d f]` express smoothness of pure
  relative dimension d ≥ 0. No nonemptiness, connectedness, properness or
  positivity of d is imposed.
* `AdicPurityScalarNaturality.Field D C` is the existing type of finite
  intermediate fields of `C.Qbar / Padic C.l`. `E F` and `h : E ≤ F` express
  exactly the stated inclusion; the underlying algebra homomorphism is
  `IntermediateField.inclusion h`. Neither proper inclusion nor Galoisness
  is assumed. The existing completed coefficient rings and their induced maps
  are used by the recorded scalar functor.
* `RCat D C E W` is definitionally the recorded raw
  `sfRationalConstructibleCategory C.l E.val W`. There is no Karoubi completion
  or common-stage Qbar category in the conclusion. Its objects retain the
  derived-complete integral constructible representatives.
* `T D C E F h W` is exactly `sfRationalScalarExtension` on these categories,
  with the actual inclusion of finite fields. It is the rationalization of
  completed integral scalar extension, not a derived tensor over a discrete
  constant non-torsion sheaf. The numerical parameter 0 is the coefficient
  construction's proof parameter; its nonzero proof is primality of ell,
  and it does not assert that the geometric characteristic is zero.
* `compactSupport D C f E` abbreviates the published
  `sfCompactSupportFiniteFunctor`, at the canonical compactification of f.
  `compactRealization` is `S.ring.rationalLeft` for that compactification,
  and `compactComparison` conjugates the actual compact-support scalar
  comparison `RationalScalarComparisonIdentification.c` by these specified
  realizations. Its signature is precisely the displayed b-isomorphism:
  `P_E ⋙ C^Y ≅ C^X ⋙ P_F`, so its component at M has the endpoints in the node.
* `H D C f d E` is the recorded `RationalSmoothPurityCanonical.rationalSource`:
  rational pullback and tensor with the Tate line of degree d, shifted by 2d.
  Its symmetric tensor coordinates canonically present `Lf_E^* K(d)[2d]`.
  `a E F h` has precisely the displayed a-isomorphism's endpoints.
  The component `HEq` pins it to the existing `sourceScalar` construction,
  rather than allowing an arbitrary automorphism of these endpoints.
* The normalized system `S`, integral purity family `I`, integral-to-rational
  source identification `qH`, and rational purity isomorphisms `γ` are all
  existential witnesses in the conclusion, not additional hypotheses.
  `I.finiteReductions` fixes integral purity by its finite-level purity roots;
  the normalized integral exceptional system has its strict-tower adjunction.
  `SourceLocalizationNormalization` fixes qH on actual good representatives.
  The equation `qH.hom ≫ γ = Q.map I.gamma ≫ gLocalization.hom` specifies the
  localized integral purity map. This is the alternate-right-adjoint
  realization of the tower adjunction described in the node's proof Step 1.
  It retains the normalization from det-sp-integral-adjunction-bijection.
* The local `let adj` is a real construction from `(O ...).adjunction`:
  transport its left adjoint along `compactRealization`, then transport its
  right adjoint along `γ.symm`. Thus these are the scalar-localized integral
  adjunctions with purity, not an independently chosen adjunction. The first
  displayed equation after the let is unit preservation, for every M in the
  full raw rational category. The next equation is counit preservation, for
  every K. The component orders are respectively
  `C^X(η_E) ≫ a(P_E M) ≫ H_F(b_M) = η_F` and
  `b(H_E K) ≫ P_F(a_K) ≫ ε_F = C^Y(ε_E)`.
* The two `UnitEquation` clauses retain the identity-field normalization.
  The two `CompositionEquation` clauses express the E⊂F⊂L cocycles of a and b.
  `alpha` is the existing `sfRationalScalarComp` of
  lem-weil-scalar-extension-composition. Its X,Y order is reversed in the
  compact-support clause because compact supports go from X to Y. Each clause
  quantifies all three fields and both inclusion proofs, including equalities.

### Dependency declarations used

* `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`,
  and its imported `FiniteFieldDatum` / `FiniteFieldDatum.CoefficientDatum`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension`; scheme properties are
  Mathlib `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsOver`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, and the recorded valuation rings.
* `Sheaf.Paper.SfIntegralConstructible`, `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
* `Sheaf.Paper.SfRationalizationKaroubi`,
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`,
  `sfRationalScalarExtension`.
* `Sheaf.Paper.QcqsCompactSupportRealization`,
  `sfQcqsCompactSupportRealization` and `sfCompactSupportFiniteFunctor`.
* `Sheaf.Paper.DerivedPullbackTensorHom`, `rationalDerivedPullback` and
  `rationalDerivedTensor`, through the canonical source functor.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`,
  `sfRationalTwistingCoefficient`, through that same source.
* `Sheaf.Paper.IntegralAdjunctionBijection`,
  `AlgebraicGeometry.ProEtale.SpIntegralAdjunction.integral_adjunction_bijection`:
  the normalized tower realization whose alternate-model purity/adjunction
  is retained in the source and exceptional system.
* `Sheaf.Paper.SfScalarExtensionComposition`, `sfRationalScalarComp` and
  `sfRationalScalarUnit`.
* The definition node `def-pur-adic-purity-scalar-naturality-data`, module
  `Sheaf.Paper.AdicPurityScalarNaturalityData`, owns `Field`, `Cat`,
  `fieldStage`, `source`, `Data` and the finite-root-normalized integral
  purity data used in the statement. No existence theorem from
  `Sheaf.Paper.AdicPurityScalarNaturality` is used as a statement dependency.
* `Sheaf.Paper.PuritySourceTransports`,
  `WeilConjectures.RationalSmoothPurityCanonical.rationalSource` and `sourceScalar`.
* The definition node `def-pur-rational-scalar-comparison-data`, module
  `Sheaf.Paper.RationalScalarComparisonData`, owns `RCat`, `Q`, `H`, `O`,
  `G`, `T`, `c`, `gLocalization`, `alpha`, `unit`,
  `SourceLocalizationNormalization`, `CompositionEquation`, `UnitEquation`.
  These are plain definitions; the comparison-identification theorem
  is not used as a statement dependency.
* The stated proof dependency
  `Sheaf.CategoryTheory.PurityConjugatedCoefficientAdjunction`,
  `CategoryTheory.purity_conjugated_coefficient_adjunction`, is a plain import.
  The other three proof-only prerequisite nodes currently have no Lean record.
  The integral-adjunction dependency is already a public statement import.

The three landed definition nodes appended to stmt_deps are
`def-pur-adic-purity-scalar-naturality-data`,
`def-pur-rational-scalar-comparison-data`, and
`def-pur-canonical-purity-source-transports`.
A traversal of both statement and proof dependency edges found no path from
any of these added dependencies back to this item. No missing notion, new
node, dependency-module repair, or mathematical statement correction is needed.

### Edge cases checked

* E=F, F=L and E=F=L remain included; the unitor equations and canonical
  associator cocycles typecheck without strict-inclusion assumptions.
* d=0 is allowed, yielding twist 0 and shift 0, without requiring a selected
  trivialization of the Tate line. No dimension or sign convention is changed.
* Empty X or Y are not excluded. All components are quantified in the full
  categories, without selecting generators or assuming nonzero objects.
* Morphisms in the raw rational category may have denominators. The natural
  isomorphisms and adjunction equations are quantified on that full category,
  rather than only on integral arrows or stalk cohomology groups.
* No torsion-free, lisse, perfect, proper or boundedness hypothesis beyond
  the recorded constructible category and the geometric hypotheses was added.
* The current blueprint's section and proof were read from
  `literature/blueprint/latest/`; its intended tensor is represented by the
  normalized completed/localized scalar functor specified by the DAG node.

### Searches

* msearch LeanFinder: `Finite l-adic coefficient field extension preserves smooth
  purity adjunction units counits and composes with scalar extension`.
  Eight results concerning integral closure, period rings, or generic scalar
  extension; no theorem with the geometric statement.
* msearch Loogle: `CategoryTheory.Adjunction.localization`.
  Generic localization theorem and unit/counit component formulas; these do
  not identify the smooth-purity functors or their coefficient comparisons.
* msearch grep: `smoothPurity|purityIso|lowerShriek`, AlgebraicGeometry.
  No hits.
* msearch LeanSearch: `finite coefficient field extension smooth purity
  adjunction compact support unit counit`. Eight generic module/representation
  and unit/counit results, no exact geometric statement.
* rg of the item id and purity/scalar-extension terms in `lean/WeilConjectures`
  and `lean/Sheaf`: no existing declaration for this item. Existing scalar,
  source-localization and coefficient-comparison interfaces were read and reused.
* rg for `SmoothPurityFieldExtension|fieldExtension` in the upstream name table,
  Mathlib AlgebraicGeometry and WeilConjectures found geometric base-field
  extensions, not this coefficient-field comparison or a namespace conflict.

No STATEMENT-DISPUTED issue or source fault was found.

## Second reading by NM

The dispatcher explicitly forbids starting another agent and states that the
maintainer performs the independent review. Accordingly this section records
an additional self-reading, not a claim of independent worker review.

I checked both displayed arrows, the directions of all realization transports,
the component order in both adjunction equations, and the X/Y reversal in the
compact-support cocycle against the node and current blueprint. The initial
compiler pass exposed only interface-elaboration issues (opaque coordinates,
qualified whiskering names and reducibility attributes), which were repaired.
No mathematical clause or hypothesis was altered. The normalized source
identification and localized integral purity equation remain explicit, so
there is no arbitrary-adjunction or arbitrary-purity-map replacement.


## Returned-delivery repair: H2

The maintainer reviewed immutable head `7d8845ead9a7` and accepted the
mathematics, returning the ownership of two statement dependencies. Replaced
`lem-pur-rational-scalar-comparison-identification` and
`lem-pur-adic-purity-scalar-naturality` in stmt_deps with the owning definition
nodes `def-pur-rational-scalar-comparison-data` and
`def-pur-adic-purity-scalar-naturality-data`. Replaced the public import of
`Sheaf.Paper.RationalScalarComparisonIdentification` with public imports of
`Sheaf.Paper.RationalScalarComparisonData` and
`Sheaf.Paper.AdicPurityScalarNaturalityData`. Updated the dependency inventory
above accordingly. The theorem signature, helpers, proof placeholder,
normalizations, and mathematical node statement are unchanged.

Compared the retained node with the current shared main node: the original
statement, original dependencies, proof, and other node fields are preserved;
the delivery supplies only the Lean record and the three owning definition
dependencies. The current owning nodes record these exact data modules.
The only return point is H2; the other comments are advisories.

Repair validation: scompile.py passed the repaired file in sandbox mode
(39.4 s) and library mode (32.8 s), with no diagnostics. The exact recorded
signature still matches the file, which retains its single stage-2 sorry.
