## Worker report

The module `Sheaf.Paper.LisseTensorPullbackRealization` states
`WeilConjectures.LisseRealization.lisse_tensor_pullback_realization` with proof
`sorry`. The other declarations are transparent abbreviations, a composite of
specified arrows, and packages of the comparisons asserted by this same node.
There are no new independent notions, dependency repairs or statement corrections.
No comparison, flatness assertion, completion isomorphism or compatibility is an
extra hypothesis. They are fields of the conclusion. The argument `a` is the
normalized realization denoted J in the node, expressed using the recorded `At`
interface; the theorem applies to every such realization.

Clause-by-clause rendering:

* The global geometric datum is `D : FiniteFieldDatum.{u}`; `l : ℕ`, `[Fact
  l.Prime]`, `hl : l ≠ D.p` express the prime and characteristic exclusion.
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`
  are the finite coefficient extension. Its integer ring and uniformizer are
  the recorded `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`, used by the imported coefficient API.
  The embedding into an algebraic closure plays no role in these constructions;
  a finite extension is represented by its field and algebra structure.
* `X : Base D l hl` bundles a scheme, its structure over Spec D.k and finite type
  (locally finite type plus quasi-compact). It imposes no separatedness.
  Every `f : X.scheme ⟶ Y.scheme` is an arbitrary scheme map, with no `IsOver`
  condition. The node's X' is Lean X, and its X is Lean Y for pullback.
* The small site is `ProEt.topology X.scheme`, of object universe u+1 and
  morphism universe u. Modules retain universe u+1. No equality of these
  universes is imposed. `realizationOrdinaryTensor` uses the published site
  tensor with the existing standard derived localization universe u+2.
* B is `completedIntegralCommRingSheafUnrestricted l E X.scheme`. A is written
  using the continuous presentation `rationalCoefficientSheaf l X.scheme E`.
  This is exactly the recorded presentation: `a.completion_residues` identifies
  B by every quotient projection and `a.localization_unit` identifies its
  sheaf localization with A by the localization unit. The scalar map is the
  existing `LisseRealization.scalar`, completion followed by localization.
* The ordinary unbounded derived categories are the existing `DerivedCategory`
  of the existing module-sheaf categories, not categories of discrete constants
  or a replacement localization. Integral objects are
  `sfIntegralConstructibleCategory`; Q is `sfRationalConstructibleLocalization`;
  raw rational objects are `Raw`. F is `pbcDerivedExtend (scalar ... a)`.
  `a.integral` identifies Q followed by J with F on integral objects, and
  `a.fractions` gives precisely the scalar-tensor formula for morphisms.
* A lisse object is `Lisse`, the abbreviation for
  `rationalLisseHeartProperty`: `sfRationalHeartProperty` intersected with
  `IsRationalLisse`. Finite locally free is the existing
  `SheafOfModules.IsFiniteLocallyFree`, used in `At.image` and
  `PullNormalized.degree_zero`. These are cover-local definitions with finite
  rank zero and different ranks on different charts allowed.
* The completed integral tensor is `constructibleIntegralTensor`, with
  underlying `integralCompletedTensor`; its raw rationalization is `tensor`.
  `RealizationTensorComparison.comparison` is a natural isomorphism of
  bifunctors on ALL integral constructible pairs with the exact displayed
  endpoints F(completed tensor) and ordinary derived tensor(F,F).
  `raw` records the induced natural isomorphism on all raw objects, and
  `integral` requires it to be the conjugate of the same integral comparison
  by `a.integral`, rather than an independently chosen natural isomorphism.
* `RealizationTensorComparison.models` quantifies over every pair of integral
  objects and EVERY good K-flat representative with its identification.
  `RealizationTensorCalculation.model` is the recorded `TensorModel`: its
  `quotients` and `shifted` fix chi as pure quotient tensors and zero shifted
  component; `completed_normalized` fixes its derived completion map.
  `scalar_sections` is exactly c tensor (m tensor n) mapped to
  (1 tensor m) tensor (c tensor n), on all homogeneous local generators.
  The calculation's left/right comparisons are fixed by
  `pbcComplexCounit`, and `.arrow` explicitly composes F(completed inverse),
  the scalar counit, the scalar associator, the published ordinary tensor
  representative comparison and the two input identifications. The `models`
  equality fixes the displayed comparison to that composite.
* `unit_sections` fixes ordinary unit comparison to multiplication for every
  c,b; in particular 1 tensor 1 goes to 1. `derived_unit_normalized` identifies
  the derived unit comparison with precisely this multiplication through the
  universal scalar-extension counit and the canonical single-complex maps.
* `lisse : TensorAt ...` and `normalized : TensorNormalized ... lisse`
  retain the recorded all-good-model degree-zero cocycle normalization.
  `degree_zero` identifies the SAME raw comparison's derived-tensor target
  with ordinary sheaf tensor in degree zero and identifies its H^0 map with
  `lisse.tensor`. Thus this is not merely existence of a sheaf tensor iso.
* `RealizationPullComparison.comparison` is a natural isomorphism of functors
  on ALL raw rational inputs, with endpoints `pull ⋙ aX.J` and
  `aY.J ⋙ ContinuousRational.derivedPull f (coefficientPull l E f)`.
  The latter is the recorded ordinary derived module inverse image
  (inverse image followed by derived extension along the structural ring map).
* `normalized : PullNormalized ... lisse` retains all of the named dependency's
  normalization fields. Its `ordinary` and `sections` fix the scalar square
  on the actual ordinary adjunction unit, with scalar one. Its `derived`,
  `counit_normalized`, `derived_normalized` fix the same square on every
  complex by its universal derived counits. `integralCompletion_normalized`
  fixes the integral map to `ordinaryIntegralCompletionComparison`, and
  `normalized` explicitly composes the realization, its inverse, the scalar
  square and the inverse source realization, as required in the node.
  Our `integral` field makes the full raw natural comparison equal to that
  prescribed comparison on each integral representative.
* For lisse pullback, `PullNormalized.degree_zero_normalized` uses the SAME
  ordinary computation counit. `heart` requires the identification with the
  H^0 single to induce the identity on H^0, then identifies the comparison
  with `Along.comparison`. Along includes its naturality and ordinary balanced
  inverse-image description. Hence basis vectors have coefficient one by the
  prescribed eta quotient coordinates and ordinary adjunction-unit square.

Dependency declarations read and used:

* `Sheaf.Paper.LissePullbackNormalization`: `LisseRealization.PullNormalized`,
  including every ordinary, derived, integral-completion and heart field.
* `Sheaf.Paper.LisseTensorNormalization`: `scalar`, `rationalComplex`,
  `ordinaryTotal`, `Model`, `TensorModel`, `TensorNormalized`.
* `Sheaf.Paper.LisseRationalRealizationData` (publicly imported by the preceding
  modules): `Base`, `At`, `At.sheaf`, `TensorAt`, `Along`, `Raw`, `Lisse`,
  `Modules`, `tensor`, `pull`, `coefficientPull`, `ordinaryPull`.
* `Sheaf.Paper.RationalLocallyFree`: `IsRationalLisse`,
  `rationalLisseHeartProperty`; `Sheaf.Paper.SfConstructibleHeart`:
  `sfRationalHeartProperty` and its standard-class definition.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`; `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralTensor`,
  `rationalDerivedTensor`, `rationalDerivedPullback` and their normalized
  pure-tensor specifications; `Sheaf.Paper.IntegralDerivedOperations`:
  `integralCompletedTensor`, `integralCompletedTensorComparison`.
* `Sheaf.SixFunctors.ConstructibleTensorCompletion`:
  `constructibleTensorTotal`, `constructibleTensorBoundary`,
  `constructibleTensorTotalSection`, `constructibleTensorCompletion`.
* `Sheaf.Paper.OrdinaryCompletedIntegralPullback`:
  `ordinaryIntegralModulePull`, `ordinaryIntegralModuleAdjunction`,
  `ordinaryIntegralDerivedPull`, `ordinaryIntegralPullComplexCounit`,
  `ordinaryIntegralCompletionComparison`, `ordinaryCompletedIntegralPullback`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` reexports the recorded
  completed coefficient construction; its `integralConstantToCompletionOfUniverses`
  is the limit lift of the actual compatible quotient cone.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports the integer
  ring, uniformizer and quotient rings and states their positive-level finiteness.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is transparently Mathlib `SheafOfModules`; Mathlib
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
  `def-weil-scheme-morphism-properties` is a convention node: it owns no
  declaration; the relevant finite-type classes are those used by `Base`.
* `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`: the published tensor
  `siteDerivedTensorIndependentCoefficients` and normalized `representativeIso`.
  This does not define a second derived tensor.

The stated proof dependencies are imported privately, including the exact
ringed-topos tensor/pullback and scalar-composition interfaces, degree-zero
normalization, flat-single tensor, and finite-type dimension theorem.
`lem-tw-lisse-localization-restriction` currently has no Lean record, so no module
for it is invented or imported. It is a proof prerequisite, not a missing notion
of this statement. The theorem's docstring retains all eight DAG proof steps.

Edge cases: empty schemes and rank zero remain allowed by `Base` and local
finite freeness; no chosen rank or global lattice is an input. Local trivializing
charts need not be finite type: the theorem quantifies over good complexes on
its base, and the recorded lisse predicate handles arbitrary pro-etale charts.
No separation, k-linearity, connectedness or torsion-free integral cohomology
hypothesis is present. All good integral representatives are quantified, even
those with torsion cohomology. Identity morphisms are included by the arbitrary
scheme-map quantifier. All positive quotient exponents are represented by n+1
in the recorded completion API. Derived categories remain unbounded.

Searches for an existing statement:

* `msearch.py ... leanfinder "Localization realization of completed tensor and
  pullback for rational lisse sheaves"`: 8 hits, including
  `SheafOfModules.freeFunctorCompPullbackIso`, `pullbackObjFreeIso` and
  `pullbackIso`. These are ordinary free-module/pullback statements and do not
  assert either completed comparison or its specified normalization.
* `msearch.py ... loogle "Functor, NatIso"`: zero hits, unknown identifier
  NatIso. This search produced no purported mathematical match.
* `msearch.py ... grep "completed.*tensor|lisse.*realization"
  Algebra/Category/ModuleCat`: zero hits.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `lisse.*[Tt]ensor|[Tt]ensor.*[Rr]ealization|PullNormalized|TensorNormalized`:
  found the existing normalization definitions and unrelated lisse Weil tensor
  statements. None states this node. Searching the exact blueprint id upstream
  returned no hit. Searching `dag/lean_names_upstream.json` for the new public
  declaration names returned no collision.
* The nearby `Sheaf.Paper.RationalRealizationTensorComparison` was read: it uses
  a different composite finite-stage/PBC realization and a coefficient field
  indexed inside a specified algebraic closure; it packages tensor comparisons
  but not this arbitrary-morphism normalized lisse pullback assertion.

Source check: read Bhatt--Scholze pp. 61--62 (Proposition 6.8.14 and Remark
6.8.15) using pdftotext. Ordinary module pullback includes coefficient change;
no equality of pulled-back coefficients with target coefficients was assumed.
The latest blueprint dual-negation proof confirms this is realization
infrastructure below that statement, rather than a blueprint unit statement.
No statement dispute or correction was needed.

Validation: every compile uses the prescribed scompile.py wrapper. An initial
explicit localization universe u+1 was rejected because the live categories
use their standard u+2 localization. Using that existing universe repaired the
mismatch without a new hypothesis or a transport of mathematical objects.

## Second reading by Q27

A second clause-by-clause pass was performed by the same dispatcher worker;
the dispatcher explicitly prohibits starting other agents. This is not claimed
as an independent agent review; the maintainer's independent review remains.
Compared the node with the actual field signatures, not just the theorem name.
Checked the direction F(completed) to ordinary tensor, inverse completion order,
scalar formula orientation, naturality on full raw objects, all-good-model
quantifiers and pullback source/target convention. Added a derived unit field
with the universal counit formula so multiplication normalization is retained
in the derived category too. Checked that lisse degree-zero tensor refers to
the same raw comparison, and that raw pullback agrees with the specified
`PullNormalized.comparison` on integral representatives. No TeX statement was
changed. No new module or theorem claims to prove a DAG prerequisite.
