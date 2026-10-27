## Worker report

This delivery states `lem-sf-exceptional-field-descent` in
`Sheaf.Paper.ExceptionalFieldDescent`. The helper records package this node's
input and conclusions; they do not introduce replacement coefficient categories.
`IntegralInput` contains only integral adjunction data. `RationalOutput`,
`CommonStageData`, and `CommonOutput` are existential outputs. There is exactly
one postponed theorem, `WeilConjectures.ExceptionalFieldDescent.exists_field_descent`.
All definitions and structures have actual data, with no hidden sorry.

### Hypotheses and conclusions

- `D : FiniteFieldDatum`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give the
  finite-field datum and the prime distinct from its characteristic.
- `FieldStage l` is the existing finite extension of `Padic l`, with its field,
  algebra, and finite-dimensional structures. Valuation rings and uniformizers
  are `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`. Quotients are already built into the
  published completed category and compact-support reduction comparisons, with
  exponent `n+1` for `n : ℕ`, so the zero quotient is never used.
- The `Over`, `LocallyOfFiniteType`, and `QuasiCompact` binders make `X,Y`
  finite-type schemes over `D.k`. `f.IsOver`, `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f` give exactly the indicated
  morphism. Neither absolute structure morphism is required to be separated.
  `c : Compactification f` fixes the compactification.
- `Ω : Type v` with `Field`, `Algebra (Padic l)`, and `IsAlgClosure` is the
  chosen closure. Its universe is independent of the scheme/finite-coefficient
  universe `u`. `coefficientField` uses the published small coefficient model
  for every finite subfield, rather than equating `u` and `v`.
- `IntegralInput.G`, `.adjunction`, `.leftLinear`, `.rightLinear`, additive
  structures, shifts, exactness, and unit/counit shift equations package the
  supplied exact linear integral adjunction. The left functor is normalized
  through its prescribed compact-support identification, exactly as node proof
  step 3 explicitly permits. It is the actual
  `sfCompactSupportFiniteIntegralFunctor`. Thus no arbitrary left realization
  or rational adjunction is an assumption.
- `.qCanonical` is `SfCompactSupportIntegralBetaSpec`: the actual proper/open
  tensor-unit mate at every reduction, including the prescribed Roos comparison.
  `.counit` makes `.b` its counit transpose; `.b` is an isomorphism. `.identity`
  and `.composition` are precisely the balanced left scalar equations with
  `sfIntegralScalarUnit` and `sfIntegralScalarComp`. Right coherence is not an
  input. `.qShift` and `.bShift` retain compatibility with the specified shifts.
- The first theorem conjunct gives equality of the published integral
  constructibility and finite-Tor predicates for both `X` and `Y`, and every
  coefficient field. This also supplies the canonical transport from the
  finite-Tor input domain to the entire integral domain; it adds no hypothesis.
- `RationalOutput.G` and `.adjunction` give the localized right functors and
  adjunctions on the literal `sfRationalConstructibleCategory` carriers.
  The left functor is literally `sfCompactSupportFiniteFunctor`, whose map
  is the raw Hom scalar extension of the prescribed integral action; hence its
  rational-left realization is identity. The additive, exact, and shift fields
  give their indicated structures.
- `.rightObjects` and `.rightTensors` fix localization of the right action.
  The tensor scalar ranges over all `Localization.Away` elements, including
  every uniformizer denominator. Additivity extends the tensor formula to all
  morphisms. `.unit`, `.counit`, `.hom`, and `.homInverse` specify the images
  of the integral unit, counit, and both inverse Hom maps. The two triangle
  identities are fields of `Adjunction`, for these very units and counits.
- `.localizationLeft`, `.localizationRight` and their identity-component,
  shift, and counit fields give the integral-to-rational comparisons. In the
  normalized input presentation the left realization is identity, so its
  required composite is exactly the localization of the integral realization.
- `.q`, `.b`, `.qLocalized`, `.bLocalized`, `.counitSquare`, `.qShift`,
  `.bShift`, `.identityLeft`, `.identityRight`, `.compositionLeft`, and
  `.compositionRight` give the rational scalar isomorphisms, their precise
  integral images, counit equation, shifts, balanced identity and composition.
  The scalar functors themselves are the existing semilinear raw localizations;
  their naturality applies also to fractions. The scalar shift normalizations
  are the integral-image normalization used in the published coefficient stages.
- `CommonStageData.leftSystem` and `.rightSystem` are morphisms of the actual
  `GeneralAlgebraicallyClosedCoefficients.stageSystem`s. `.leftStages` and
  `.rightStages` fix their finite functors to the rational functors just
  constructed; `.leftComparisons` and `.rightComparisons` fix their betas to
  the corresponding rational scalar maps. These are whole-functor and
  whole-isomorphism `HEq`s; they retain all components and avoid unfolding
  the small coefficient field's category structures. `.stageAdjunction_eq`,
  `.leftStageShift_eq`, and `.rightStageShift_eq` transport exactly the same
  rational adjunction and shifts to the stage systems. The existing `Morphism.functor`
  sends a pair to the pair at the same field and a represented arrow to
  `beta; finiteFunctor.map h; beta inverse`. Its quotient construction gives
  independence of representatives/enlargement, addition, identity and composition.
- `CommonOutput.adjunction`, additive/exact/shift fields, `.unit`, `.counit`,
  and `.hom` give the common-field adjunction with its finite-stage Hom recipe,
  represented unit/counit, triangle identities, and induced shifts. Every pair
  lies in a stage; every finite diagram of arrows has a common-stage
  representative, so the same-stage `.hom` formula specifies both Hom maps on
  arbitrary pairs and their enlargement compatibility. Its inverse is the
  inverse of this equivalence (equivalently the represented counit recipe).
- `.q`, `.b`, `.qIdentity`, `.bIdentity`, `.qShift`, `.bShift`, and
  `.counitSquare` give both finite-field-inclusion comparisons, identity on
  represented objects, with the same counit and shift equations. The published
  common-stage distinguished triangles give the represented triangles used by
  the exactness assertions. No completion or ambient closure adjunction occurs.

### Dependencies and source checks

Read the full recorded dependency signatures and docstrings. The declarations
used are `FiniteFieldDatum` (`Sheaf.Paper.FiniteFieldFiber`);
`Padic.finite_coefficientExtensionRing` and the coefficient ring/valuation-ring
constructions (`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`);
Mathlib's scheme/morphism properties; `Compactification` and its refinement
category (`WeilConjectures.Compactification.RefinementCategory`);
`sfRationalConstructibleCategory`, localization, scalar unit and associator
(`Sheaf.Paper.SfRationalizationKaroubi`);
`GeneralAlgebraicallyClosedCoefficients`' published `Stage`, `Pair`,
`stageSystem`, `inclusion`, coefficient models and normalized shifts
(`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`);
`sfQcqsCompactSupportRealization` (`Sheaf.Paper.QcqsCompactSupportRealization`);
`sfCompactSupportFiniteIntegralFunctor` and `sfCompactSupportFiniteFunctor`
(`Sheaf.Paper.CompactSupportFiniteAction`); `SfCompactSupportIntegralBetaSpec`
(`Sheaf.Paper.CompactSupportCoefficientAction`); and existing `FieldStage`
(`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData`).

Three already-landed definition owners were added to `stmt_deps`, as permitted
by brief-stage2 §5: `def-weil-compact-support-finite-action`,
`def-weil-compact-support-coefficient-action`, and
`def-sf-constructible-exceptional-coefficient-construction-data`. No existing
node was restated or repaired. A dependency graph read confirmed none of these
additions has a dependency path back to this item.

The proof imports retain `integral_residue_tor`, semilinear scalar localization,
`Adjunction.mkOfHomEquiv`, Mathlib adjunction mates, coherent pair-functor descent,
and `PbcScalarExtension`, according to the nine node proof steps. Their imports
are plain proof imports; statement constructions have public imports.

Read Zheng, Propositions 2.23, 2.29, 3.16, Lemma 5.22 and Proposition 5.24
from the local PDF. Read the current blueprint's exceptional-inverse-image
page under `literature/blueprint/latest/`. The newest page defines the integral
adjoint by Brown representability and identifies its restriction by uniqueness;
this node's accepted statement is the separate conditional localization and
pair-descent assertion for the supplied integral adjunction. It is unchanged.
The original construction obligations retained by the split are reproduced below.

### Edge cases

Checked empty schemes and zero objects (no nonemptiness of a scheme or an
object is imposed); unbounded locations of bounded cohomological intervals;
positive quotient exponents, including the residue quotient at index zero;
identity embeddings and repeated fields in every balanced unit/composition
formula; ramified embeddings, where the image of a uniformizer is a unit times
a positive power; non-separated `X,Y` with separated `f`; all integral
representatives rather than an arbitrarily smaller finite-Tor rational category;
arbitrary independent closure universe; and pairs with different coefficient
fields (the existing quotient functor and common-stage Hom formula apply after
a common enlargement). Only invertibility of `ell` on the finite-field base is
used to invoke the residue-Tor result. No zero coefficient ring or denominator
zero is introduced.

### Searches actually run in this worker session

- `msearch.py ... leanfinder "Localize an integral linear adjunction then descend
  it to the common finite coefficient field constructible category"`: eight
  unrelated ring/localization hits, including `Algebra.EssFiniteType.cond`;
  no matching constructible-category statement.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.Linear"`:
  `CategoryTheory.Adjunction.extLinearEquiv`, about Ext, not this assertion.
- `msearch.py ... grep
  "exceptionalFieldDescent|IntegralExceptionalField|FieldDescent" CategoryTheory`:
  zero hits.
- `msearch.py ... leansearch "Localization of linear adjunctions and coherent
  functors on a common finite field category"`: eight generic results including
  `CategoryTheory.Adjunction.localization` and derived-adjunction variants;
  none includes these geometric categories and prescribed comparisons.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `ExceptionalField|exceptionalField|exceptional-field-descent|field descent`,
  and for `exists_field_descent|IntegralInput|RationalOutput`: no exact existing
  theorem. The latter found only unrelated pairing integral-input data.
  The item-id search in `lean/WeilConjectures` had no hits.
- Searched `dag/nodes` and the project for the coefficient-construction,
  scalar-extension and compact-support notions. Reused the existing interfaces.
  In particular the old `RingSystem` includes rational and closed operations,
  so it cannot be used as an integral-only hypothesis: the new input record
  deliberately contains none of those conclusions.

No new independent notion, dependency-module repair, statement correction,
STATEMENT-DISPUTED flag, or node fault is asserted. The only changed node fields
are `lean` and the authorized additions of landed definition owners to `stmt_deps`.

### Validation

The final module compiled through the prescribed `scompile.py` wrapper, both as
`Sheaf.Stage2.Sandbox0` (51.4 s) and as its library module (26.7 s), with no
errors or warnings. The file contains one `sorry`, the main theorem's proof.
No diagnostic declarations or probe modules remain in the delivery.

## Second reading by Q46

The dispatcher explicitly prohibits spawning another worker; independent
maintainer review follows delivery. This section records Q46's separate reread,
not a claim of an independent second agent. It caught the initial draft's use
of `RingSystem` as an input: that record already contained rational and closed
operations. That draft was replaced before delivery. The reread also removed
arbitrary integral scalar shift choices in favor of the published normalized
ones, retained explicit rational scalar-shift localization, checked both
inverse Hom formulas and all denominator scalars, and kept closure/scheme
universes independent. The final clause-by-clause mapping is above.

## Retained construction steps 17–19

Old step 17: By the residue-Tor theorem every integral constructible representative belongs to the integral finite-Tor category. Localize the $R_E$-linear operations, natural transformations and adjunction Hom bijections at $\varpi_E$. The inverse localized Hom maps remain inverse because localization preserves the equations for their composites; the resulting unit, counit and triangles are their images. Raw scalar localization has the same objects and localized Hom modules, with exact localization functor. Hence the localized adjunction acts on exactly the published rational categories, and its operations and coefficient maps are exact with the induced shifts. Choose its left functor to be the published rational compact support and its rationalLeft realization to be the identity identification. This does not require a Karoubi completion.

Cited nodes: lem-coef-integral-residue-tor, def-weil-rationalization-karoubi, lem-weil-linear-scalar-localization-triangulated, lem-weil-pbc-adjunction-of-natural-bijection, def-weil-integral-rational-qbar-compact-support.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Raw rational localization of the integral adjunction; blueprint coefficient construction."}

Old step 18: For integral-to-rational comparison take $q$ to be the localization of integralLeft followed by the inverse of rationalLeft. Take $b$ to be the identity comparison on the localized integral-right object, transported along those choices. The counit equation is the image of the integral one, so it has the required transpose normalization. For a rational embedding $E\to L$, define $q,b$ by localizing their integral versions on the same object representatives. On a morphism $h/\varpi_E^r$ use its localized image; the integral maps are linear and natural, so this is independent of representatives and natural. This gives exactly rationalization_normalized and rational_normalized: the left maps are the raw images of the indicated integral maps. The scalar-extension theorem and localized derived structures give the required endpoint shifts, and the comparisons preserve them.

Cited nodes: def-weil-rationalization-karoubi, lem-weil-scalar-extension-exact-triangulated, lem-weil-pbc-commshift-nattrans-comp-whisker.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Rationalization and rational coefficient comparisons, on the prescribed integral representatives."}

Old step 19: Define the closed-stage operations on a pair $(E,K)$ by $(E,F_EK)$ and $(E,G_EK)$. For a map represented over $L$ use its image under $F_L$ or $G_L$, conjugated by the scalar comparisons. The left transition identities follow from canonical tensor associativity and proper/open mate pasting of Step 16. For the right transitions, take the inverse transposes of the two composites: substitution of the counit equations reduces equality to the left transition identity. Injectivity gives equality. Therefore passage to a larger common field preserves these represented maps, composition and identities. Likewise the Hom bijections commute with transition maps, so inverse natural bijections pass to the directed colimit defining the closed coefficient category. Use them for the adjunction. Distinguished triangles and shifts are represented over one finite field, which gives exactness. On the inclusion of a finite common field take $q$ to be the identity on $(E,F_EK)$; take $b$ to be its counit transpose. This is the identity on $(E,G_E L)$ by the finite-field adjunction. These choices give common_normalized and the required shifts.

Cited nodes: def-weil-algebraically-closed-coefficients, lem-weil-scalar-extension-composition, lem-weil-pbc-mate-pasting, lem-weil-pbc-adjunction-of-natural-bijection.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Common finite-field construction and third Hom bijection of sk-thm-sf-tensor-hom."}

