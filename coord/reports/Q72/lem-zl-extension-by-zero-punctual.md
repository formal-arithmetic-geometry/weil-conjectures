## Worker report

This delivery states `WeilConjectures.extensionByZero_punctual` in
`Sheaf.Paper.ExtensionByZeroPunctual`. Every theorem has proof `sorry`; definitions
contain actual functor, coefficient-map, fixed-pair, and eigenvalue data. The
extension functor is selected as the left adjoint of the existing canonical Weil
restriction, so the selection determines it up to the unique adjunction comparison.
It is not an arbitrary functor with prescribed object values.

The source read was main-20261015,
`sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md`,
parts (1) and (2). The weight definition was also read in its actual blueprint file,
`sec-algebraic-groups-lie-algebras/sk-p-readout/def-weil-punctual-weights.md`.
The item's statement is unchanged. No statement dispute or correction is needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed finite-field datum, including k₀, k, q and characteristic | `D : FiniteFieldDatum.{u}`; the existing structure retains all its field, cardinality and algebraic-closure data. |
| Prime ℓ different from the characteristic | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`. |
| Fixed algebraic closure of Qℓ and iota | `Qbar : Type v`, `Field`, `Algebra (Padic l)`, `IsAlgClosure`, and `iota : Qbar ≃+* ℂ`; no equality between v and u. |
| Separated finite-type k₀-schemes | `U₀ X₀ : Over (Spec (.of D.k₀))`, with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on both structure morphisms. Separatedness is explicitly included in the main theorem and adjoint existence theorem. |
| Open immersion over k₀ and its base change | `(j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]`; `zlFiberMap D j₀` is exactly the existing `Over.pullback` map. Quasi-compactness is derived, not assumed. |
| Constructible Qbar-Weil sheaves | `sfCommonStageWeilSheaf D l hl U₀ Qbar` and its X₀ counterpart, the recorded full heart-carrier subcategories of fixed pairs. |
| The rational/common-stage compact-support functor gives this extension | The fourth conjunct compares the carrier with `sfQbarCompactSupportValue` of the given integral representative and the compactification `(j,id)`; the finite-stage clause supplies a natural comparison with `sfCompactSupportFiniteFunctor`, including arrows. |
| Sends sheaves to sheaves | `zlOpenWeilShriek` has the actual two constructible Weil hearts as source and target. Its adjoint-existence statement is one of the named postponed theorem clauses of this item. |
| Exactness | `Additive`, `PreservesFiniteLimits`, and `PreservesFiniteColimits` of that same functor. In an abelian heart this is precisely exactness. |
| The actual adic coefficient fibres | The existential families FU and FX satisfy `SfAdicCommonFiberSpec`, whose finite-stage functors are uniquely the rationalizations of completed geometric pullback, H⁰, final-object sections, and inversion of the uniformizer. The stage comparison includes the actual inclusion of the small finite coefficient model into Qbar. |
| Every geometric point in the open | For every algebraically closed Ω and `x : Spec Ω ⟶ U`, a natural isomorphism compares `j!` followed by the target fibre at `x ≫ j` with the source fibre at x. Any target geometric point in the open has this unique factorization. Ω is not required to be algebraic over the base or lie over a closed point. |
| Every geometric point outside the open | `Set.range x.base ⊆ (Set.range j.base)ᶜ` implies `IsZero` of the coefficient **module object**, for every input sheaf. |
| Local geometric Frobenius at a closed point in U₀ | At each finite coefficient stage L the theorem supplies J and a **natural** isomorphism `e` of `zlClosedCoefficientFiber` functors. The displayed equation says `F_X ≫ e = e ≫ F_U`, using `localClosedFrobeniusCohomology ... 0` on both sides. The point and residue-field compatibility hypotheses select precisely the corresponding closed points and geometric lifts. |
| Same finite/common-stage Weil action | The natural isomorphism `zlWeilHeartStage U₀ L ⋙ j! ≅ J ⋙ zlWeilHeartStage X₀ L` includes the Weil structures and all arrows. The stage functor bundles the already recorded stage pullback comparison, not a new Frobenius action. |
| All real punctual upper bounds | `∀ w : ℝ`, `ZlPunctualUpperBound ... F w → ZlPunctualUpperBound ... (j!F) w`. The predicate is the explicitly requested eigenvalue inequality, and has no mixed-filtration premise. |
| All real punctual pure weights | `∀ w : ℝ`, `SfIsPunctuallyPureOfWeight ... F w → SfIsPunctuallyPureOfWeight ... (j!F) w`, using the dependency repair below. |
| Correct q_x | Both weight predicates use `(Nat.card (X₀.left.residueField x.val) : ℝ) ^ (w / 2)`. |

The finite-stage local-fibre formulation expresses the local action on the actual
rational point complex, and its common-stage natural comparison transports that
action to Qbar. It neither asserts Frobenius at an arbitrary nonclosed geometric
point nor drops the separate fibre formula at those points.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `.geometricFiber`, and its coefficient conventions.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
  The morphism-property convention node has no declaration of its own; its named
  Mathlib finite-type, quasi-compact and separated classes are used directly.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeartProperty`,
  `sfCommonStageHeartProperty` and their full hearts.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilSheaf`,
  `sfCommonStageWeilSheaf`, their forgetful and Frobenius pullback functors,
  `sfWeilStageObject`, and `sfWeilStagePullbackIdentification`.
- `Sheaf.Paper.QcqsCompactSupportRealization` and its public imports:
  `sfQbarCompactSupportValue` and `sfCompactSupportFiniteFunctor`, retaining
  the recorded completed-tower integral, rational and common-stage construction.
- `Sheaf.Paper.AdicHeartPullbackFibres`: `PerAdic.adicHeartPullbackFibres`,
  `PerAdic.pointSections`, `PerAdic.integerToField`, the full original rational,
  scalar and common-stage assertion predicates, and their fibre normalizations.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localClosedPoint`,
  `localClosedFrobeniusCohomology`, `localPointComplex`, and the underlying point
  transport and pullback comparisons. These are geometric Frobenius operators.
- The unusable old weight signatures were read in
  `WeilConjectures.DeligneLaumon.Reduction.Weights` and
  `WeilConjectures.WeilSheaf.Stalk`. They take the older `WeilSheaf` category;
  the dependency module below repairs the interface for the recorded heart.
- Three already-landed nodes are added to the item's statement dependencies:
  `def-zl-weil-ind-sheaf-category` provides the actual `zlWeilPull`,
  `zlFiberMap`, and the abelian common-stage Weil heart;
  `def-zl-weil-compact-support-cohomology` provides the existing geometric-fibre
  structure-map instances and `zlClosurePrimeUnit`;
  `def-pur-completed-coefficient-presentation-transport` provides
  `purCoefficientModel`, the actual normalized coefficient-presentation equivalence.
  Their modules are `Sheaf.Paper.WeilIndSheafCategory`,
  `Sheaf.Paper.WeilCompactSupportCohomology`, and
  `Sheaf.Paper.CompletedCoefficientPresentationTransport` respectively.

Proof-only imports include each recorded proof-dependency module that is available:
`LocalizedModuleExactIndependent`, `SfIntegralCompactSupportConstructible`,
`SfConstructibleHeart`, upstream `LowerShriekFunctoriality`,
`CompletedOpenExchangeTransport`, `ProEtaleExtensionZero`, and `FrobeniusOpenSquare`.
The geometric-base-change/noetherian/closed-complement nodes,
`lem-sf-integral-open-reduction-comparison`, and
`lem-dl-a1-constructible-fibres-exact` have no recorded modules and supply no
additional import. Their uses remain explicit in the theorem proof docstring.

Edge cases checked against the signatures and source:

- Empty open immersion and empty target: no nonemptiness or density assumption.
  Outside fibres are zero and the inside comparisons have no points to test.
- Identity immersion: inside fibres and their Frobenius comparisons apply everywhere.
- Zero sheaf and zero-dimensional fibre: `HasEigenvalue` is false on the zero
  vector space, making purity and upper bounds vacuous, exactly as in the source.
- Every real w, including zero and negative values, remains quantified.
- Nonsemisimple Frobenius is allowed. Eigenvalues are taken after extension to Qbar,
  rather than only testing eigenvalues belonging to the finite field of definition.
- All closed points, every compatible residue embedding and geometric lift, and all
  geometric Ω-points are retained. No degree-one or rational-point restriction.
- The mixedness repair permits m = 0 and nonstrict filtration inclusions.
- Site universe u and coefficient closure universe v are independent. Fibre modules
  have carrier universe `max (u + 1) v`, preserving the small-site size convention.

Searches made before drafting, through the prescribed msearch wrapper:

- LeanFinder: `extension by zero of constructible Weil sheaves is exact with identical
  stalk Frobenius and preserves punctual weights`. Eight unrelated hits about
  condensed modules and exactness, including `Profinite.NobelingProof.succ_exact`;
  no exact theorem on these coefficient categories.
- Loogle: `CategoryTheory.ShortComplex.ShortExact,
  AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`. Zero hits; the latter name
  is unknown to the Mathlib search service. Its upstream declaration was separately
  opened and is the incompatible category described above.
- Mathlib grep: `extension.by.zero|punctually|lowerShriek`. One hit in
  `Mathlib/NumberTheory/MulChar/Basic.lean`, unrelated to sheaves.
- LeanSearch: `extension by zero of an adic constructible Weil sheaf is exact and
  preserves punctual weights`. Eight unrelated adic-completion, Ext and
  function-extension hits; no match.
- Direct rg of `WeilConjectures` and `lean/Sheaf` for extension-by-zero, lower-shriek,
  punctual weight and common-stage names located the recorded interfaces above.
  The exact item-id search in upstream `WeilConjectures` returned no hit. Direct
  name searches in Mathlib, upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found none of the new declaration names.

Validation: the final three-module `scompile.py` run passed with no errors or
unexpected warnings. The prescribed `deliver2.py --no-push` then printed
`OK (dry run): commit 2403d2a40c passes the preflight and compiles; nothing pushed`.
All three delivered files were compiled separately in dependency order.

## Dependency modules

`lem-per-adic-heart-pullback-fibres`: `Sheaf.Paper.AdicHeartIntrinsicFibres`
reexports the original module, retaining its raw coefficient categories and complete
assertion package. The new primary theorem repeats all twelve original conjuncts
and supplies the same coefficient fibres in the intrinsic presentation. The module
constructs the integral fibre with the **existing** `purCoefficientModel.inverse`,
completed point pullback, H⁰, final-object sections, and actual fraction-field tensor.
A unique localization extension defines the rational fibre. The common-stage
normalization compares its restriction to each actual finite-stage inclusion with
that rational fibre followed by scalar extension to Qbar. Thus this is an interface
transport, not replacement by a free fibre functor or a discrete non-torsion sheaf.
Only the node's lean field is changed.

`def-weil-punctual-weights`: `Sheaf.Paper.AdicPunctualWeights` gives the node's
purity and finite-filtration mixedness definitions on the currently recorded
`sfCommonStageWeilSheaf`. `SfPunctualEigenvalue` computes the recorded finite-stage
local closed-point operator, extends that linear map to Qbar along the actual
coefficient inclusion, and uses Mathlib `Module.End.HasEigenvalue`. It quantifies
finite-stage presentations and residue embeddings; their spectra agree by the
recorded conjugacy and coefficient conventions. Purity is the precise norm equality
at every closed point. Mixedness is a finite chain of monos with zero initial term,
last term isomorphic to F, and pure cokernels of weights ≤ w. Only this dependency's
lean field changes. No new DAG definition is needed: both notions already belong
to these two existing nodes.

## Second reading by Q72

This is a separate pass through the final node text and the drafted signatures by
the single dispatcher worker; no second worker was launched, as instructed. The
maintainer's independent review remains the independent reading for this delivery.

The pass checked every row of the hypothesis/clause table above against the actual
signatures. It caught and repaired: (1) section typeclasses for separatedness could
otherwise be omitted by Lean's binder collection, so they are explicitly included
for the adjoint and main theorem; (2) same-stage object isomorphisms were insufficient
for coefficient functor compatibility, so the final formulation uses a natural
isomorphism of stage-inclusion functors; (3) testing finite-field eigenvalues alone
would miss eigenvalues in a larger field, so the actual linear map is first extended
to Qbar; (4) the common-stage weight predicate must use the actual fixed-pair heart,
not the older upstream sheaf category. The dependency repairs cover both purity and
mixedness, and preserve the full original adic-heart assertion package.

The inside stalk assertion is a natural isomorphism, the outside assertion is zero
in ModuleCat, and the finite-stage natural isomorphism explicitly conjugates the
recorded geometric-Frobenius operators. The compact-support comparison refers to the
actual common-stage completed-tower value and finite rational action, with no added
properness assumption on j. No further source/statement mismatch was found.
