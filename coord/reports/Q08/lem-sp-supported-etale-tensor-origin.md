## Worker report

The module `Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin` states
`AlgebraicGeometry.ProEtale.SupportedEtaleTensorOrigin.supported_etale_tensor_origin`.
It supplies canonical comparison constructions as helpers of this same statement.
Every definition contains actual data. The three postponed proofs are the main theorem,
naturality of the ordinary balancing map, and existence and uniqueness of its normalized
pro-etale derived scalar/tensor isomorphism. The latter two implement precisely the
canonical scalar/tensor identification in Step 5 of this node, and carry proof docstrings.
They are listed, together with the comparison constructions, in `lean.declarations`.
There are no new independent notions, dependency repairs, or statement corrections.

Hypotheses and clauses:

- The prime is `(ℓ : ℕ) (hℓ : Nat.Prime ℓ)`; `A B : Type u`, CommRing and Finite
  instances give finite commutative unital rings, with the given unital map `f : A →+* B`.
  `hA` and `hB` say that a power of ℓ is zero. Exponent zero permits only the zero ring,
  which the node also permits. No nontriviality, flatness, or Tor bound on B is imposed.
- `U Z : Scheme.{u}`, `j : U ⟶ Z` and `[IsOpenImmersion j]` retain arbitrary schemes.
  No Noetherianity, quasi-compactness, separation or characteristic assumption is added.
- The ordinary uncompleted categories are the recorded `Etale.DerivedCategoryModule`
  and `DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat (ULift A)))`.
  `comparison` is the exact termwise `comparisonUpperStar.mapDerivedCategory`.
  The fixed and intrinsic categories are identified by the recorded
  `sfIntrinsicDerivedEquivalence`, without changing site or scheme universes.
- `hM : DerivedCategory.TStructure.t.bounded M` is bounded cohomology. `hc` uses
  the recorded `IsConstructibleProEtaleFixedModuleSheaf` on EVERY homology sheaf.
  That predicate requires a positive finite constructible locally closed stratification,
  local constancy, and finite geometric stalks, not an etale-origin assumption.
- `ht` uses the recorded `HasFiniteProEtaleTorAmplitude U A` on the canonical
  intrinsic realization of M. Its universal degree-zero module tests and one ordered
  interval are retained. This declaration is reexported by the current dependency module
  `RingedProEtaleTorAmplitudeOfUniverses`; the fixed-module category is not substituted
  for the intrinsic Tor test.
- The conclusion quantifies `L`, asserts `TStructure.t.bounded L`, asserts the recorded
  `IsConstructibleEtaleModuleSheaf` on every cohomology sheaf, and supplies the origin
  isomorphism `e : (comparison A U).obj L ≅ M`.
- `etaleOpen A j` is the recorded etale open extension by zero descended termwise;
  its value on L is K. `proOpen A j` is the fixed-coordinate value N. `openPresentation`
  is the canonical comparison of that fixed operation with the recorded intrinsic
  `sfIntrinsicExtensionByZero`, constructed by cancelling the realization unit and
  descending the exact sheaf square. It is not a replacement open-extension definition.
- `etaleTensor f j L` is H, using the recorded Etale.derivedTensor with the
  `Etale.scalarCoefficient (liftedHom f) Z` as the second input. This is precisely B
  with its restricted A-action, in degree zero; no B-action is forgotten accidentally.
  The theorem asserts boundedness of both K and H, and separately `t.plus` of both.
- The first canonical identification, relative to e, is `supportedComparison A j L M e`.
  It descends the existing `openImmersionLowerShriekComparisonUpperStarIso` and applies
  `proOpen.mapIso e`. It is defined for every e, so the theorem's witness e supplies it
  without an additional existential choice of an isomorphism.
- The second canonical identification is obtained from `fixedTensorComparison` at K,
  followed by tensoring `supportedComparison` with the specified B coefficient. The
  former is an actual natural isomorphism, built by `tensorScalarSquare` from the
  etale scalar/tensor iso, `pbcDerivedComparisonRestrict`, `pbcComparisonReduction`,
  and `proScalarTensorIso`. This uses the same K-flat balancing normalization as the
  unbounded monoidal comparison; its ordinary map is scalar unit, lax tensorator of
  restriction, and the right unitor. No boundedness of H is used in its definition.
- The third identification is the specified `supportedFixedScalarMap f j` at M.
  Its source is N tensor B, in fixed coordinates, and its target is the fixed restriction
  of `j!_B (fixedScalar f U M)`. The theorem asserts `IsIso` of the intrinsic realization of THIS arrow. It is the
  inverse normalized scalar/tensor map followed by restriction of `openScalarMap`,
  which is the mate of the exact restriction square `sfFixedOpenRestriction`.
  `restrictionPresentation`, `openPresentation`, and `scalarPresentation` transport
  this target to exactly `scalarRestriction f Z (j!_B (scalarExtensionFunctor f U (E_U M)))`.
  `supportedIntrinsicScalarMap` composes those three boundary comparisons explicitly,
  and the theorem asserts its component at M is invertible. Thus its target literally
  contains the recorded scalarExtensionFunctor and intrinsic extension by zero. These
  comparisons are normalized by identity on scalar-unit sections and adjunction units.
  No bare Nonempty natural isomorphism or arbitrary map is used in any definition.

The reducibility boundaries are `@[irreducible] def`, not axioms or opaque constants;
all have explicit construction bodies and can be unfolded by a subsequent proof.
The original direct specialization of the unbounded monoidal comparison was expensive
in kernel reduction. The final composition through normalized scalar/tensor comparisons
compiles in about 12 seconds without changing its objects or normalization.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: finite-coefficient module categories;
  `SfIntrinsicRealizationTransport`: `Scheme.sfIntrinsicDerivedEquivalence`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: ordinary derived category,
  homologyFunctor, `TStructure.t.bounded` and `TStructure.t.plus`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`:
  `Scheme.sfIntrinsicExtensionByZero`, its additive and exact instances;
  fixed-coordinate `ProEtale.openImmersionLowerShriek`.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses` reexports
  `Scheme.HasFiniteProEtaleTorAmplitude` used in ht.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`:
  `ProEtale.scalarExtensionFunctor`, with its original ringed derived extension;
  `scalarRestriction` from its public OpenScalarExchange import.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
- `Sheaf.Paper.EtaleDerivedScalarTensor`: scalarCoefficient, scalarTensorIso_existsUnique,
  scalarTensorModelFunctor and scalarTensorModelNormalization. The general normalization
  is reused verbatim for the pro-etale specialization, not redefined.
- `Sheaf.Paper.SfCompactSupportRestrictionOfScalars`: sfRealizationRestriction,
  sfFixedOpenRestriction. The scalar presentation is the left-adjoint uniqueness map
  of this section-normalized restriction comparison. The similarly named published
  transport module imports the downstream ReductionDirectImageComparison, so it is
  not imported here: that would close the item's dependency cycle.
- `Sheaf.Paper.WitnessCompatibility`, publicly imported through the preceding modules:
  pbcFixedScalarExtension, pbcComparisonReduction, pbcDerivedComparisonRestrict.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison`:
  openImmersionLowerShriekComparisonUpperStarIso.

The proof-only imports name the node's declared proof route: finite constructible sheaf
origin, boundedConstructible_of_homology, exact extension by zero and comparison,
exact comparison pullback, canonical ringed tensor pullback, open projection formula,
constant-ring map, and classical comparison faithfulness. Their use is explained in the
main proof docstring. The general exact functor/cohomology ingredient uses the dependency's
Mathlib match, with the exact-functor homology comparison available through these imports.

Edge cases checked: zero ring A or B; exponent zero; zero M; empty U or Z; identity j;
coefficient identity or quotient; non-Noetherian U and Z; arbitrary positive or negative
cohomological shifts; and B of infinite projective dimension over A. All remain admitted.
The finite constructibility predicate's positive number of strata does not exclude an
empty scheme, since an empty stratum is permitted. A finite Tor interval tests B_U itself.
The formal sites keep object universe u+1 and morphism universe u; coefficients use ULift
into u+1 and all bound variables and universes are explicit.

Searches actually made:

- `msearch.py ... leanfinder "A bounded constructible finite Tor amplitude pro-etale
  complex extended by zero has bounded etale origin and bounded derived coefficient
  tensor"`: eight unrelated algebraic-etale/bounded-derived-representative hits, no match.
- `msearch.py ... loogle '"Sheaf", "tensor"'`: twelve mostly
  PresheafOfModulesOfCommRing tensor declarations, no statement of this lemma.
- `msearch.py ... grep 'pro.?etale.*(constructible|bounded)|constructible.*pro.?etale'`:
  zero Mathlib hits.
- `rg` of the item id and supported-etale-tensor/origin keywords in both
  `lean/WeilConjectures` and `lean/Sheaf`: no existing exact declaration. Targeted
  searches found the recorded comparison, scalar, exact open and tensor APIs used above.
- Existing scalar/tensor and realization source signatures and docstrings were opened;
  the published etale scalar normalization supplies exactly the reusable general
  representative predicate. No new independent notion was needed.

No STATEMENT-DISPUTED finding or statement correction.

## Second reading by Q08

This is a dispatched solo worker delivery. No independent second reader was started:
the brief reserves that independent reading to the maintainer. During the worker's own
final rereading, the node and final file were compared clause by clause as recorded above.
The check corrected the distinction between intrinsic finite-Tor tests and fixed-coordinate
constructibility, retained the globally constructible strata condition, and kept the
specified B-action in the coefficient sheaf. The final comparisons are defined normalized
maps, not existential isomorphisms. This paragraph does not claim an independent review.
