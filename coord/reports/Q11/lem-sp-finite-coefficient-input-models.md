## Worker report

The new module `Sheaf.Paper.FiniteCoefficientInputModels` states
`AlgebraicGeometry.finiteCoefficientInputModels`, with its sole theorem proof `sorry`.
It constructs the canonical complex and derived tensor comparisons using the existing
scalar-restriction conjugate. Its other declarations are transparent abbreviations for
published functors and termwise complex functors, plus additivity instances obtained
by applying the published scalar adjunctions' `left_adjoint_additive`.
No object is selected from an unspecified existence theorem.

The mathematical statement is unchanged. Only `lean` and the permitted additions to
`stmt_deps` change. No dependency node is modified and no new definition node is needed.

### Hypotheses and objects

| Node hypothesis/object | Lean rendering |
| --- | --- |
| Noetherian scheme X, equivalently a finite affine cover by Noetherian spectra | `(X : Scheme.{u}) [IsNoetherian X]`; Mathlib's Noetherian scheme class is locally Noetherian plus quasi-compact |
| Prime ell | `(ℓ : ℕ) (_hℓ : ℓ.Prime)` |
| Finite commutative rings A and B | `A B : Type (u + 1)`, `[CommRing A] [CommRing B] [Finite A] [Finite B]` |
| A and B killed by powers of ell | `_hA` and `_hB` each assert `∃ n : ℕ, ∀ x, (ℓ ^ n) • x = 0` |
| Unital coefficient map A to B | `(φ : A →+* B)` |
| Ordered integer interval | `(a b : ℤ) (_hab : a ≤ b)` |
| L in the ordinary etale derived category | `L : Etale.DerivedCategoryModule A X` |
| Bounded constructible cohomology of L | `_hL : Etale.DerivedCategory.isBoundedConstructible A X L` |
| Every degree-zero module Tor test on L | `_hTor : Etale.DerivedCategory.hasTorAmplitudeIn A X a b L`; this is the recorded predicate, which quantifies over every etale module sheaf |
| Exact N_X on derived objects | `(ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory` |
| L_B | `(ProEtale.pbcFixedScalarExtension.{u} X.smallEtaleTopology φ).obj L`, the published left adjoint to actual derived restriction of scalars |
| (N_X L)_B | `(finiteInputProScalar φ X).obj (N_X.obj L)`; this is an abbreviation for that same published scalar-extension construction on the actual pro-etale site |

These are the fixed-ring ModuleCat presentations of the ordinary constant-ring
module categories. The recorded `finiteCoefficientEtaleRealization` and
`finiteCoefficientRealization` identify them with the respective ring-sheaf module
categories. The pro-etale objects remain in universe `u+1` and morphisms in `u`;
coefficient modules are in `u+1`. The explicit essential-smallness witness in
`finiteInputProScalar` instantiates the published site API; it is not a hypothesis
or an equality between site object and morphism universes.

### Every conclusion clause

| Node clause | Lean rendering |
| --- | --- |
| There exists one complex P representing L | `∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat A)) ℤ`, with `Nonempty (L ≅ DerivedCategory.Q.obj P)` |
| P is flat termwise | `∀ q, exactFunctor _ _ (tensorRight (P.X q))`; this is precisely tensor exactness, the recorded fixed-module reading of def-pc-flat-sheaf-modules |
| P is constructible termwise | `∀ q, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)` using the recorded finite-value stratification predicate |
| P vanishes outside [a,b] | `∀ q, q < a ∨ b < q → IsZero (P.X q)` |
| P is K-flat against arbitrary acyclic complexes | `MorphismProperty.kFlat (HomologicalComplex.quasiIso ... (.up ℤ)) P` with the canonical total-complex monoidal structure explicitly supplied |
| P tensor_A B | `finiteInputEtaleExtension φ X P` is exactly the existing `etaleSheafExtendScalars` applied termwise, retaining its B-action |
| N_X P | `finiteInputComparison A X P` is exactly `comparisonUpperStar` applied termwise |
| (N_X P) tensor_A B | `finiteInputProExtension φ X (finiteInputComparison A X P)` is exactly `sheafExtendScalars` applied termwise |
| Each of these three complexes has flat terms | Each has its own `∀ q, exactFunctor _ _ (tensorRight (... .X q))` conjunct, over its own coefficient ring and site |
| Each has the same strict degree interval | Each has its own `∀ q, q < a ∨ b < q → IsZero (... .X q)` conjunct |
| Each is K-flat | Each has its own quasi-isomorphism `kFlat` conjunct, with the actual complex category and monoidal structure supplied |
| They represent L_B, N_X L, (N_X L)_B respectively | Three separate `Nonempty (... ≅ DerivedCategory.Q.obj ...)` conjuncts in the actual target derived categories, not merely cohomology isomorphisms |
| The canonical tensor comparison identifies the last complex with N_X(P tensor_A B) | `finiteInputTensorComparison φ X P` is the inverse of the termwise image of the existing `etaleSheafExtendScalarsCompComparisonUpperStarIso`. That source is the conjugate of identity-on-sections scalar restriction. It is an actual B-linear complex isomorphism, not an arbitrary map or a `Nonempty` choice |
| The comparison also lives in the derived category | `finiteInputDerivedTensorComparison φ X P` is exactly `DerivedCategory.Q.mapIso (finiteInputTensorComparison φ X P)`, giving the specified derived isomorphism between those two models |
| L_B is bounded constructible | `Etale.DerivedCategory.isBoundedConstructible B X (L_B)` |
| L_B has Tor amplitude in the same [a,b] | `Etale.DerivedCategory.hasTorAmplitudeIn B X a b (L_B)` |
| N_X L is bounded constructible | Its cohomology sheaves satisfy `Scheme.IsConstructibleProEtaleFixedModuleSheaf X A`, and it satisfies the standard `DerivedCategory.TStructure.t.bounded` |
| N_X L has Tor amplitude in the same [a,b] | `ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat A) X a b (N_X L)`, the already recorded categorical specialization of the universal degree-zero module test |
| (N_X L)_B is bounded constructible of the same Tor amplitude | The same three separate intrinsic constructibility, standard boundedness and universal categorical Tor-amplitude conjuncts, now over B |
| No flatness/projective-dimension assumption on B/A | There is no such binder, no coefficient-flatness instance, and no restriction on the unital ring homomorphism |

For the canonical-comparison clause, the definition itself supplies the isomorphism;
there is no extra hypothesis assuming a comparison exists. Its localization is also
supplied as a public definition, while the theorem's three representation clauses
state the required derived identifications with the actual input L.

The categorical `kFlat` definition requires both tensor functors to preserve every
quasi-isomorphism. In the present symmetric abelian complex categories this is the
node's acyclic-test condition: apply preservation to an acyclic complex's map to zero;
conversely a quasi-isomorphism has acyclic cone, and tensor commutes with cones.
No boundedness restriction is imposed on the test complex.

### Dependency declarations read and used

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, the recorded cohomology convention and
  `Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `ProEtale.FiniteCoefficientModules`, `finiteCoefficientEtaleRealization`,
  `finiteCoefficientRealization`, `finiteCoefficientComparison`, and their exact
  realization interfaces; these justify the ordinary fixed-ring presentation.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`, using the actual finite-value predicate.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: reexports the recorded bounded-interval
  predicate; its extra GE predicate is not substituted for the bounded interval.
- `Sheaf.Paper.ComparisonPullbackExact`: `comparisonPullbackExact`,
  `comparisonConstantRingMap`; the exact module comparison is
  `ProEtale.comparisonUpperStar`, also read in its source.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: the recorded ordinary scalar
  functor and its K-flat, bounded constructible and same-interval clauses. Its
  intrinsic presentation is not silently imposed on ModuleCat-valued cohomology.
- `Sheaf.Paper.WitnessCompatibility`: `ProEtale.pbcFixedScalarExtension`, the actual
  scalar left adjoint for a general unital coefficient map, used on both sites.
- `WeilConjectures.SixFunctors.ProEtale.ScalarExtension`:
  `sheafExtendScalars`, `etaleSheafExtendScalars`, their adjunctions, and
  `etaleSheafExtendScalarsCompComparisonUpperStarIso`; the latter is explicitly
  defined by conjugating identity-on-sections restriction of scalars.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its K-flat representative characterization is the proof plan for the comparison.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, the recorded intrinsic finite
  stratification/local constancy/finite-stalk condition, not an etale-origin replacement.
- `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`:
  the recorded `HasRingedSiteTorAmplitudeOfUniverses` universal test on ringed
  modules. For these fixed-module objects the separately recorded exact categorical
  specialization below is used instead of copying that definition.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude`:
  `ProEtale.DerivedCategory.torAmplitudeIn`, attached to the already landed
  `def-sf-categorical-proetale-tor-amplitude`. Its source specializes
  `DerivedCategory.torAmplitudeIn` and tests every pro-etale module sheaf.
- `Mathlib.AlgebraicGeometry.Scheme`, `Mathlib.AlgebraicGeometry.Noetherian`, and
  `Mathlib.RingTheory.Noetherian.Defs`: `Scheme`, `IsNoetherian`, `IsNoetherianRing`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`
  and `CategoryTheory.exactFunctor`; the latter supplies its recorded fixed-module
  rendering without a new flatness definition.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: the preserved ringed
  predicates and publicly imported `CategoryTheory.MorphismProperty.kFlat`;
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat` gives its full definition.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` with the recorded finite-value
  cohomology predicate and a bounded interval.

All modules of the fifteen proof dependencies are imported (plain imports when
only needed by the postponed proof). The theorem docstring follows the DAG's
complete eight-step proof: flat-constructible replacement, bounded-flat K-flatness,
ringed pullbacks and their computations, canonical comparison, termwise scalar
constructibility, Serre closure, intrinsic site comparison, and Tor tests via the
flat-model criterion. The original source tag typo in the bounded-above dependency
is handled as the node already specifies: the proof docstring uses 06YQ, not 06YS.
The actual Stacks 0GL6 remark was opened in `more-etale.tex`; the report does not
attribute the flat-constructible input assertion itself to that remark.

### Added existing statement dependencies

`def-weil-pbc-constructible-complexes` names the exact bounded-constructible
predicate already used by the recorded flat-constructible input theorem.
`def-weil-pbc-witness-compatibility` names the published scalar-extension
adjoint and site/scalar comparison supporting declarations.
`def-sf-categorical-proetale-tor-amplitude` names the existing generic pro-etale
Tor predicate at `A = ModuleCat A` and `ModuleCat B`. Each is already landed;
only their ids are appended to this item's `stmt_deps`. No duplicate notions or
new data constructions are introduced, and no dependency's interface is replaced.

### Edge cases checked before stating

- Non-flat coefficients: A = Z/4, B = Z/2, L = A[0], a = b = 0 gives the
  flat B-model B[0]. The result needs neither B/A flat nor finite projective dimension.
- Identity coefficient map: the scalar adjunctions give the usual unit comparison;
  the chain comparison is the canonical restriction conjugate, not an arbitrary iso.
- Zero coefficient ring and zero complex: trivial rings and zero objects are allowed
  throughout, including exponent n = 0 in the annihilation hypothesis.
- Empty scheme and empty strata: `Scheme.Stratification` permits empty strata;
  its trivial one-stratum partition realizes the positive-size pro-etale convention
  even on the empty scheme. No geometric point of an empty stratum is chosen.
- Negative endpoints and a = b: all supports use integer comparisons exactly,
  with no positivity or extra width condition.
- The K-flat test is genuinely unbounded; the Tor test ranges over arbitrary
  module sheaves on each relevant site, not just constructible or flat sheaves.

### Searches

- `msearch.py ... leanfinder "Bounded flat constructible models preserved by finite
  scalar extension and etale proetale comparison"`: eight ordinary flat/etale
  algebra hits, including `AlgebraicGeometry.Flat.isStableUnderBaseChange`; no match.
- `msearch.py ... loogle "DerivedCategory, CochainComplex"`: twelve generic derived
  localization/single-functor declarations, including `DerivedCategory.Q`; no match.
- `msearch.py ... grep "flat.*[Cc]onstructible|[Cc]onstructible.*flat" CategoryTheory`:
  zero Mathlib hits.
- `msearch.py ... leansearch "A bounded complex of flat constructible etale sheaves
  remains K-flat and bounded constructible after arbitrary finite scalar extension
  and proetale comparison"`: eight ordinary module-flatness/base-change hits;
  no theorem with the four input models and the two simultaneous extensions.
- Direct `rg` and the requested id `grep -rn` in `lean/WeilConjectures`, and `rg`
  in `lean/Sheaf`: no declaration of this node and no name collision for any
  delivered declaration. Concept searches found FlatModel, the recorded
  EtaleFlatConstructibleModel, ScalarExtensionFunctor and the source scalar/site
  conjugate; these provide parts, not this entire statement.
- DAG/source search for `ProEtale.DerivedCategory.torAmplitudeIn` found the already
  landed `def-sf-categorical-proetale-tor-amplitude`, so no new node or alias
  implementation of Tor amplitude was added.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The existing
ringed versus fixed-module presentation differences are handled by the recorded
canonical realizations and the already recorded categorical predicate.

### Validation

`scompile.py Q11 lem-sp-finite-coefficient-input-models` compiled the complete
module both as a sandbox and under its final library module name, without errors
or warnings. The only postponed proof is the one named theorem of the item.
Final preflight/compile validation is supplied by the prescribed `deliver2.py`
dry run and delivery.

## Second reading by Q11

The dispatcher explicitly requires this worker to deliver without starting other
agents. This is a final worker clause audit; it does not claim an independent
second agent read the packet. The maintainer performs the independent delivery
review. Comparing the node and final file again found no missing hypothesis or
conclusion: all four complexes have their own flatness, strict support and K-flatness
clauses; the three requested representations are genuine derived isomorphisms;
the comparison is constructed canonically in both complexes and the derived
category; bounded intrinsic constructibility and the identical universal Tor
interval occur for each of the three output derived objects. Earlier compiler
probes exposed an ambiguous essential-smallness inference in the general scalar
API; the final abbreviation supplies the standard witness explicitly and changes
no universe or mathematical assumption. The proof remains `sorry`; no private
copy of a definition and no choice of an arbitrary map remains.
