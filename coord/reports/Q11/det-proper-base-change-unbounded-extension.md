## Worker report

The module `Sheaf.Paper.UnboundedBaseChangeExtension` states
`AlgebraicGeometry.ProEtale.CondensedRing.unboundedBaseChangeExtension`, with `sorry` as its
whole proof. Two real helper definitions express its specified map and its implication:
`termwiseCondensedAmbientExchange` and `UnboundedBaseChangeExtension`. No theorem is proved.
No source statement was corrected and no new node or dependency module is required.

Clause-by-clause reading:

| Node clause | Lean rendering |
| --- | --- |
| A prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]`. |
| A field k of positive characteristic different from ell | `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`; a prime ring characteristic is positive. |
| Four separated finite-type k-schemes | The four `Scheme.{u}` variables each have `Over (Spec (.of k))`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on their structure morphism. The conjunction of locally finite type and quasi-compactness is finite type. |
| Every arrow is a k-morphism | `IsOver (Spec (.of k))` on each of `p`, `p'`, `g`, and `g'`. |
| The chosen cartesian square | `sq : ChosenCartesianSquare g' p' p g`, including its chosen pullback isomorphism, projection equations and `sq.toCommSq.w : g' ≫ p = p' ≫ g`. |
| p is proper; g arbitrary | `[IsProper p]`, with no extra condition on `g` or on `p'`. |
| Admissible commutative condensed coefficients | The conclusion enumerates finite discrete commutative rings killed by `ℓ^n`, `ℤ_[ℓ]`, `ℚ_[ℓ]`, all finite intermediate fields and their valuation rings, and `Profinite.padicAlgClRingObj ℓ`. All have the existing commutative ring-object structures. |
| Finite-subextension convention for Qlbar | `Profinite.padicAlgClRingObj ℓ` comes from `padicAlgClCondensedRing`, whose sections are precisely continuous maps with values in some finite intermediate field. It is not `continuousMapRingObj (PadicAlgCl ℓ)`. |
| Ordinary unbounded D(Mod of Lambda_X) | Both quantifiers of `UnboundedBaseChangeExtension` use `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))`. No completeness condition enters. |
| Bounded constructible finite-Tor generators | `constantModelBoundedConstructible Λ X K ∧ DerivedCategory.finiteTorAmplitude _ K`, the exact predicate used by the recorded closure. |
| Localizing closure under ambient small sums | `localizingClosureProEtale Λ X K`, imported unchanged from the recorded closure module. |
| Exact termwise inverse images | The source and target of `termwiseCondensedAmbientExchange` use `(upperStar Λ g).mapDerivedCategory` and `(upperStar Λ g').mapDerivedCategory`. |
| Total right-derived pushforwards | `(lowerStar Λ p).rightDerivedFunctor` and `(lowerStar Λ p').rightDerivedFunctor`; the full module-object composites are derived. |
| Specified unit/theta/counit exchange beta | `termwiseCondensedAmbientExchange` is the canonical `condensedAmbientExchange` with source and target transported along `leftDerivedUpperStarIsoMapDerivedCategory`. See the normalization explanation below. |
| Isomorphism on every Dctf object implies isomorphism throughout Loc | The defining implication of `UnboundedBaseChangeExtension` has an antecedent universally quantifying all generator objects, and a consequent universally quantifying all closure objects, with `IsIso` of the same map in both. The theorem asserts this implication separately for every stated coefficient. |

The six coefficient assertions are a conjunction of the source's cases, rather than an
extra admissibility assumption. A finite ring can always be represented in `Type 0`, so
`A : Type` does not exclude finite coefficient rings up to ring isomorphism. The explicit
discrete topology is exactly the prescribed topology, not a restriction on finite rings.
The condition `(ℓ ^ n : A) = 0` is equivalent to annihilation by that power, since A is unital.
All finite subextensions of the fixed algebraic closure are quantified, without fixing a
degree, a ramification bound, or a distinguished E.

Normalization of beta: the existing `condensedAmbientExchange` is defined by `mateEquiv`
from `condensedAmbientPullbackComparison` and the two
`derivedUpperStarLowerStarAdjunction`s. The comparison is
`(leftDerivedUpperStarComp Λ p' g).symm`, the equality of composites from the square,
and `leftDerivedUpperStarComp Λ g' p`. The latter is obtained by applying left derivation
to the existing underived `upperStarComp`, followed by the exact-functor composition
comparison. Its canonical identification with termwise derivation is
`leftDerivedUpperStarIsoMapDerivedCategory`. Transport the left adjoints of both derived
adjunctions along this identification. Naturality of the exact-functor comparison and its
composition comparison identify theta with the termwise image of the two `upperStarComp`s.
In the mate formula the intermediate p and p' comparison isomorphisms cancel with the
transported unit and counit. The two surviving comparisons are exactly the outer factors
in `termwiseCondensedAmbientExchange`: source `D(g*) -> Lg*`, then the existing mate, then
target `Lg'* -> D(g'*)`. Thus the definition presents the displayed beta on the precise
termwise endpoints, and introduces neither an arbitrary map nor a second choice of exchange.
The dependent `upperStarComp` Mathlib match is usable: it is the uniqueness-of-left-adjoints
construction applied to these very module-object adjunctions and `lowerStarComp`; the
published `upperStarComp` is that specialization.

Dependency declarations inspected and used:

- `sk-def-sfb-dc-setting`: the published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, including
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`; its explicit setting
  is rendered by the theorem's binders. The theorem does not use a chosen compactification.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients` publicly imports
  `Sheaf.Paper.LocalizingClosure`; the actual closure is
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale`, on the intersection of
  `constantModelBoundedConstructible` and `DerivedCategory.finiteTorAmplitude`.
  The imported `IsLocalizingAdmissibleCoefficient` has an all-continuous-maps Qbar branch;
  the source of this item explicitly overrides that convention. Accordingly the theorem
  enumerates the six cases, as the recorded pullback theorem does, and uses the required
  finite-subextension object. It does not apply that differing predicate to Qbar.
- `sk-def-sfb-qlbar-condensed`: its closed slopmaster2 audit identifies
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. Their actual sectionwise
  definitions and docstrings were read. No missing prerequisite is restated.
- `def-weil-pbc-cartesian-square`: `AlgebraicGeometry.ChosenCartesianSquare` in
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, publicly available through the exchange.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; universal closedness supplies quasi-compactness.
- `sk-prop-sfb-cartesian-coefficients`: `AlgebraicGeometry.ProEtale.cartesianCoefficients`,
  `CartesianCoefficientProperty`, and `cartesianCoefficientPullbackIso` from
  `Sheaf.Paper.CartesianCoefficients`. Exactness is already installed by the published
  module-object pullback API; this theorem module is a proof import.
- `sk-def-sfb-module-derived-pushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`,
  `leftDerivedUpperStarComp`, and `leftDerivedUpperStarIsoMapDerivedCategory` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`, together with
  the generic `Functor.rightDerivedFunctor` and `Functor.mapDerivedCategory`.
- `def-sfb-module-upper-star-comp`: the recorded
  `CategoryTheory.Adjunction.leftAdjointCompIso` from
  `Mathlib.CategoryTheory.Adjunction.CompositionIso` and its actual module-object
  specialization `AlgebraicGeometry.ProEtale.CondensedRing.upperStarComp` from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`. Its formula is
  used by the imported derived composition comparison, not redefined here.
- `sk-def-sfb-derived-categories`: `DerivedCategory` and `HasDerivedCategory`, plus the
  exact comparison just named and the recorded
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` module
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` as a proof import.
- Added existing dependency `def-weil-pbc-ambient-ringed-exchange`:
  `AlgebraicGeometry.ProEtale.CondensedRing.condensedAmbientExchange` and
  `condensedAmbientPullbackComparison` in `Sheaf.Paper.CondensedAmbientExchange`.
  This landed node gives the very canonical map whose termwise presentation the item uses;
  adding its id to stmt_deps is the authorized addition of a landed dependency.

Proof imports also include the recorded `Sheaf.Paper.UnboundedLocalizingPullback` and the
Mathlib adjoint-shift, exact-right-adjoint, triangulated-restriction and composition tools.
The proper-image detail and the determination node have no recorded module to import;
no substitute assumption for either is added. Their five-step proof use is retained in the
theorem docstring for stage 3. All statement dependencies are represented by the existing
objects and exact interfaces; no dependency record needs repair.

Edge cases checked before writing: empty schemes (no nonemptiness binders); zero complexes
(no nonzero restriction); identity and arbitrary base-change maps (g has no property binder);
zero finite coefficient ring (n = 0 is allowed); nonreduced finite rings such as Z/ell^2
(no field or flatness restriction on A); unbounded and noncomplete objects in the closure;
empty coproducts and sums indexed in the fixed ambient universe; all integers in finite Tor
amplitude (the existing predicate is used without a nonnegative-degree restriction).
Only p is assumed proper; no base-changed-proper hypothesis is added.

Searches performed in this session:

- `msearch.py ... leanfinder "Proper base change on bounded constructible finite Tor complexes extends to the localizing closure"`: eight unrelated source-local-closure/stability hits; no matching theorem.
- `msearch.py ... loogle "CategoryTheory.Adjunction.leftAdjointCompIso, CategoryTheory.NatTrans.CommShift"`: zero hits for the combined query. The individual recorded declarations were then read in their source files.
- `msearch.py ... leansearch "Proper base change extends from constructible complexes to localizing closure"`: eight localization/base-change and stability results, including properness stability; no extension theorem.
- `msearch.py ... grep "baseChange.*localiz|localiz.*baseChange|isoLocus" CategoryTheory`: zero hits.
- `rg` of `det-proper-base-change-unbounded-extension`, `properBaseChange`, and localizing/base-change patterns in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, the read-only side framework, and `lean/Sheaf/Paper`: found the integral localizing theorem's proof citation, and the existing ambient exchange construction, but no general extension statement.
- `rg` of the proposed declaration names and item id in `dag/lean_names_upstream.json`, upstream `WeilConjectures`, and `lean/Sheaf`: no existing declaration with the proposed names.
- The recorded sources, framework notes, current blueprint statement and full proof paragraph were read. No external source download was needed.

Validation: `scompile.py Q11 det-proper-base-change-unbounded-extension` on the delivered
module completed cleanly, including its sandbox and library passes (5.2 s and 4.5 s).
No warnings or errors were emitted. There is one intentional named theorem `sorry`.

## Second reading by Q11

This is an in-thread second pass with the node JSON and final Lean file reopened; no other
agent was started, as required by the dispatcher brief. I checked each row above against
the actual signatures and the helper bodies. The coefficient list has all six cases, and
Qbar uses `padicAlgClRingObj`; no all-continuous-maps coefficient was substituted. The
source/target arrows of the two transport isomorphisms give `Rp_* ⋙ D(g*)` and
`D(g'*) ⋙ Rp'_*`, and the same transported component is used in the antecedent and
consequent. The Dctf predicate is exactly the generator predicate of the imported closure;
finite Tor amplitude is not dropped. All four schemes and all four k-morphisms are bound,
p alone is proper, and cartesianness includes the chosen pullback identification.
Every universe and section variable is explicitly declared. The only postponed proof is
the theorem, whose docstring follows all five DAG proof steps. No mismatch requiring a
statement correction was found. The existing ambient-exchange dependency was added rather
than silently omitted from the dependency record. The admissibility-predicate discrepancy
is resolved by explicit source-coefficient enumeration, with no dependency edit. No further
code change was needed after compilation.
