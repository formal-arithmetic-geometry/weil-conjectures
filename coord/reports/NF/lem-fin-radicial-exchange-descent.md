## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteRadicialExchangeDescent` states
`AlgebraicGeometry.Etale.finite_radicial_exchange_descent`, with one `sorry` and no
new definitions. The node is unchanged except for `lean`. No statement correction,
dependency repair, new node, or disputed statement is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The coefficient convention of `def-weil-pbc-constructible-complexes` is
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. The sheaves are on the small etale
  sites and have values in `ModuleCat.{u + 1} Λ`, exactly the recorded convention.
- The base morphism S' → S is `v`, with `[IsFinite v] [Surjective v]
  [UniversallyInjective v]`. Universally injective is the scheme-theoretic radicial
  property (Mathlib's Stacks 01S4 convention).
- The finite-type S-schemes are the maps `aX`, `aY` with
  `[LocallyOfFiniteType aX] [QuasiCompact aX]` and the analogous two instances for
  `aY`. No separation, Noetherianity, or reducedness assumption is imposed.
- The S-open immersion is `j`, `[IsOpenImmersion j]`, and `hj : j ≫ aY = aX`.
- The constructible finite sheaf is `F` with
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. This predicate includes finite
  constant module values on a finite constructible stratification. `singleFunctor _ 0`
  places that sheaf in degree zero.
- The base change to S' is presented by `hY : IsPullback pY bY aY v` and
  `hX : IsPullback pX j' j pY`. Thus X' is also the base change of X over S.
  `L((pX)^*[ModuleCat Λ])` is exact derived inverse image, and `R((j')_*[ModuleCat Λ])`
  is total derived direct image, not an arbitrary functor or comparison.
- The upstairs bounded-constructible assumption is `hbounded`, applying the recorded
  `DerivedCategory.isBoundedConstructible Λ Y'` to that direct image.
- The upstairs formation assertion is `hexchange`: every `(T : Scheme.{u})
  [IsNoetherian T] (t : T ⟶ S')`, every Cartesian target presentation and every
  Cartesian source square has invertible canonical `derivedBaseChangeMap` evaluated
  on the pulled-back degree-zero sheaf. There is no bounded-constructibility
  assumption on any test target.
- The conclusion's first conjunct applies the same bounded-constructible predicate
  to `Rj_*` of the original degree-zero sheaf.
- The conclusion's second conjunct quantifies over every Noetherian T → S, with the
  same arbitrary Cartesian presentations, and asserts `IsIso` of the actual canonical
  exchange component. This is formation commuting with all the specified base changes.

Dependency declarations inspected and used:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`; its full definition
  uses the recorded constructible-module predicate on every cohomology sheaf and
  vanishing outside an integer interval.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets` retains/imports the recorded
  module declaration `AlgebraicGeometry.Etale.derivedBaseChangeMap` from
  `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`. Its full signature and
  docstring were read there: it is the mate of the canonical derived inverse-image
  square isomorphism, with the canonical derived adjunctions. The abelian helper is
  not substituted for the module-valued map.
- `def-weil-pbc-scheme-conventions` is explicitly a convention-only node with no
  module or declaration. Its named Mathlib properties are used directly: `Scheme`,
  `IsFinite`, `Surjective`, `UniversallyInjective`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsOpenImmersion`; Cartesian presentations use `IsPullback`.
- The underlying sheaf predicate is `Scheme.IsConstructibleEtaleModuleSheaf` in
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, and the derived category
  is `Etale.DerivedCategoryModule` in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, both read in full.

All recorded proof-dependency modules are imported (non-public when only needed for
stage 3), including universal-homeomorphism invariance, exact module inverse image,
exact derived functors, the mate-isomorphism lemma, topological invariance of the site,
constant sheaves, reduction, inverse-image composition and Mathlib mate pasting.
Mathlib geometric and homology ingredients are also supplied through those imports.
The docstring records all seven proof steps of the node, including Noetherianity of T'
and the canonical module exchange pasting argument.

Edge cases checked: empty source or target schemes, zero sheaf, zero coefficient ring,
identity cover, nonreduced bases, arbitrary characteristic, non-Noetherian S and S',
and empty Noetherian test schemes are not excluded. The finite universal homeomorphism
has an equivalence of etale topoi in these cases as well. All schemes and test schemes
use the same `u`; coefficients and sheaf values use `u + 1`, as the recorded categories
require. No independent small test universe or extra universe equality is imposed.
Arbitrary Cartesian presentations express the intrinsic assertion without selecting
new comparison maps or restricting to a favored presentation.

Searches (2026-10-15):

- `msearch.py ... leanfinder "Derived direct image and canonical base change descend
  along a finite surjective radicial morphism"`: eight hits, concerning geometric
  flat descent, normalization and base-change stability of finite/surjective morphisms;
  no etale derived exchange-descent statement.
- `msearch.py ... loogle "AlgebraicGeometry.Etale.derivedBaseChangeMap"`: zero hits,
  unknown identifier in the public index. The actual upstream declaration was located
  and inspected by source search, then used.
- `msearch.py ... grep "radicial|UniversallyInjective" AlgebraicGeometry`: 13 hits,
  only the geometric universally-injective API, not the theorem sought.
- `msearch.py ... leansearch "Etale derived direct image base change descends along
  finite surjective radicial maps"`: service unavailable, Internal Server Error.
- `rg -n 'radicial.*descent|fin.*radicial|lem-fin-radicial-exchange-descent'` on
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and project `lean/Sheaf`: no
  existing statement of this descent lemma. Project generic-open constructibility
  cites this argument in its proof plan but states a different theorem.
- `rg` for `derivedBaseChangeMap`, `DerivedCategoryModule`, and derived-image APIs
  located the upstream canonical map and recorded coefficient category; the neighboring
  generic-open module confirms the same arbitrary-Cartesian-presentation interface.

Validation: prescribed `scompile.py NF lem-fin-radicial-exchange-descent` compiled the
sandbox and library-path forms cleanly (3.4 seconds each), with no diagnostics.


## Second reading by NF

Independent reading of the node, the blueprint source at
sec-smooth-purity/sk-prop-sf-cbc/lem-fin-radicial-exchange-descent.md,
and the delivered Lean module. Verdict: the statement matches; no Lean or node
repair was needed. The worker report is retained above.

Object, hypothesis, and conclusion checklist:

1. Bases S and S' and their finite surjective radicial map: `{S S' : Scheme.{u}}`,
   `v : S' ⟶ S`, `[IsFinite v] [Surjective v] [UniversallyInjective v]`.
   Correct. I read Mathlib's finite and universally-injective class definitions:
   these are finite affine ring maps and universal topological injectivity,
   respectively, not merely injectivity on the original space.
2. Finite-type S-schemes X and Y: `aX`, `aY`, each with
   `LocallyOfFiniteType` and `QuasiCompact`. Correct, including nonseparated and
   non-Noetherian schemes. The convention-only dependency introduces no alternative
   structure or extra assumption.
3. Open immersion over S: `j`, `[IsOpenImmersion j]`, and `hj : j ≫ aY = aX`.
   Correct. The equation is the required S-linearity, not an additional restriction.
4. Finite constructible sheaf F: finite commutative coefficient ring
   `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`, module sheaf `F`, and
   `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. Correct under the coefficient
   convention of the node's constructible-complexes dependency and its proof.
   I opened that dependency and IsConstructibleEtaleModuleSheaf: the latter uses
   finite locally closed constructible strata and finite constant module values
   on etale trivializing covers, not the distinct upstream stalk predicate.
5. The base-changed schemes and sheaf: `pY`, `bY`, `hY : IsPullback pY bY aY v`,
   and `pX`, `j'`, `hX : IsPullback pX j' j pY`. Correct: Cartesian pasting with
   `hj` identifies X' with X ×_S S'. No separate arbitrary upstairs sheaf is used.
   `singleFunctor _ 0` puts F in degree zero and `L((pX)^*[ModuleCat Λ])`
   is its canonical exact derived inverse image.
6. Bounded constructibility upstairs: `hbounded` applies
   `DerivedCategory.isBoundedConstructible Λ Y'` to Rj'_* of that inverse image.
   Correct. I read the predicate: all integer cohomology sheaves are constructible,
   and an integer interval a ≤ b contains all nonzero cohomology.
7. Formation upstairs for every further Noetherian base change: `hexchange`
   quantifies over every T with `[IsNoetherian T]`, t : T → S', all target
   Cartesian presentations, then all source Cartesian presentations. Its conclusion
   is `IsIso` of `derivedBaseChangeMap ... sq.toCommSq` on the pulled-back F.
   Correct: the coefficient, argument, and orientation are those of the canonical
   exchange, with no additional assumption on test maps or boundedness downstairs.
8. Conclusion over S: the first conjunct is bounded constructibility of Rj_*F;
   the second quantifies over every Noetherian T → S with the same Cartesian
   presentations and asserts invertibility of the canonical exchange on F.
   Both clauses, their quantifier order, and their coefficients match the node.

Dependency signatures were read in BoundedConstructibleComplexes,
BaseChangeMapAbelianAndSets, IsConstructibleEtaleModuleSheaf, and upstream
SixFunctors/BaseChange/DerivedUnbounded and Etale/Derived/Coefficients. In particular
DerivedCategoryModule is precisely the derived category of the indicated small-etale
module sheaves. BaseChangeMapAbelianAndSets publicly imports and records the original
module-valued derivedBaseChangeMap; the delivered theorem uses that declaration,
not its abelian helper. The map is the mate of the derived inverse-image square
isomorphism under the canonical derived adjunctions. No unusable dependency record,
new definition node, dependency module, or statement correction occurs here.

Source cross-check: I read Stacks etale-cohomology.tex Tags 04DZ and 03SI,
morphisms.tex Tag 04DF, and sites-cohomology.tex Tag 0E47. They concern arbitrary
schemes and the canonical exchange under composition; they add no Noetherianity,
separation, reducedness, or characteristic hypothesis. The blueprint's hypothesis
is finite (not merely integral), which ensures that the pulled-back Noetherian test
scheme in proof step 5 is Noetherian. The docstring includes all seven expanded
node proof steps, including this point, constructibility descent on strata, and
canonical mate pasting. There is exactly one named theorem with proof `sorry`,
no definitions, no hollow data, no auxiliary proved assertions, and no unbound
variable or universe. Both required source/blueprint docstrings are present.

Edge cases: empty X, Y, S, or test schemes are allowed subject only to the stated
maps and surjectivity. Zero F and the zero coefficient ring are allowed; no
Nontrivial hypothesis appears. The identity cover, nilpotent thickenings and
arbitrary characteristic are included. There is no degree or nonempty-index
restriction; integer degree zero is only the embedding of the sheaf. All schemes
and test schemes use the common scheme universe u; coefficients and module values
use u+1, exactly the dependency's size convention, with no independent smaller
universe making the test quantifier vacuous.

Independent duplicate searches (2026-10-15):

- `msearch.py NF lem-fin-radicial-exchange-descent leanfinder "An etale derived
  exchange isomorphism is detected after a finite universal homeomorphism of bases"`:
  only etale geometric/algebra equivalence results, no matching descent theorem.
- `msearch.py ... loogle "IsIso (AlgebraicGeometry.Etale.derivedBaseChangeMap _ _).app"`:
  public index does not know IsIso; this search is inconclusive.
- Independent case-insensitive rg search for radicial/universalhomeomorphism paired
  with exchange/descent across Mathlib, upstream WeilConjectures, and lean/Sheaf:
  only GenericOpenImmersionConstructibility's proof-plan reference, not this lemma.
  The exact declaration name is absent from dag/lean_names_upstream.json.
  The upstream derivedBaseChangeMap itself was located and read, then reused.

Changes: appended this independent second reading only; no mathematical mismatch
was found and no correct statement was rewritten. The node lean.statement was
checked verbatim against the full signature in the sandbox file.
