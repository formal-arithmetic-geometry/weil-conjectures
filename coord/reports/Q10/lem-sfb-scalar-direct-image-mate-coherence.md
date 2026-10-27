## Worker report

The module `Sheaf.SixFunctors.ScalarDirectImageMateCoherence` states
`AlgebraicGeometry.ProEtale.CondensedRing.scalarDirectImageMateCoherence`.
Its only postponed proof is this named theorem, with the complete five-step DAG
proof in its docstring. The two supporting definitions contain real data.

The node statement is unchanged. `stmt_deps` gains the already landed
`def-sfb-test-map-derived-composition`: its published general-scheme-map
`RootCoordinateFace.lowerComp` is needed in the statement, rather than only the
proof. No new notion, node, dependency module, or correction is required.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Arbitrary commutative condensed rings and their map are
  `{Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')`. `ScalarSixRing` is the recorded
  `CommMon` of abelian sheaves on the coherent profinite site. Its underlying
  `Λ.X` is the `Profinite.CondensedRing` ring-object presentation; the bundled
  commutative object supplies the commutativity instance. Nothing requires a
  presentation by a topological ring or any admissible-coefficient restriction.
- Arbitrary schemes and composable maps are `{X Y W : Scheme.{u}}`, `f`, and `g`.
  `ModuleRingedComparison.internalModules Λ.X X` uses the original small
  pro-etale topology on `X.ProEt`, with its distinct object and morphism sizes.
  The coefficient sheaves are pulled back from the point, not constant discrete
  replacements. `DerivedCategory` is the ordinary unbounded module-derived
  category; no completion or constructibility subcategory appears.
- `T_Z` is precisely the already defined `scalarSixChange a Z`, the left functor
  of the published derived extension/restriction adjunction at `coefficientMap`.
  `scalarSixPull` is the exact termwise presentation of derived pullback.
  `RootCoordinateFace.lower Λ.X f` is the published total right derived functor
  of the full module direct image. `RootCoordinateFace.adjunction` is the actual
  exact-pullback/right-derived adjunction of the same underived adjunction as
  `derivedUpperStarLowerStarAdjunction`; exactness identifies the latter's
  K-flat left-derived functor with termwise pullback.
- `c_f` is `(scalarDirectImagePullbackData.theta a f).inv`. The definition
  `scalarDirectImagePullbackData` projects the witness supplied by the recorded
  `scalarSixPullback` theorem. Its `thetaNormalization` fixes every forward map
  to `scalarSixPullHom a f`. Hence the choice determines the comparison up to
  equality (isomorphism inverses are then unique); it does not choose data from
  a mere unspecified existence theorem. The remaining fields are propositions.
  In particular there is no new hypothesis supplying arbitrary comparisons.
- `scalarDirectImageMate a f` is `mateEquiv` of that inverse and the actual
  geometric adjunctions. Expanding the existing `mateEquiv` definition at `K`
  gives `eta'` followed by `R'_f(c_f)` followed by `R'_f(T_X epsilon_f)`, exactly
  the node's defining formula, using functoriality to split the final map.
- The first conjunct quantifies over all `K`, `K'`, and `h : K ⟶ K'` and writes
  the naturality square of this specified transformation.
- The second conjunct is the geometric composition equation, with the two
  `RootCoordinateFace.lowerComp` transports inserted. The left path is gamma
  for `f ≫ g` followed by the primed compositor. The right path first applies
  `T_W` to the unprimed compositor, then gamma for `g` at `R_f K`, then `R'_g`
  of gamma for `f`. This states equality before suppressing the canonical
  identifications, with precisely the orientation of the DAG proof step 3.
- The third conjunct is the node's unit equation for every `N`, using
  `RootCoordinateFace.adjunction.unit`, the published scalar functor on the
  unprimed unit, and `theta.inv` on the right.
- The fourth conjunct is the node's counit equation for every `K`, using
  `scalarSixPull Λ' f` on gamma and the primed counit on the left, and `c_f`
  followed by scalar extension of the unprimed counit on the right.
- The fifth conjunct quantifies over every further commutative condensed ring
  `Λ''` and map `b : Λ' ⟶ Λ''`. `scalarSixTower a b Z` is the already specified
  derived tensor associator. Its left path is `s_Y` followed by gamma for
  `a ≫ b`; its right path is `T_Y^b(gamma^a)`, gamma for `b` at `T_X^a K`, and
  `R_f` over `Λ''` of `s_X`, exactly the scalar-composition equation.
- All these equalities occur in the internal module-derived categories. The
  module actions are part of the objects and morphisms; no forgetful functor
  is used to replace a required equality. CoefficientMap and the canonical
  Cartesian identifications are the recorded ones. There are no flatness,
  boundedness, finite-type, invertibility, or constructibility hypotheses.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and its small-site topology, used by the published internal-module categories.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `AlgebraicGeometry.ProEtale.coefficientMap`, its identity/composition laws,
  and the two coefficient squares; `derivedComapUpperStarIso` normalizes the
  scalar pullback hom through the already published scalarSixPullHom.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`
  and `leftDerivedUpperStarIsoMapDerivedCategory`, giving the actual total
  derived adjunction and its exact-pullback presentation.
- `Sheaf.SixFunctors.ScalarSixPullback`: `scalarSixPullback`,
  `ScalarSixPullbackData` (including normalization, composition and tower),
  `scalarSixChange`, `scalarSixPull`, `scalarSixPullComp`, `scalarSixPullHom`,
  `scalarSixTower`, and the existing internal module-category presentation.
- `Sheaf.Paper.CartesianCoefficients`: `cartesianCoefficients` and
  `cartesianCoefficientPullbackIso`; the untwisted canonical inverse-image
  identification carries the coefficient action. Its twist and finite-free
  clauses impose no hypotheses on this theorem and are not used here.
- `Sheaf.Paper.RootTowerCoordinateFace`, recorded for
  `def-sfb-test-map-derived-composition`: `RootCoordinateFace.lower`,
  `upper`, `adjunction`, `upperComp`, `lowerComp`. `lowerComp` is defined by
  `conjugateIsoEquiv` of the inverse exact pullback compositor, as required.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `unit_mateEquiv`,
  `mateEquiv_counit`, `mateEquiv_hcomp`, `mateEquiv_vcomp`,
  `mateEquiv_conjugateEquiv_vcomp`, `conjugateEquiv_mateEquiv_vcomp`,
  `conjugateEquiv` and `conjugateIsoEquiv`. These are the recorded Mathlib
  matches of all five generic mate/conjugate proof dependencies. Their full
  signatures and source docstrings were read; no private mate construction
  or restatement of these lemmas is introduced.

Edge cases checked before writing: identity geometric maps, identity coefficient
maps (including either map of the scalar tower), zero objects, empty schemes,
and nonflat maps such as condensed discrete Z to Z/2. Every functor and equality
is still typed in these cases; no map gamma is inverted. Complexes may be
unbounded in both directions. No characteristic or prime parameter is introduced.
The universe convention is the original pro-etale one, without identifying the
object and morphism universes. The selected pullback comparison remains fixed by
its normalization in all cases.

Searches made (also logged by msearch.py in searches.jsonl):

- LeanFinder, query “Naturality geometric composition units counits and successive
  scalar extension of canonical derived coefficient direct image mates”: eight
  hits, including `unit_mateEquiv`, `mateEquiv_counit` and ordinary module scalar
  composition. No declaration states all the specified derived comparisons.
- Loogle, query `CategoryTheory.mateEquiv, CategoryTheory.mateEquiv_hcomp,
  CategoryTheory.unit_mateEquiv`: zero hits. Direct Mathlib source reading then
  found the recorded general mate lemmas above.
- msearch grep, query `mateEquiv|unit_mateEquiv`, subdirectory
  `CategoryTheory/Adjunction`: five hits in Mates.lean, giving the existing
  definition and unit/counit identities; used rather than copied.
- rg on both `lean/WeilConjectures` and `lean/Sheaf`, queries for scalar mate,
  scalar direct image, scalarSix gamma, and the new declaration names;
  grep of the exact item id in upstream: no existing complete statement.
  The upstream `derivedPushHom` is a related construction from the restriction
  square, not this full coherence assertion. Its source and `derivedPullIso`
  were read. `Sheaf.Paper.DerivedScalarMateComposition` handles sectionwise
  ring-sheaf models with another normalization and only geometric composition;
  it is not the present internal condensed-coefficient assertion and was read.
- Exact new-name rg over Mathlib, upstream and Sheaf: no collision for
  `scalarDirectImagePullbackData`, `scalarDirectImageMate`, or
  `scalarDirectImageMateCoherence`.

Validation: scompile.py compiled both its sandbox probe and the delivered library
module cleanly; no errors or warnings were printed. The library file completed
within the normal per-file limit.

No statement dispute or known node fault.

## Second reading by Q10

No separate worker was started: the dispatcher brief prohibits other agents and
requires direct delivery. The maintainer's independent review reads this packet.
The worker checked both node and file, especially the direction of theta inverse,
both compositor transports and the ordering of the three scalar-tower arrows.
