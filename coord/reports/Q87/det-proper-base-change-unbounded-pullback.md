## Worker report

The module `Sheaf.Paper.UnboundedLocalizingPullback` states
`AlgebraicGeometry.ProEtale.unboundedLocalizingPullback` with `sorry`.
`UnboundedLocalizingPullback` is a structure packaging precisely its clauses; it
constructs no new pullback or coefficient ring. Its fields contain the restricted
functor and its properties, rather than asking for them as hypotheses.

Hypotheses and coefficients, checked against the node and its source page:

- Distinct primes are `(p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)`.
- The arbitrary characteristic-p field is `(k : Type u) [Field k] [CharP k p]`.
  There is no finiteness, perfection, or algebraic-closedness assumption on k.
- The two schemes have their existing `Scheme.Over (Spec (.of k))` structures;
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` are imposed on each
  structure map. Finite type is exactly the first two properties together.
- `(g : Y' ⟶ Y) [g.IsOver (Spec (.of k))]` is the arbitrary k-morphism. Neither
  properness nor smoothness nor flatness of g is assumed.
- The finite case quantifies over `A : Type` with `CommRing A`, `Finite A`, and
  its discrete topology; `(∃ n : ℕ, (l ^ n : A) = 0)` is annihilation by an l-power.
  `Profinite.continuousMapRingObj A` is its condensed coefficient ring. Every
  finite ring has a small representative; the theorem covers all finite rings,
  and does not require that A be a field or a quotient of a DVR.
- The next two conjuncts use `continuousMapRingObj ℤ_[l]` and
  `continuousMapRingObj ℚ_[l]` with their p-adic topologies.
- The finite-extension conjunct quantifies over the existing
  `PadicAlgCl.FiniteIntermediateField l`. It treats both
  `Profinite.padicIntegersRingObj l E` and `Profinite.continuousMapRingObj E`.
  These are exactly O_E and E with their induced topologies. Choosing finite
  subfields of the fixed algebraic closure is the source's coefficient convention.
- The last conjunct is `Profinite.padicAlgClRingObj l`, whose underlying sheaf is
  the finite-subextension-valued continuous functions, not all continuous maps.

Conclusion clauses, in the structure:

- `commShift` and `exact` assert triangulated exactness of
  `(CondensedRing.upperStar Λ g).leftDerivedFunctor`, the already defined total
  derived functor of the full module inverse-image composite. The existing
  `leftDerivedUpperStarIsoMapDerivedCategory` identifies it with exact termwise
  inverse image, so this is the g*=Lg* of the node.
- `sums` asserts `PreservesColimitsOfShape (Discrete I)` for every index type in
  `Type (u + 2)`, the object/index universe used by the recorded
  `localizingClosureProEtale` interface. This is preservation of arbitrary
  existing ambient small coproducts, including the empty coproduct; no nonempty
  or finite indexing assumption occurs.
- `constructible` takes an arbitrary object of the ambient unbounded derived
  module category and the conjunction `constantModelBoundedConstructible Λ Y K`
  and `DerivedCategory.finiteTorAmplitude _ K`. It returns exactly these two
  properties on its derived pullback. This is the object predicate underlying
  the dependency's `ConstantModelConstructibleFiniteTor` full subcategory.
- `sourceTriangulated` and `targetTriangulated` supply the inherited triangulated
  structures on the localizing full subcategories. `restriction` is a functor
  between those very full subcategories. `inclusion` equates its composite with
  the target full inclusion to the source full inclusion followed by Lg*.
  Thus it is a restriction of the specified ambient functor, not an unrelated
  functor with similar properties.
- `restrictionCommShift`, `restrictionExact`, and `restrictionSums` state the
  exactness and small-coproduct preservation of this restriction. The inherited
  shifts and distinguished triangles come from Mathlib's full-subcategory API.

Dependencies read and used:

- `Sheaf.Paper.LocalizingClosure`: `CategoryTheory.IsLocalizingSubcategory`,
  `CategoryTheory.localizingClosure`, `AlgebraicGeometry.ProEtale.localizingClosureProEtale`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`, and the
  predicate underlying `ConstantModelConstructibleFiniteTor`. These retain the
  finite constant scalar models, finite constructible strata, and affine-local
  convention of the dependency, without substituting upstream arbitrary matrices.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `CondensedRing.derivedUpperStarLowerStarAdjunction` and
  `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`, using
  `CondensedRing.upperStar` and `CategoryTheory.Functor.leftDerivedFunctor`.
- `sk-def-sfb-dc-setting`: its recorded declaration/docstring in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
  explains the explicit scheme-over-field binders; its chosen compactification
  is not needed to state inverse image. No new definition of the setting is made.
- `def-weil-triangulated-category`: Mathlib `Pretriangulated`, `IsTriangulated`,
  `Functor.CommShift`, `Functor.IsTriangulated`; the supplied signatures were read.
- `sk-def-sfb-qlbar-condensed` has no lean field but DOES have a closed slopmaster2
  audit. Its recorded `Profinite.padicAlgClCondensedRing` and
  `Profinite.padicAlgClRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` give the exact
  sheaf; that module and the finite-subextension construction were read. Per the
  standing brief, the closed audited dependency is reused without rebinding it.
- The available proof-dependency modules are imported without `public`; unrecorded
  proof nodes with no declaration are left for stage 3. The proof docstring
  follows all five steps, including the all-target-module Tor test and the
  uncompleted nature of the integral/rational pullback.

Edge cases checked: the empty scheme, zero complex, zero finite ring and exponent
zero, identity g, arbitrary (possibly empty) coproduct indices, the base field as
finite coefficient subextension E=Q_l, and arbitrary nonperfect k. None is excluded
by the binders. The underlying categories are unbounded; neither completeness nor
bounded-below hypotheses have been inserted.

Searches performed:

- `msearch.py ... leanfinder`: “Inverse image on unbounded pro etale derived module
  categories preserves coproducts and bounded constructible complexes with finite
  Tor amplitude”: eight generic condensed AB4/AB5 and derived t-structure hits;
  no theorem for these finite-constant-model finite-Tor localizing categories.
- `msearch.py ... loogle`: `"IsTriangulated", "PreservesColimitsOfShape"`:
  zero hits.
- `msearch.py ... grep`: `TorAmplitude|Constructible.*[Pp]ullback|[Pp]ullback.*Constructible`:
  zero hits.
- `rg` of the project and upstream sources for pullback, localizing, TorAmplitude,
  and constructibility found generic exact-derived interfaces, the dependency
  definitions above, and the older completed coefficient formalism; none states
  this theorem. The exact node-id search in upstream returned no matches.
- Searches for both proposed declaration names in upstream and `lean/Sheaf`
  returned no matches. The coefficient search located the existing EllAdic
  construction, so no second Q_l-bar definition or new notion node is needed.

The compiler initially reached the default heartbeat budget while elaborating
the inherited restricted shift. Transparent definitional equality and a scoped
800000-heartbeat budget resolve this without changing any type or the 60-second
wall-clock limit. The budget is scoped separately to the two declarations.

No statement correction, disputed statement, new definition node, or dependency
module is proposed. The original node is changed only in `lean`.

## Second reading by Q87

Author's separate check with the node and final signature open (the maintainer
provides the independent review): matched the primes, characteristic, both finite
and separated structure maps, and the k-morphism binder one by one. Read each
coefficient conjunct against the admissible list: arbitrary finite l-primary rings,
Z_l, Q_l, both O_E and E for every finite subextension, and the specified Q_l-bar
sheaf are all present. Checked that `constructible` uses the recorded finite-Tor
predicate in both source and target, not bounded constructibility alone. Checked
that `restriction` has an equality with the actual ambient derived functor after
full inclusion, and that exactness and sums refer to this same restriction.
All variables and the sole scheme/site universe are explicit; the finite scalar
models live in Type as in the published continuous-map coefficient API. No extra
geometric hypothesis was found. An initially inferred K binder was replaced by
its explicit ambient derived-category type before final validation.

Validation: the prescribed `scompile.py Q87 det-proper-base-change-unbounded-pullback`
completed successfully for the final file in both sandbox and final-module-path modes,
with no errors or warnings. The node signature was checked byte-for-byte against the
file; the node differs from the repository copy only in `lean`; all Lean lines are at
most 100 characters. Only `unboundedLocalizingPullback` has a `sorry` proof.

## Maintainer review fix (cc reviewer, 2026-10-18)

The delivered `UnboundedLocalizingPullback` took the shift-commutation of `Lg^*`
(`[commShift : ...CommShift ℤ]`) and of the restriction (`[restrictionCommShift : ...]`) as
existential data fields. No `CommShift` instance on
`(CondensedRing.upperStar Λ g).leftDerivedFunctor` exists in the library. So `exact` and
`restrictionExact` said only that *some* shift isomorphism makes the functor triangulated. That
is weaker than exactness of `g^* = Lg^*` with its canonical shift (def-weil-triangulated-category:
an exact functor is `[F.CommShift ℤ] [F.IsTriangulated]` for the functor's shift structure). The
restriction's shift was also not tied to the ambient one.

Fix, without changing the theorem signature (the node's `lean.statement` is unchanged):
- new `unboundedLocalizingPullbackCommShift`: the canonical shift of `Lg^*`, transported from
  Mathlib's `mapDerivedCategory` shift along `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`
  (local instance in this file);
- the structure is now a `Prop` with fields `exact`, `sums`, `constructible`, `localizing`
  (`Lg^*` maps `Loc(Dctf(Y))` into `Loc(Dctf(Y'))`), `sourceTriangulated`, `targetTriangulated`,
  `restrictionExact`, `restrictionSums`. The restriction is Mathlib's
  `ObjectProperty.lift (ι ⋙ Lg^*) localizing` with its inherited shift. This replaces the free
  `restriction` functor plus the equation `inclusion`.
