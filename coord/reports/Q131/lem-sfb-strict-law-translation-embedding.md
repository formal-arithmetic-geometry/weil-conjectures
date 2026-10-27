## Worker report

The delivery states `AlgebraicGeometry.strictLaw_translation_embedding` in
`Sheaf.AlgebraicGeometry.StrictLawTranslationEmbedding`. Its only proof is `sorry`.
Two new definition modules supply the missing relative rational-map, chart-quotient,
and strict-law language. Every definition contains real data, with no choice from
an existence theorem and no postponed construction. No existing node statement is
changed. No dependency record needs repair.

Source read: BLR, Néron Models, 5.2, printed pp.118–119, primary scan
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf
(PDF pages 124–125, zero based). The construction preceding Lemma 4 uses all
S-schemes as test objects, pulls back the universal left translation, and Lemma 4
asserts monomorphy and compatibility with the partial multiplication. The latest
blueprint contains no separate strict-law definition (the ancestor command gives
None); the inherited BLR source and complete via chain are retained for new nodes.

Hypothesis and clause correspondence:

- The ring is `A : Type u`, `[CommRing A]`, `[IsNoetherianRing A]`.
  `[IsStrictlyHenselianLocalRing A]` includes `HenselianLocalRing A`, hence the local
  ring structure, and separably closed residue field. No redundant local instance
  assumption is added. Normality is exactly the recorded inline condition `hnormal`:
  every prime localization is a domain and integrally closed.
- `S = Spec A` is written explicitly `Spec (CommRingCat.of A)` throughout; `Y : Over S`
  retains the structure morphism `Y.hom` rather than an arbitrary untied map.
- `[Smooth Y.hom]`, `[LocallyOfFiniteType Y.hom]`, and `[QuasiCompact Y.hom]`
  express smooth finite type. `[IsClosedImmersion (pullback.diagonal Y.hom)]`
  expresses the stated relative separatedness, without assuming Y absolutely separated.
- `hfibres : ∀ s, Nonempty (Y.hom.fiber s)` expresses nonempty scheme-theoretic fibres.
  `fiber` is Mathlib's pullback along `fromSpecResidueField`.
- An S-dense open is `RelativeBirational.FibrewiseDense p U`, defined as density
  of the inverse image under `p.fiberι s` for every base point s. This is exactly
  the open of the scheme-theoretic fibre, not a pointwise test on geometric points.
- A relative partial map contains an actual open domain, fibrewise density, a
  scheme morphism, and its equation over S. `PartialMap.Agrees` requires an
  S-dense common open with equality of restricted scheme morphisms. `RationalMap`
  is its quotient. `Chart` contains an isomorphism between two dense opens over S;
  `SelfMap` is the quotient by dense agreement. `Quot` imposes the equivalence
  closure; common-open agreement is already an equivalence relation (finite
  intersections of fibrewise dense opens are dense), so this is the stated quotient.
- `m : StrictLaw Y` retains a multiplication representative `m.mul : PartialMap
  (square Y) Y`. `Associative` provides an S-dense open of `cube Y`, the four
  factorizations of `(a,b)`, `(b,c)`, `(a,m(b,c))`, `(m(a,b),c)` into its domain,
  and equality as morphisms of the two results. Storing a representative of the
  rational law is legitimate because a strict law supplies such a domain D.
- The strictness opens are `m.mul.domain`, `m.leftRange`, `m.rightRange`.
  All six projection-density conditions are separate structure fields. `leftIso`
  and `rightIso` are actual scheme isomorphisms; their four projection equations
  are exactly `(x,m(x,y))` and `(m(x,y),y)`. The ambient hypotheses occur in the
  theorem binders, so the bare strict-law datum has no hidden additional hypothesis.
- The existential `B : (Over S)ᵒᵖ ⥤ GrpCat` is a contravariant group-valued functor
  on every S-scheme. Its objectwise equivalences `e T` identify its underlying
  sets with the actual chart quotient `SelfMap ((Over.pullback T.hom).obj Y)`.
  These equivalences merely express the stated group structure on that quotient;
  they do not postulate an unrelated group or replace a canonical map by one.
- `IsComposite f g h` specifies agreement with `f ∘ g` on a fibrewise dense common
  open and a genuine lift into f's domain. The theorem asserts composite charts
  exist for every pair and that multiplication in B is their class under e.
  Thus the group operation is composition in the order τ_a ∘ τ_b.
- `RelativeBirational.IsPullback Y g f f'` fixes both full inverse-image opens
  under the existing `baseChangeMap` and the induced isomorphism, with equations
  for both inclusions. The theorem asserts existence of such a chart for every
  base morphism and states that `B.map g.op` takes its class to this pullback class.
  Functor identity and composition equations and group homomorphisms are supplied
  by the type of B. The quotient identifications account for iterated pullback.
- `τ : yoneda.obj Y ⟶ B ⋙ forget GrpCat` is a natural transformation from exactly
  `Y(T) = Hom_S(T,Y)`. Its components are injective for every T.
- For each T and a, the theorem supplies a chart f with `IsLeftTranslation m T a f`
  and `e T (τ.app (op T) a) = f.toSelfMap`. The predicate fixes the pairing q
  by its two projections, fixes both full inverse-image opens under q, and fixes
  the isomorphism by commuting with `m.leftIso`. This is precisely pulling back
  the universal left translation in the first coordinate, including sheaf maps.
- The last conjunct quantifies over every representative r of the rational law,
  with `r.Agrees m.mul`, and every factorization d of `(a,b)` into its domain.
  The two projection equations identify a,b and `d ≫ r.hom = c.left` identifies
  `m(a,b)=c`. It concludes `τ(c)=τ(a)*τ(b)`, i.e. the required composition equation.
  It is not limited to D or to reduced/field-valued test objects.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`. The theorem uses Scheme, Hom and Spec directly.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: scheme base change
  is `Over.pullback`, `Limits.pullback`, its two projections and `baseChangeMap`;
  the dependency's primary declaration `Scheme.Modules.moduleBaseChange` is for
  module sheaves and is not incorrectly substituted for scheme base change.
  Its full source docstring and all six recorded signatures were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` and `Localization.AtPrime` from their Mathlib modules,
  in the dependency's prescribed inline normal-ring form.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`,
  extending Mathlib's `HenselianLocalRing` with separably closed residue field.
- The two new definition nodes below use Mathlib scheme morphisms, open subschemes,
  `homOfLE`, `Over`, `fiber`, `fiberι`, fibre products and isomorphisms directly.
- Proof-only import `Mathlib.AlgebraicGeometry.Sites.Fpqc` supplies the already
  recorded fpqc-covering and representable-descent tools. Smoothness permanence
  and smooth-flatness are already available in the public smoothness module.
  The two sfb proof dependencies have no recorded declarations, so have no module
  import yet; their results are described in the seven-step proof docstring.

Edge cases checked: T empty (the unique empty maps and chart classes cause no
exception), nonreduced T (all comparisons are equalities of scheme morphisms),
arbitrary T→S (no smoothness, finite-type, reducedness or flatness binder on T),
reducible or disconnected fibres (density is in the whole fibre, and no integral
or irreducible assumptions appear), zero-dimensional fibres, and all characteristics.
No component of a nonempty fibre can be silently discarded. Empty fibres are
allowed in the general definition, but Y's fibres are nonempty as required here.
The single universe u is the ordinary `Scheme.{u}` convention: every test scheme
in the same category is included, with no independent lower universe restricting
which algebras can be tested. Smoothness and finite type on Y are not duplicated
as assumptions on the test family: they hold after arbitrary base change.

Searches made:

- `msearch.py ... leanfinder "Relative strict birational law injective left
  translation into birational self maps of schemes"`: eight unrelated injective,
  dominant and absolute-partial-map hits, no relative-law translation theorem.
- `msearch.py ... leansearch "relative rational map scheme dense in every fibre
  strict birational group law"`: eight hits including `Scheme.RationalMap` and
  `Scheme.PartialMap`; full source signatures show absolute topological density,
  not fibrewise density and arbitrary-base pullback.
- `msearch.py ... leanfinder "Associative strict birational group law on a scheme
  isomorphisms of dense opens universal left and right translations"`: eight hits
  on cartesian symmetry, absolute PartialMap setoid and scheme isomorphisms; no match.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.PartialMap,
  AlgebraicGeometry.Scheme.RationalMap"`: twelve hits on the absolute quotient,
  restriction and representatives. Their existing over-S classes do not impose
  fibrewise density. The absolute API is insufficient for this relative notion.
- `msearch.py ... grep "StrictBirational|FibrewiseDense|FiberwiseDense|RelativeRational"
  AlgebraicGeometry`: zero Mathlib hits; a second grep with birational/strict law
  also had zero hits. Exact outputs are recorded in both new nodes' mathlib_searches.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for these names and concept variants:
  no relative birational-law API. `grep -rn` of the item id in WeilConjectures: none.
- `rg -l` of the DAG for strict birational law and birational self maps: strict-law
  theorem nodes, but no definition node. `tools/blueprint_refs.py search
  'strict birational'`: 0 blueprint nodes. Its ancestor command returns None.
  The latest blueprint text search likewise has no strict-law definition.

There is no STATEMENT-DISPUTED flag, statement correction, or unusable recorded
interface. The source and node agree. All three delivered files compile cleanly
through scompile.py, with no warnings besides the permitted postponed proof.

## Second reading by Q131

The dispatcher prohibits starting other agents; this is a second pass by the same
worker, not a claim of an independent worker review. The maintainer's independent
review remains required. I reread the item node and all three files side by side.
The first pass accidentally made relative partial maps extend Mathlib's absolute
PartialMap, requiring an extra density proof on the total space; I removed that
field and use precisely fibrewise-dense actual open-domain morphisms. I also fixed
the structure morphisms of square and cube: the Over pullback is over Y or T,
whereas these products must be regarded over S by composing their last projection.
The final statement retains the Noetherian/normal/strictly-henselian ring, relative
separatedness, smooth finite type, nonempty fibres, all six strictness densities,
associativity on a dense triple-product open, the exact chart quotient, canonical
composition and base-change characterizations, naturality, injectivity, and the
compatibility for every representing multiplication domain. In particular I checked
the product order f∘g and τ_a∘τ_b, and the left-translation pairing's first coordinate
a∘pr_T and second coordinate pr_Y. No data is `sorry`; the only postponed theorem
is the assigned node. The extra existence conjuncts for composite/pulled-back charts
make their canonical characterizations effective, rather than vacuous implications.

## New nodes

`def-sfb-relative-birational-maps`: Relative partial maps on fibrewise dense opens,
their quotient, actual birational charts and their quotient, plus predicates
characterizing composite and pulled-back charts. Source: BLR 2.5 and 5.2 before
Lemma 4. Mathlib's absolute rational-map API has no fibrewise-density restriction;
no project or DAG definition node supplies it. The module contains real domain,
morphism, isomorphism and quotient data, with no arbitrary-map substitution or choice.
All searches with exact returned output are in its node. Its primary declaration is
`AlgebraicGeometry.RelativeBirational.SelfMap`; all helpers are listed in declarations.

`def-sfb-strict-birational-law`: Representative data for an associative relative
rational multiplication, both strict isomorphisms and every projection-density
condition, triple-product associativity, and the predicate for the canonical
pulled-back universal left-translation chart. Source: BLR 5.2 Definition 1 and
construction before Lemma 4. The same searches find only theorem nodes repeating
this notion, not a carrying definition or usable library declaration. It builds on
the relative-map node and existing scheme/base-change conventions. Its primary
declaration is `AlgebraicGeometry.RelativeBirational.StrictLaw`; all helpers are listed.
