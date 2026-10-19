## Worker report

The module `lean/Sheaf/CategoryTheory/AccessibleFunctorPresentabilityRanks.lean`
states `CategoryTheory.accessible_functor_presentability_ranks`.  It uses Mathlib's
`CategoryTheory.IsLocallyPresentable`, `CategoryTheory.IsCardinalLocallyPresentable`,
`CategoryTheory.IsCardinalPresentable`, `Cardinal`, and
`CategoryTheory.Functor.IsCardinalAccessible` for the ordinary categorical notions.
The powers inequality is written explicitly, so the statement does not silently use
Mathlib's separately defined `Cardinal.SharplyLT` predicate.

The hypotheses render the node as follows.  `A` and `D` are object types in the
independent object universes `u₁` and `u₂`, each with `Category.{v}` structure and
`IsLocallyPresentable.{v}`.  `alpha : Cardinal.{v}` has `[Fact alpha.IsRegular]`,
`H : A ⥤ D`, and `[H.IsCardinalAccessible alpha]`, which is preservation of every
small `alpha`-filtered colimit in Mathlib's ordinary-category encoding.  The first
conclusion gives `rho : Cardinal.{v}` with a regularity witness and `alpha ≤ rho`.
For every regular `tau`, the sharp-rank premise is `rho < tau` together with
`∀ a b, a < tau → b < rho → a ^ b < tau`.  Under it the conclusion says that both
categories are `IsCardinalLocallyPresentable` at `tau`, and that every
`tau`-presentable `P : A` has `H.obj P` tau-presentable in `D`.

The final clause quantifies every regular `sigma` with `rho ≤ sigma` and every
cardinal bound.  It supplies a regular `tau` above the bound and `sigma`, satisfying
`∀ a b, a < tau → b < sigma → a ^ b < tau`, and repeats the same two local-
tau-presentability conclusions and the preservation of tau-presentable objects.
The existential regularity witness `hTau` is passed explicitly to the Mathlib
predicates in this final clause; this is definitionally the same assertion as the
first clause's typeclass form. The first universal clause also proves these properties
for every `tau` sharply above any `sigma ≥ rho`: restrict its exponents to `b < rho`,
and use `rho ≤ sigma < tau`. Thus the final clause retains the universal claim about
all such upper ranks, as well as their unbounded existence.

The sole statement dependency is the recorded Mathlib declaration
`CategoryTheory.Limits.colimit` in `Mathlib.CategoryTheory.Limits.HasLimits`
(node `def-weil-pbc-category-colimit`).  Its `Cocone`, `IsColimit`, `colimit.desc`,
and filtered-category interfaces are the universal-property notion named by the
source statement; no private colimit definition was introduced. I read its full
signature and docstrings in `HasLimits.lean` (the `to_dual`-generated colimit,
cocone, and `colimit.desc` declarations), together with the `Cocone` and `IsColimit`
structures in `Limits/Cones.lean` and `Limits/IsLimit.lean`.

The available proof dependency declarations are imported without `public`:

* `Mathlib.CategoryTheory.Presentable.Directed`:
  `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`.
* `Mathlib.CategoryTheory.Limits.Final`:
  `CategoryTheory.Functor.Final.isColimitWhiskerEquiv`.
* `Mathlib.CategoryTheory.Presentable.StrongGenerator`:
  `CategoryTheory.IsCardinalLocallyPresentable.of_le`.
* `Mathlib.CategoryTheory.Presentable.Limits`:
  `CategoryTheory.isCardinalPresentable_of_isColimit`.
* `Mathlib.SetTheory.Cardinal.Regular`: `Cardinal.isRegular_succ`.
* `Mathlib.SetTheory.Cardinal.HasCardinalLT`: `HasCardinalLT.exists_regular_cardinal`.
* `Mathlib.CategoryTheory.Limits.Types.Filtered`: the recorded filtered-colimit
  elementwise comparison declarations.

The object-presentability-rank dependency is already provided by the public
`Mathlib.CategoryTheory.Presentable.LocallyPresentable` import, specifically
`CategoryTheory.instIsPresentableOfIsAccessibleCategory`. The sharp-filtered-poset-
subsets node has no recorded module or Mathlib match, so it cannot yet contribute
a proof import. It is a proof dependency only and no unstated notion from it is
needed in this signature.

I checked the empty-family case in the large-rank clause: the statement imposes no
nonemptiness on a generating family and has an independent cardinal bound.  I also
checked `alpha = aleph0`: Mathlib regularity includes infinitude, and
`IsCardinalFiltered J aleph0` is equivalent to ordinary filteredness. The empty
indexing category is correctly excluded from filteredness by the empty test
diagram; it is still included among colimits required by local presentability.
Thus an empty category cannot accidentally satisfy local presentability. The
zero bound and exponent `b = 0` are retained without exceptions. The identity
functor is covered. A constant functor to an infinite set preserves filtered
colimits but need not preserve finitely presentable objects, so the conclusion
correctly asserts no preservation at the input rank `alpha`. No characteristic,
object-universe equality, or nonempty-index hypothesis was added.

Searches made:

* `msearch.py ... leanfinder`: query "An accessible functor between locally presentable
  ordinary categories sends presentable objects to presentable objects at all sufficiently
  large sharply larger regular cardinals"; eight hits, including the object-presentability
  instance and functor accessibility primitives, with no uniform-rank theorem.
* `msearch.py ... loogle '\"IsCardinalPresentable\", \"IsCardinalAccessible\"'`: six hits,
  including coyoneda characterizations and density instances; no matching statement.
* `msearch.py ... grep "preserv.*[Pp]resentab|strongly.*accessible|sharply"
  CategoryTheory/Presentable`: thirteen hits, including the presentability adjunction
  theorem and sharply-smaller definitions. Inspection of `Presentable/Adjunction.lean`
  shows it assumes an adjunction with an accessible right adjoint, which this node
  does not assume. No exact theorem.
* `rg -n "accessible.*presentability|PresentabilityRanks|presentability ranks|
  lem-coef-accessible-functor"` in the project and source: no existing declaration of
  this node.
* `grep -rl "lem-coef-accessible-functor-presentability-ranks" dag/nodes`: found this split
  node and its citer, with no existing Lean declaration.

No statement correction or `STATEMENT-DISPUTED` flag is needed.

Source validation: opened the current online HTT PDF at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf, printed pp. 425--427 and 819.
Remark the project server supplies a uniform rank by bounding images of a small collection
of generators; Proposition the project server and Definition A.2.6.3 give the sharp upper-rank
construction. Mathlib's `Cardinal.SharplyLT` has a different categorical definition,
so the precise power inequality of the node remains inline. The declaration docstring
contains the node's nine-step ordinary-category proof, including the empty-family bound,
reindexing, cocone comparison, retract, and arbitrarily large rank calculations.

## Second reading by Q39

I opened the node and the complete declaration in
`lean/Sheaf/CategoryTheory/AccessibleFunctorPresentabilityRanks.lean` and matched the
statement item by item. The fixed universe and ordinary categories are rendered by
`{A : Type u₁}`, `{D : Type u₂}`, `[Category.{v} A]`, and `[Category.{v} D]`; the
`Cardinal.{v}` parameters use the same small-cardinal universe as the category
interfaces. Local presentability is exactly `[IsLocallyPresentable.{v} A]` and
`[IsLocallyPresentable.{v} D]`. The infinite regular input rank is
`(alpha : Cardinal.{v}) [Fact alpha.IsRegular]`, and preservation of small
`alpha`-filtered colimits is exactly `[H.IsCardinalAccessible alpha]` for
`H : A ⥤ D`. No extra finiteness, size, or nonemptiness hypothesis is present.

The first conclusion clause is rendered by
`∃ rho, Fact rho.IsRegular, alpha ≤ rho`, followed by universal regular `tau`.
Its premise is precisely `rho < tau` together with
`∀ a b, a < tau → b < rho → a ^ b < tau`, which is the node's inline
definition of `rho ≪ tau`. Its conclusions are, in order,
`IsCardinalLocallyPresentable A tau`, `IsCardinalLocallyPresentable D tau`, and
preservation of every `tau`-presentable `P` under `H.obj`. The second clause has
universal regular `sigma` with `rho ≤ sigma`, an arbitrary cardinal `bound`, and
an existential regular `tau` satisfying `bound < tau`, `sigma < tau`, the exact
power inequality with exponent bound `b < sigma`, and the same two local-rank and
object-preservation conclusions. The explicit `hTau : Fact tau.IsRegular` is
passed to the predicates with `@`, so it states the same rank assertion without
introducing a stronger assumption.

The node's only statement dependency, `def-weil-pbc-category-colimit`, is the
recorded Mathlib `CategoryTheory.Limits.colimit`/`Cocone`/`IsColimit` interface;
the theorem's proof docstring uses it only for the universal-property argument.
All proof dependencies listed by the node are imported as their recorded Mathlib
or project interfaces in the docstring plan; no private replacement was added.

I checked edge cases: an empty generator family is allowed (the separate cardinal
bound still supplies `rho`), zero cardinal bounds and exponent `b = 0` remain in
the universal inequalities, `alpha = ℵ₀` is covered by Mathlib regularity and
cardinal filteredness, and the identity and constant-functor cases are not
excluded. Empty indexing categories are excluded only where filteredness itself
requires nonemptiness, while arbitrary small colimits in local presentability are
unchanged. The independent object universes `u₁,u₂` are retained and no universe
equality is imposed.

For the one-definition-per-notion check I searched Mathlib and the source project
with `msearch.py` LeanFinder and Loogle queries for accessible functors, presentability
ranks, and sharp cardinals, and used `rg`/`grep` over `Mathlib/`, `WeilConjectures/`,
and `lean/Sheaf/`. These found the ordinary presentability primitives and related
lemmas but no theorem matching this uniform-rank statement. The HTT source was read
at Lemma the project server, Proposition the project server, Remarks the project server and the project server (pp. 425--427),
and Definition A.2.6.3 (p. 819); its sharp relation agrees with the explicit power
inequality. The node and Lean statement are byte-for-byte identical. I found no
mismatch, made no changes, and added no `STATEMENT-DISPUTED` or statement correction.
