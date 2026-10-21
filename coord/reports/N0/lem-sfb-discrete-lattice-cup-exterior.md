## Worker report

The module `Sheaf.CategoryTheory.DiscreteLatticeCupExterior` states
`Profinite.DiscreteLatticeCup.discrete_lattice_cup_exterior`: the specified coordinate-cup
map is invertible in the ordinary derived category of internal modules. Definitions
construct the finite exterior complex and its actual arrow from the recorded connecting
classes and derived cup product. No statement correction, dependency repair or new node
is needed. Every theorem proof is `sorry`; every definition has actual data. The only
choice constructs a coordinate character from an existence-and-uniqueness assertion
whose sectionwise equations determine that character uniquely.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Any commutative condensed ring on the small coherent profinite site | `A : CategoryTheory.CondensedBar.Ring.{u}`, the existing `CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1})`; this bundles precisely `Profinite.CondensedRing` with its commutativity proof |
| Ordinary internal module derived category | `Modules A` is the recorded internal `Mod` category; every derived object is explicitly `DerivedCategory.{u+1} (Modules A)` |
| Every rank r >= 0 | `r : ℕ`, with no positivity assumption |
| D = Z^r discrete | `Lattice.{u} r = ULift.{u} (Multiplicative (Fin r → ℤ))`, with the inherited discrete integer/product/lift topology and group structure |
| Trivial action on R | Recorded `cohomology A (Lattice r)` is `derived A (Lattice r)` applied to `coefficient`, the single complex on the existing trivial action of the regular module |
| Coordinate character n ↦ n_i 1_R on every test object | `coordinateCharacter_exists` uniquely specifies `Character.app` on every continuous lattice section with constant ith coordinate; the named character's naturality determines all other sections by the finite clopen fibre cover. The docstring supplies the gluing construction and proof. Fin r labels coordinates 0 through r-1 in their original order |
| Positive connecting class delta_i : R[-1] → RΓ(R[0]) | `coordinateClass` is exactly the dependency's `characterClass (coordinateCharacter ...)`, which applies the derived functor to the unipotent extension boundary and shifts down by one |
| Finite direct sum over subsets, summand R[-card I] | `exteriorComplex` is the actual finite biproduct, indexed by `Finset (Fin r)`, of regular-module single complexes shifted by `-(I.card : ℤ)`; `exteriorObject` is its localization |
| Zero differential; degree q indexed by q-element subsets | Every summand is a shift of a degree-zero single complex, so all differentials vanish and only subsets of cardinality q contribute in degree q |
| Empty subset is the unit | The empty-list branch of `orderedCup` is `shiftFunctorZero.hom`, followed by `baseUnitIso.inv` and the recorded `cupUnit` |
| Increasingly ordered cups on every nonempty subset | `subsetCup` sorts I by the ordinary order on Fin r, then `orderedCup` recursively composes the coordinate connecting classes with the recorded `cup`. `splitShift` uses the canonical derived `shiftTensorShiftIso` and regular-unit multiplication, without a permutation |
| The actual map chi | `cupMap` is the localization's finite-biproduct comparison followed by the biproduct descent of `Q.commShiftIso` and each `subsetCup`. It has exactly the stated component on every subset |
| Isomorphism in D(Mod_R), retaining the map | `discrete_lattice_cup_exterior : IsIso (cupMap A r)` |
| Rank zero is the identity R[0] | `rankZeroInclusion` is the empty-subset single-complex inclusion. `rank_zero_identity` retains the target's unit-normalized isomorphism to the regular degree-zero object and states that this inclusion followed by chi is its identity |
| Zero ring allowed; no characteristic, completeness or flatness | The ring binder has no nontriviality or supplementary assumption and all constructors use finite sums, integral multiples, units and ordinary derived tensor |

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`; the generic
  action, module morphisms and category, specialized by the recorded `Modules` alias.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.Modules`,
  `ActionModule`, `trivial`, `Invariants`; these are the internal sectionwise action and
  normalized invariant-adjunction interfaces used by the calculus.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `singleFunctor` and the localization's additive/shift structures.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`. Its arbitrary-ring
  alias is equivalent to the bundled commutative input already used by the calculus;
  no continuous-function presentation of A is imposed.
- `def-weil-size-convention` is a convention record with no declaration. Explicit u,
  site `Profinite.{u}`, coefficient size u+1 and derived morphism size u+1 realize it.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus` publicly supplies
  `CondensedBar.Ring`, `Modules`, `sectionRing`, and
  `CondensedDerivedRestriction.Character`, `characterClass`, `cohomology`, `cup`,
  `cupUnit`, `baseUnitIso`. Read its source and the defining sources
  `CondensedEquivariantBarData`, `CondensedDerivedCup`, `CondensedUnipotentClass`,
  including the exact positive extension boundary and its shift convention.
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`:
  `DerivedCategory.shiftTensorShiftIso`, with its K-flat ordinary derived-tensor
  normalization, used for the actual source identifications of the cup products.
- `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution` is a non-public proof import;
  read its `Subsets`, `KoszulModel`, `derivedInvariants` and main theorem. This proof
  interface uses a larger localization universe, so it is deliberately not used to
  replace or restrict the statement's existing restriction-calculus derived category.
- `WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison` is a non-public
  proof import; read `DerivedCategory.triangleOfSESδ_eq_degreewiseSplit` and its full
  source/proof docstring.
- The proof dependency `lem-sfb-lattice-koszul-triangulated-cup-comparison` currently
  has no Lean record or source module. Its statement is used in the natural-language
  proof; no import can be supplied until that proof-only prerequisite is stated.

Edge cases checked before writing: r=0 has exactly the empty subset and its cup is the
unit, with the explicit identity normalization retained; r=1 has the unit and one
positive coordinate class; repeated indices are absent because the labels are finite
subsets, and sorting introduces no permutation of the ordered product. Negative and
out-of-range cochain degrees have only zero terms. Empty profinite test objects have
unique ring sections, so the coordinate-character characterization is consistent even
when every integer satisfies its vacuous constant-coordinate condition. The zero ring
has zero regular module and zero derived objects; its unique arrow is invertible.
No division by factorials, 2, or any other integer occurs; characteristic 2 is allowed.
The universe lift retains the same discrete group and excludes no rank or coefficient.

Searches made for an existing statement (all results were read):

- `msearch.py` leanfinder: "Ordered coordinate cup products identify the zero differential
  exterior complex with derived invariants for a discrete integer lattice acting
  trivially on a condensed ring". Eight hits, including continuous-cohomology face-map
  identities and `groupCohomology.d₀₁_eq_zero`; none is this internal-module derived map.
- `msearch.py` loogle: `"groupCohomology", "cup"`. Zero hits.
- `msearch.py` grep: `(cup|koszul|exterior).*(invariant|cohomology)` in
  `RepresentationTheory`. Zero hits.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `lattice.*[Cc]up`, `[Cc]up.*[Ee]xterior`, `coordinateCharacter`, and the selected
  declaration names. No existing declaration states the item. The dense-lattice
  consumer only names this item in its proof docstring. The rational-polynomial
  exterior complexes have ordinary ring coefficients and a different statement.
- Read the recorded Mathlib signatures for `Finset.sort`, `Finset.length_sort`,
  `biproductComparison`, and the single/shift/localization API before constructing
  the actual finite-sum arrow.

Validation: all compilation uses `scompile.py` against the live published server build;
no shared source or tool was edited and no local/global library build was run.

Elaboration repair: the regular-unit splitting and the shifted tensor splitting are
constructed directly as canonical morphisms. This avoids generating unused composite
isomorphism proof fields. No timeout limit or mathematical hypothesis was changed.

Final single-file server compilation succeeded without warnings or errors under both
names: sandbox 54.2 seconds, final library module 50.9 seconds, each within the unchanged
60-second limit. No diagnostic commands, profiling options or heartbeat overrides remain.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
