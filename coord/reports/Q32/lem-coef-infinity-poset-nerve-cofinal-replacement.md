## Worker report

The module [InfinityPosetNerveCofinalReplacement.lean](lean/Sheaf/CategoryTheory/InfinityPosetNerveCofinalReplacement.lean)
adds the canonical precomposition map on fixed-apex right-pinched mapping spaces,
the path-on-components predicate, and the statement-only theorem
`SSet.Presentability.infinity_poset_nerve_cofinal_replacement`.
The theorem follows the node clause by clause:

- `κ : Cardinal.{u}` and `hκ : κ.IsRegular` render the infinite regular cardinal.
- `K : SSet.{max (u + 1) v}` and `hK : IsKappaSmall κ K` render a κ-small simplicial set,
  with no quasicategory instance on `K`.
- `∃ B` and `(_ : PartialOrder B)` render the partially ordered set;
  `HasCardinalLT B κ` renders `|B| < κ`, including the empty-poset case.
- `φ : nerve B ⟶ K` renders the simplicial map from the ordinary nerve.
- `∀ E [Quasicategory E]`, `p : K ⟶ E`, and `T : E _⦋0⦌` render the sufficiently large
  quasicategory, arbitrary diagram, and chosen vertex. The universe is the common
  containing universe `max (u + 1) v`, as in the presentability definitions.
- `restrictionOnCoconeMappingSpace φ p T` is exactly `Enhanced.mappingSpaceMap` for
  `MonoidalClosed.pre φ`; its source is the right-pinched mapping space from `p` to the
  constant diagram at `T`, and its target has the canonically restricted endpoints.
  `Enhanced.IsWeakHomotopyEquivalence` renders the equivalence of Kan complexes.
- `∀ c, IsJoinedToRestriction ... c` renders the “in particular” clause. The predicate
  expands to a source vertex `a` and a target 1-simplex `γ` whose two faces are the
  restricted vertex and `c`, respectively, i.e. a path in the target mapping space.
- There is no colimit or existence hypothesis on `E`; only `[Quasicategory E]` occurs.

The helper declarations use the recorded dependency declarations from
`Sheaf.CategoryTheory.PresentableInfinityCategory` (`SSet.Presentability.IsKappaSmall`)
and `Sheaf.CategoryTheory.EnhancedDiagramsCones` (`SSet.Enhanced.mappingSpace`,
`mappingSpaceMap`, `diagramVertex`, `constantDiagrams`, and
`IsWeakHomotopyEquivalence`). The theorem explicitly asserts `KanComplex` for both mapping spaces.
The theorem's proof docstring records the complete eight-step five-map
last-vertex/first-vertex/injective-simplex/degeneracy-removal construction, the finite
embedded resolution for `κ = aleph_0`, the uncountable cardinal count, and the empty case;
all proof dependencies remain in the DAG and the proof is `sorry` as required at stage 2.

Edge cases checked against the source and node are `K = ∅` (take `B = ∅` and identity
restriction), a point (degenerate simplices show why the finite-resolution route is
needed), a finite embedded simplex, a two-point discrete simplicial set, a chain
`0 < 1`, and `κ = aleph_0` versus an uncountable regular cardinal. No nonemptiness of
`K`, `B`, or `E` was introduced.

Searches made:

- `rg -n 'poset.*nerve.*cofinal|CofinalReplacement|isKappaFiltered_iff_poset'` in
  `lean/Sheaf` and `WeilConjectures`: no matching declaration.
- `grep -rl 'lem-coef-infinity-poset-nerve-cofinal-replacement' dag/nodes`: found only
  the item and its citer records; no Lean declaration.
- `msearch.py Q32 lem-coef-infinity-poset-nerve-cofinal-replacement leanfinder
  'Every kappa small simplicial set admits a cofinal map from the nerve of a poset of
  cardinality less than kappa'`: eight hits, including
  `SSet.Finite.exists_epi_from_isCardinalPresentable`, `CategoryTheory.SimplicialNerve`,
  `CategoryTheory.nerve.representableBy`, `SSet.stdSimplex.isoNerve`, coskeletality,
  `CategoryTheory.nerveFunctor`, `CategoryTheory.nerve`, and nerve edge surjectivity.
  These concern presentations or nerves, with no cofinal poset replacement.
- `msearch.py ... loogle 'CategoryTheory.nerve'`: twelve hits for the nerve and its
  basic functoriality; no matching cofinal replacement theorem.
- `msearch.py ... grep 'cofinal|Cofinal|poset' AlgebraicTopology`: two hits in
  `Mathlib/AlgebraicTopology/SimplicialNerve.lean:18-19`, describing enriched homs as
  nerves of path posets; neither states cofinal replacement.

The reviewed Q34 report and the item source were read, including HTT Variants the project server
and the project server, Proposition the project server, Proposition the project server, and Remark the project server.
No statement correction or `STATEMENT-DISPUTED` flag is needed. The prior dry-run
failure was a shared-fetch wait; this delivery recreates the missing sandbox files and
reruns the wrapper checks.

Validation: `scompile.py` compiles the delivered module cleanly, with no warnings.
The dry run reached `OK (dry run)` at commit `2a4e12d8ed`; the final packet is checked
again after adding the explicit Kan clauses and complete proof docstring.
Proof-only imports are the four published proof dependency modules. The four simplex/
finite-resolution inputs have no recorded Lean declarations, so there are no modules
for them to import yet; the Mathlib nondegenerate decomposition is imported through
PresentableInfinityCategory. No new node or dependency-module repair is needed.

## Second reading by Q32

I read the item node, its HTT source place (Variants the project server--the project server,
Propositions the project server and the project server, and Remark the project server), and the delivered file
independently. The node's statement renders as follows, with the corresponding
Lean and verdict.

- The infinite regular cardinal is `κ : Cardinal.{u}` with
  `hκ : κ.IsRegular`; this is exactly the first two theorem binders, and
  `Cardinal.IsRegular` includes `aleph0 ≤ κ`, so the infinitude hypothesis is
  present.
- The arbitrary simplicial set and its smallness hypothesis are
  `K : SSet.{max (u + 1) v}` and `hK : IsKappaSmall κ K`. There is no
  `[Quasicategory K]`, matching the source and node.
- The replacement object is
  `∃ (B : Type (max (u + 1) v)) (_ : PartialOrder B), ...`; its size clause is
  `HasCardinalLT B κ`. This is the node's partially ordered set and
  `|B| < κ`, including `B = PEmpty` and the finite conclusion at
  `κ = Cardinal.aleph0`.
- The replacement map is `∃ (φ : nerve B ⟶ K)`, using Mathlib's ordinary
  nerve and a simplicial map exactly as in the node.
- The universal quantifiers are
  `∀ (E : SSet.{max (u + 1) v}) [Quasicategory E] (p : K ⟶ E)
  (T : E _⦋0⦌)`. Thus the target is a quasicategory in the common containing
  universe, with an arbitrary diagram and arbitrary chosen vertex; no
  colimit, presentability, nonemptiness, or other hypothesis is added.
- The source mapping space is
  `Enhanced.mappingSpace ((ihom K).obj E) (Enhanced.diagramVertex p)
  (((Enhanced.constantDiagrams K E).app _) T)`, which is the right-pinched
  mapping space from `p` to `Δ_K T`.
- The target mapping space has the restricted diagram and restricted constant
  endpoint, namely
  `Enhanced.mappingSpace ((ihom (nerve B)).obj E)
  (((MonoidalClosed.pre φ).app E).app _ (Enhanced.diagramVertex p))
  (((MonoidalClosed.pre φ).app E).app _
  (((Enhanced.constantDiagrams K E).app _) T))`. The second endpoint is the
  canonical precomposition image of `Δ_K T`, which is definitionally the
  constant diagram on `T` after the standard `constantDiagrams`/`curry`-
  precomposition identity; this is the canonical endpoint used by the
  restriction map and expresses `Δ_{N(B)}T` from the node.
- The two explicit `KanComplex` conjuncts render “equivalence of Kan
  complexes”; the next conjunct is
  `Enhanced.IsWeakHomotopyEquivalence
  (restrictionOnCoconeMappingSpace φ p T)`, with the helper definition being
  exactly `Enhanced.mappingSpaceMap` for precomposition by `φ`. This is the
  node's equivalence clause under the dependency's weak-homotopy-equivalence
  convention.
- The final conjunct quantifies every target vertex `c` and asserts
  `IsJoinedToRestriction ... c`. Its definition supplies a source vertex `a`
  and a target 1-simplex with faces the restricted vertex and `c`, so it is
  exactly the node's path-on-components (“in particular”) clause.

No hypothesis or conclusion is missing or strengthened. The source's empty
case is represented by `B` and `K` both empty and the unique map. The zero/
point cases, finite embedded simplices, a two-point discrete set, the chain
`0 < 1`, `κ = aleph0`, and an uncountable regular `κ` are all covered; no
nonemptiness of `K`, `B`, or `E` is assumed. The source's finite case is handled
in the proof docstring through the finite embedded-simplex resolution, while
the uncountable case uses the five-map construction and its cardinal count.

I searched the project's `lean/Sheaf` and upstream `WeilConjectures` with
`rg` for cofinal poset-nerve replacements, the DAG for duplicate declarations,
and ran the available `msearch.py` LeanFinder, Loogle, and grep queries in the
worker log. Mathlib's ordinary nerve and `Final` declarations do not state this
quasicategorical mapping-space replacement. The dependency declarations
`IsKappaSmall`, `constantDiagrams`, `mappingSpace`, `mappingSpaceMap`,
`diagramVertex`, and `IsWeakHomotopyEquivalence` were opened and are the ones
used by the file. No dependency has an unusable interface, no new definition
node is needed, and no repair note applies.

The only apparent syntactic difference from the prose notation is the target's
canonical restricted constant endpoint, required so that the precomposition
map has its actual type; the existing `constantDiagrams` curry/precomposition
identity identifies it with `Δ_{N(B)}T`. I made no code change after this
reading. `scompile.py` compiles the module cleanly with only the required
`sorry` proof.
