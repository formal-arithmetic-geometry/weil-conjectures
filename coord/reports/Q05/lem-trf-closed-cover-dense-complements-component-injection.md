## Worker report

The module `Sheaf.Topology.ClosedCoverDenseComplements` states
`Topology.exists_injective_components_of_closed_cover_dense_complements` with `sorry`.
It introduces no definitions and changes the item's node only in `lean`.
The statement follows Stacks Project, More on Morphisms, Tag 0554,
`lemma-irreducible-components-in-neighbourhood`, retaining the nowhere-dense
intersection hypothesis established before that proof's final paragraph.
The final sentence's weaker wording “not dense” is not substituted for the
item's dense-relative-complement hypothesis. No statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `T : Type u` and `[TopologicalSpace T]` introduce an arbitrary topological space.
- `I : Type v` and `[Finite I]` introduce an arbitrary finite index set, with an
  independent explicitly declared universe. There is no `Nonempty I` assumption.
- `E : I → Set T` is the given family of subsets of the ambient space.
- `h_nonempty : ∀ i : I, (E i).Nonempty` states that every covering piece is nonempty.
- `h_closed : ∀ i : I, IsClosed (E i)` states that every covering piece is closed.
- `h_cover : (⋃ i : I, E i) = Set.univ` states that the pieces cover all of `T`.
- `h_dense : ∀ i j : I, i ≠ j → Dense {x : E i | (x : T) ∉ E j}` states exactly
  that `E i \ E j` is dense in `E i`. The set in `Dense` has ambient type `E i`,
  carrying the induced subspace topology; membership in `E i` is provided by its
  subtype. By `dense_iff_closure_eq`, its closure in that subspace is the whole
  subspace. This is not density in `T`.
- `∃ (x : I → T)` provides the required indexed points.
- `∃ (K : I → irreducibleComponents T)` provides components of `T`, not just
  irreducible subsets or components of individual pieces. Each value is a subtype
  whose property asserts membership in Mathlib's set of maximal irreducible subsets.
- `∀ i : I, x i ∈ (K i : Set T)` supplies membership of each point in its component.
- `(K i : Set T) ⊆ E i` supplies containment of the selected component in its piece;
  consequently the selected point also belongs to `E i`.
- `∀ j : I, j ≠ i → x i ∉ E j` is the private-point assertion against every other
  piece. The reversal from `i ≠ j` in the density assumption has no mathematical effect.
- `Function.Injective K` is the component assignment's injectivity, equivalently
  the assertion that components with distinct indices are distinct. It expresses
  both the pairwise-distinctness assertion and the stated “in particular” injection
  without a second redundant conjunct.
- No irreducibility assumption is made on `E i`, and no Noetherianity, separation,
  generic-point, sobriety, or nonemptiness assumption is made on the ambient space.

Dependency declarations read and used:

- `def-weil-irreducible-components` is a Mathlib leaf, with no Lean record needed.
  Its recorded `irreducibleComponents` in `Mathlib.Topology.Irreducible`, lines
  104–108, is `{s | Maximal IsIrreducible s}`. The `IsIrreducible` definition
  (lines 48–53) includes nonemptiness, and
  `isPreirreducible_iff_isClosed_union_isClosed` gives the closed-cover formulation.
  `isClosed_of_mem_irreducibleComponents` gives closedness of components.
- The proof dependency `lem-sc-irreducible-components-cover` is also a Mathlib leaf.
  Its exact recorded declarations in the same module were read:
  `exists_mem_irreducibleComponents_subset_of_isIrreducible` (lines 126–133),
  `mem_irreducibleComponent` (lines 147–149), and
  `irreducibleComponent_mem_irreducibleComponents` (lines 158–160).
  They give maximal extensions and a component containing each point in an arbitrary
  topological space. The single public import provides both statement and proof
  dependencies; no second copy or extra dependency module is needed.

Edge cases checked before writing:

- Empty `I`: its union is empty, so the covering assumption forces `T` empty.
  Functions with empty domain exist even when their codomains are empty, so both
  existential families and injectivity are available without any nonempty instance.
- Singleton `I`: the density hypotheses are vacuous and the one piece is the
  nonempty ambient space, which may be reducible. A component containing any chosen
  point suffices, so irreducibility of the piece must not be imposed.
- Empty `T` with an inhabited `I` is ruled out by `h_nonempty`, as the node requires.
- For equal nonempty pieces at two distinct indices the relative complement is empty
  and cannot be dense in their nonempty subspace. Thus the hypothesis correctly
  excludes this failure of distinctness.
- Crossing components may share points; the conclusion only chooses a private point
  in each piece, and does not assert that the components themselves are disjoint.
- Non-Noetherian and non-sober spaces are allowed: component existence uses the
  general maximal-extension theorem, not generic points or finite decomposition.

Searches actually performed for an existing statement:

- `msearch.py`, LeanFinder query: “A finite closed cover by nonempty subsets with
  dense pairwise complements admits distinct irreducible components and private
  points in each member”. Eight hits included `isIrreducible_iff_sUnion_isClosed`,
  Noetherian finite decomposition results, and the disjoint-cover subsingleton result.
  None states private-point selection together with this component injection.
- `msearch.py`, Loogle query: `"irreducibleComponents", "IsClosed"`.
  One hit: `isClosed_of_mem_irreducibleComponents`, only closedness of a component.
- `msearch.py`, grep query:
  `(irreducibleComponents|irreducibleComponent).*(inject|cover|dense)|(inject|cover|dense).*(irreducibleComponents|irreducibleComponent)`
  in Mathlib's `Topology`: no hits.
- `msearch.py`, LeanSearch query: “Finite closed cover with dense pairwise relative
  complements admits an injection from its indices into the irreducible components”.
  Eight hits: component definition, Noetherian finite-component results, clopen cover
  results, and scheme finite subcovers. None has the item's hypotheses and conclusion.
- `rg -n` for `irreducibleComponents|component.*injection|dense.*complement` in the
  project's upstream and Sheaf topology directories found only unrelated stratification
  and closed-orbit results. The component/injection/cover/dense regular expression
  above was also run over all of `lean/WeilConjectures` and `lean/Sheaf`; results
  concern Jacobson maps, dense-open component modifications, and curve normalization.
  None states this arbitrary-space finite-cover theorem.
- `rg -n` for `closed.cover.*dense|dense.*closed.cover|exists_injective_irreducibleComponents|dense_sdiff`
  over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found no match. `grep -rn` for this item's blueprint id in `lean/WeilConjectures`
  also found no match. The chosen declaration name was checked against these sources.

The theorem docstring records all five proof steps, the named component-existence
input, and the finite closed-cover induction, with their Stacks sources.
There are no disputed statements, new nodes, or dependency repairs.

Validation: the module is checked through the prescribed `scompile.py` server
wrapper; the dry run and final delivery use `deliver2.py`. No local or global
library build is run, and no shared repository file is edited directly.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
