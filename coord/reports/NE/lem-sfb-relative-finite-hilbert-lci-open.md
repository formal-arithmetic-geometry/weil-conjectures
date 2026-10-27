## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertLciOpen` states
`AlgebraicGeometry.RelativeFiniteHilbert.lci_open`, with proof `sorry`.
It supplies two explicit helper definitions owned by this node: `lciGroupoid`
equips the recorded full subcategory `Lci` with the inherited projection, and
`lciInclusion` is its actual inclusion into `groupoid`. Their data contain no
`sorry`, choices of objects, or additional mathematical assumptions.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme S is `{S : Scheme.{u}}`; test schemes are `Over S`.
  The explicit universes `u v₁ w₁ v₂ w₂` permit different object and morphism
  universes for X and Y. No equality of those universes is imposed.
- The morphism of groupoids is `F : BasedFunctor X Y`, where X and Y are
  `BasedCategory` objects over `Over S`.
- The stack assumptions are `hX : IsFppfModuliStack X` and
  `hY : IsFppfModuliStack Y`. These use the fppf topology, fibred groupoids,
  effective descent and unique gluing of arrows, rather than the etale-only
  `IsModuliStack` predicate.
- Representability by algebraic spaces is `hF : IsRepresentableByAlgebraicSpaces F`.
  `R` fixes the representatives `Representative (F := F) T y` for every test
  scheme and object y, as the definition dependency expressly permits. These
  consist of the space, its projection and a based equivalence with the explicit
  relative fibre, including projection compatibility. R is representative data,
  not a hypothesis of algebraicity or an independently supplied induced map.
- Flatness and local finite presentation of every represented projection are
  `hflat : FlatLfp R`. Read in the dependency, this is the conjunction of the
  two separate `SpaceProperty` tests on each `(R T y).projection`, using the
  node's existential surjective etale scheme-chart convention.
- Every integer d at least one is `d : ℕ+`. H_d is exactly `groupoid F d hX hY`;
  L_d is exactly the existing `Lci (d := d) hX hY hF R hflat` with its base
  functor, named `lciGroupoid`. No arrows are discarded from the full subcategory.
- The first and second conjuncts assert `IsFppfModuliStack` for H_d and L_d,
  respectively. Thus both descent conclusions are present.
- The inclusion j_d is the explicit `lciInclusion`, whose underlying functor
  is `ObjectProperty.ι` and whose projection equality is `rfl`.
- A scheme T and an object xi over it are encoded without redundancy by
  `A : RelativeFiniteHilbert F d`, with `T = A.T`. Every fibre object is such
  an A, and this quantification includes every T and xi.
- The open representative is `W : Over S` and `i : W ⟶ A.T` with
  `IsOpenImmersion i.left`. This is precisely an open subscheme, expressed by
  its open immersion rather than a fixed representative of its open subset.
- The relative two-fibre is the dependency's explicit
  `relativeFiber (F := lciInclusion ...) A`. An object is an lci Hilbert object
  equipped with its arrow to A over the test map, equivalently the stated
  identification with A's pullback. Its canonical base projection is
  `relativeProjection`. This is the inverse-comparison convention already
  fixed by the dependency, and retains automorphisms, not isomorphism classes.
- The based functor `e` from `discreteModuli (yoneda.obj W)` and
  `e.toFunctor.IsEquivalence` assert natural scheme representation. The equation
  for every z identifies its structural projection with `yoneda.map i`.
  The `eqToHom` only transports along the given based-functor base equality.
  This compatibility is essential: representation is over T, not an arbitrary
  equivalence of total categories.
- For every `T' : Over S` and `g : T' ⟶ A.T`, the final iff uses the recorded
  canonical `A.pullback hX.1 hY.1 g` and `IsLciObject` with its representative.
  The right side `∃ f : T' ⟶ W, f ≫ i = g` is factorization through the same
  open. The left side tests the canonical induced map for both unramifiedness
  and lci; it adds no arbitrary map or geometric hypothesis.
- Neither surjectivity of F nor algebraicity of X or Y occurs as a binder.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`, with the over topology from `Mathlib.CategoryTheory.Sites.Over`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `IsRepresentableByAlgebraicSpaces`,
  `discreteModuli`; the based-category and explicit relative-fibre conventions
  were read in full. `IsModuliStack` is etale-only and is deliberately not used.
- `Sheaf.CategoryTheory.SiteStackification`: `CategoryTheory.IsFppfModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale` and `IsSurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids`:
  `RelativeFiniteHilbert`, `groupoid`, `base`, `Representative`, `FlatLfp`,
  `SpaceProperty`, `SchemeLci`, `IsLciObject`, `Lci`, `pullback`, `inducedMap`,
  `relativeFiber`, `relativeProjection`. Their signatures and docstrings,
  including the comparison and representative data, were read.
- The size-convention node is metatheoretic; its recorded instruction is to
  bind the universes explicitly, which this file does.

The single public import exports the statement-dependency interfaces above.
Available proof dependencies are imported privately: the algebraic-space fibre
product theorem, generic base-change of precoverings, and the finite-morphism
properness/finite-fibre API. The three proof inputs without Lean records
(`lem-sfb-finite-locally-free-fppf-descent`,
`lem-sfb-space-closed-source-unramified-base-open`, and
`lem-sfb-space-relative-lci-parameter-open`) are named in the complete proof
sketch, and have no module to import. They are proof inputs only; nothing in
this statement requires inventing their interfaces.

Sources opened: `literature/stacks-project/criteria.tex`, the construction
`equation-relative-map` and Lemma `lemma-lci-locus-stack-in-groupoids` (06CL),
and `examples-stacks.tex`, the finite Hilbert construction and
`lemma-hilbert-d-stack` (05WB). The five-step docstring follows the node's proof:
cover/object/arrow descent, identification under base change, intersection of
parameter opens, compatible open representation, and descent of the full
subcategory by joint surjectivity.

Edge cases checked before writing: d=1 is included, while d=0 is excluded by
both the node and `ℕ+`. The empty base, empty test scheme, empty open and whole
open are all allowed by `Over S` and `IsOpenImmersion`; no Nonempty or
surjectivity premise is added. For the empty test scheme the factorization and
empty-source membership remain meaningful. Nonreduced bases and arbitrary base
changes are allowed. Identity base changes use the recorded pullback, with no
choice of an unrelated lift. A zero-dimensional or singular representative is
not excluded. No smoothness, Noetherian, separation, finite-type-base or
algebraic-stack hypothesis is imposed.

Searches actually run using msearch.py (NE, this item):

- LeanFinder: "The finite Hilbert groupoid of a flat locally finitely presented
  representable morphism of fppf stacks is a stack and its unramified local
  complete intersection locus is an open substack". Eight results, headed by
  `UniversallyOpen.of_flat`, `Algebra.isOpen_unramifiedLocus` and
  `IsOpenImmersion.of_flat_of_mono`; no Hilbert stack theorem.
- Loogle: "RelativeFiniteHilbert, IsFppfModuliStack, IsOpenImmersion".
  Zero results, reporting unknown identifier RelativeFiniteHilbert.
- Mathlib grep: `Hilbert|IsFppfModuliStack|lciLocus`, subdirectory
  AlgebraicGeometry. Zero hits.
- LeanSearch: "finite Hilbert stack unramified local complete intersection open
  immersion". Eight results about open immersions, including IsOpenImmersion
  and its stalk characterization; no finite Hilbert stack theorem.
- `rg -n 'RelativeFiniteHilbert|Hilbert.*[Ss]tack|hilbert.*[Ll]ci'` in
  `lean/WeilConjectures` and `lean/Sheaf`: only the recorded Hilbert definition
  module and its use in AffineLciConormalSplitting; no statement of this node.
  `grep -rn 'lem-sfb-relative-finite-hilbert-lci-open' lean/WeilConjectures`
  returned no matches. No second definition or existing exact theorem found.

No statement correction, new node, unusable dependency, or disputed statement.
The existing CompactObject example is a withdrawal stub; its node directs to
`WeilConjectures.CategoryTheory.CompactObject`, whose actual module header and
source/docstring conventions were read instead.

Validation: scompile.py compiled the sandbox and final module cleanly against
published live sources. The first probe needed an explicit F argument on
`relativeProjection`; this was supplied and the second compile passed in about
four seconds per module, without warnings. The only postponed theorem in this
module is `lci_open`.

## Second reading by NE

Author's second reading, as the dispatcher prohibits other agents; independent
review is the maintainer's delivery review. I reopened the node and final file.
The conjunction has both H_d and L_d stack assertions, not only the latter.
The positive degree and both source-stack assumptions match. `hF`, R and hflat
use precisely the recorded representability and two-chart interfaces. The
helper's underlying objects and arrows reduce to the recorded full Lci
subcategory. For the open conclusion I checked that the equivalence's target
is the relative fibre of the actual inclusion, and that the displayed equation
uses that same inclusion and the same open map i. The last iff quantifies over
all test maps and uses the recorded canonical pullback, with the representative
at the pulled-back object's y. The open is allowed to be empty or the entire
base. No missing clause or extra geometric hypothesis was found. No mathematical
change was needed during this reading.
