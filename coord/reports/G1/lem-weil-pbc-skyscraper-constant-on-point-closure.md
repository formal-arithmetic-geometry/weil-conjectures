## Worker report

The module `lean/Sheaf/Topology/SkyscraperConstantOnPointClosure.lean` states
`TopCat.skyscraper_constant_on_point_closure`; its sole proof is `sorry`.
The node has no statement dependencies. No node correction, new definition node,
or dependency module is needed: the node itself gives the two sheaves' concrete
section descriptions, which are rendered using Mathlib notions rather than new definitions.

Hypothesis and clause correspondence:

- An arbitrary topological space, point and set are `(Y : TopCat.{u}) (y : Y)
  (A : Type u)`. There are no separation, finiteness, nonemptiness of A, or
  discreteness hypotheses. The common universe is arbitrary; both carriers can
  be placed in a common universe. `open Classical in` supplies the decidability
  used internally by Mathlib's skyscraper, without a mathematical hypothesis.
- W is exactly `closure ({y} : Set Y)`. The domain V intersect W is the subtype
  `{w : Y // w ∈ V ∧ w ∈ closure ({y} : Set Y)}`, with its induced topology.
  No independent W or inclusion map is supplied that could vary from the node.
- The source sheaf is Mathlib's `skyscraperSheaf y A`: its underlying presheaf
  assigns `if y ∈ V then A else terminal (Type u)`. Its restriction is the
  identity after type transport when the smaller open contains y, and the
  unique terminal map otherwise, exactly the node's one-point-set prescription.
- Clause (1) is the first conjunct, for every `V : Opens Y`:
  `((V : Set Y) ∩ closure ({y} : Set Y)).Nonempty ↔ y ∈ V`.
- Clause (2) is the second conjunct: when `y ∈ V`, every `g : LocallyConstant
  {w : Y // w ∈ V ∧ w ∈ closure ({y} : Set Y)} A` satisfies
  `∃ a : A, ∀ w, g w = a`. Mathlib's local constancy is equivalent to having
  an open neighbourhood at each point on which the map is constant
  (`IsLocallyConstant.iff_exists_open`). No topology on A is required.
- The target sheaf is specified by existential `F : Y.Sheaf (Type u)` and
  section equivalences `e V` with exactly those locally constant maps. The
  equation `e U (F.obj.map i.op s) = LocallyConstant.comap ... (e V s)`
  for each inclusion `i : U ⟶ V` explicitly prescribes restriction as restriction
  of functions. Thus this is the full concrete direct-image sheaf from the
  node, expressed by natural identifications of its section sets. F is not an
  arbitrary isomorphic sheaf with unspecified identifications or restrictions.
  Existential F includes the assertion that this section presheaf is a sheaf;
  all the identifications and their naturality are conclusions, not hypotheses.
- Clause (3) gives `kappa : skyscraperSheaf y A ≅ F`, a sheaf isomorphism, and
  `∀ V, Function.Bijective (kappa.hom.hom.app (op V))`. Under e these are also
  the bijections of the node's concrete section sets.
- When `hy : y ∈ V`, `cast (if_pos hy).symm a` is a in the source section set;
  its image under `e V` is required to equal `LocallyConstant.const _ a`.
- When `y ∉ V`, the last conjunct requires the image of every source section
  to equal every locally constant map on the intersection. Clause (1) makes
  this domain empty, so there is exactly one such map, including when A is
  empty. This specifies precisely the empty map without choosing an element
  of A or adding an inhabitedness hypothesis. The source is a terminal set.
- Being a sheaf isomorphism already includes naturality of kappa and inverse
  equations; the explicit naturality of e identifies this with the restriction
  compatibility asserted in the node.

Mathlib declarations read and used:

- `Mathlib.Topology.Sheaves.Skyscraper`: root `skyscraperSheaf`,
  `skyscraperPresheaf`, their section and restriction definitions, and
  `skyscraperPresheaf_isSheaf`. Also read `skyscraperPresheaf_eq_pushforward`:
  it is pushforward from a one-point space, not from the point closure, so it
  does not already state this item.
- `Mathlib.Topology.LocallyConstant.Basic`: `LocallyConstant`,
  `LocallyConstant.const`, `LocallyConstant.comap`, `IsLocallyConstant`, and
  `IsLocallyConstant.iff_exists_open` (for the semantic check).
- `TopCat.Sheaf`, its category and underlying presheaf, and `TopCat.Presheaf.IsSheaf`
  were read in `Mathlib.Topology.Sheaves.Sheaf`.
- The standard closure, subtype topology, open-set inclusions, continuous
  subtype inclusion, and equivalences come through these imports.

Edge cases checked before writing: empty V has terminal source sections and
the unique empty map as target; if A is empty and y belongs to V then both
section sets are empty, while the universal constant-map assertion is vacuous.
If A is empty and y does not belong to V then the target still has its empty
map. A singleton A works in both cases. The empty space has no supplied y,
as in the node. A nonclosed point, including a generic point of a two-point
Sierpinski space, still satisfies the closure argument: every relatively open
neighbourhood of a specialization contains y. No Hausdorff or sober assumption
has been smuggled in. The statement does not restrict opens or cover sizes.

Searches (2026-10-11):

- `msearch.py ... leanfinder "skyscraper sheaf is direct image of locally
  constant sheaf on closure of a point"`: eight hits including
  `skyscraperPresheaf_eq_pushforward`, `skyscraperSheaf`, and its functor;
  no match for all three clauses or the closure comparison.
- `msearch.py ... loogle "TopCat.skyscraperSheaf, LocallyConstant"`: zero hits;
  unknown identifier `TopCat.skyscraperSheaf` (the actual declaration is at root).
- `msearch.py ... leansearch "skyscraper sheaf direct image constant sheaf
  closure singleton"`: service unavailable, Internal Server Error.
- `msearch.py ... grep "locallyConstant|LocallyConstant|skyscraper"
  Topology/Sheaves`: thirteen hits, skyscraper and flasque material, no comparison.
- Local `rg` for `locallyConstant|LocallyConstant|skyscraper|Skyscraper` in
  project and upstream Topology sources found existing inline descriptions of
  locally constant section presheaves and ringed-module skyscrapers. The
  descriptions in `InverseImageClosedPushforwardConstant.lean`,
  `ClosedPushforwardConstantRestriction.lean`, and
  `LocallyConstantGermEvaluation.lean` were read; none states this item.
- Local `rg` of the item id in upstream `WeilConjectures` had no match;
  `rg "skyscraper.*constant|constant.*skyscraper|point_closure"` in
  `dag/lean_names_upstream.json`, `lean/Sheaf`, and upstream `WeilConjectures`
  found only Fourier-transform comments in a different setting.
- Mathlib `rg` and direct reading of `Topology/Sheaves/Skyscraper.lean`
  and `Topology/LocallyConstant/Basic.lean` confirmed no declaration for the
  full item and confirmed the reused definitions' exact meaning.

The local Stacks source files are absent on this machine. The exact source
places were opened on the Stacks website:
[Modules 0CAL](https://stacks.math.columbia.edu/tag/0CAL) and
[Sheaves 009A](https://stacks.math.columbia.edu/tag/009A).
The former omits the point-closure claim in its finite sober reduction;
the node expands its elementary argument, which holds for arbitrary spaces.
The theorem docstring reproduces all five proof steps. No statement fault or
STATEMENT-DISPUTED issue was found.

Server validation: `scompile.py G1 lem-weil-pbc-skyscraper-constant-on-point-closure
.../SkyscraperConstantOnPointClosure.lean` returned exit 0, compiled in 1.2 s,
with no errors or warnings. The first compile revealed that an untyped
categorical `eqToHom` cannot be applied as a function; it was replaced by
the explicit type transport `cast`, with no change to the statement's meaning.

## Second reading by G1

I independently read the node and the theorem signature. The objects and hypotheses correspond item by item:

- `Y : TopCat.{u}`, `y : Y`, and `A : Type u` are exactly the arbitrary topological
  space, point, and set; there are no added separation, finiteness, nonemptiness, or
  discreteness assumptions.
- The closure and inclusion are rendered intrinsically as
  `closure ({y} : Set Y)` and the subtype
  `{w : Y // w ∈ V ∧ w ∈ closure ({y} : Set Y)}`; no independently varying `W` or
  map is introduced.
- Clause (1) is the first conjunct, with the same quantifier over every open `V` and
  the same equivalence `((V : Set Y) ∩ closure ({y} : Set Y)).Nonempty ↔ y ∈ V`.
- Clause (2) is the second conjunct: for `y ∈ V`, every
  `LocallyConstant` map on the indicated intersection has one value `a : A` and is
  pointwise equal to it. No topology or extra structure on `A` is assumed.
- The existential `F : Y.Sheaf (Type u)` and equivalences `e V` render the target
  sheaf's locally constant sections. The displayed equation with `i : U ⟶ V` uses
  `LocallyConstant.comap` along the induced subtype map and exactly expresses
  restriction of functions.
- Clause (3) is rendered by `kappa : skyscraperSheaf y A ≅ F`, sectionwise
  bijectivity, the `y ∈ V` constant-section equation (using `cast` for Mathlib's
  conditional source section), and the `y ∉ V` equation identifying the unique
  empty-intersection map. Naturality is included by the sheaf isomorphism and the
  explicit restriction equation for `e`.

Edge cases checked: empty opens give the terminal skyscraper section and the unique
empty locally constant map; `A = Empty` makes the `y ∈ V` assertion vacuous and still
leaves the non-containing case well defined; singleton `A` works; arbitrary, including
nonclosed/generic, points are allowed; the empty space is correctly excluded only by
requiring the supplied point `y`; no characteristic, index, or cover-size condition is
present.

Searches were reviewed in Mathlib's `Topology/Sheaves/Skyscraper.lean` and
`Topology/LocallyConstant/Basic.lean`, the upstream `WeilConjectures` sources, and
`lean/Sheaf` with LeanSearch, LeanFinder/Loogle, and `rg`. They provide the
skyscraper and locally constant primitives but no theorem combining closure, constant
sections, and the sheaf isomorphism. The Stacks source places are Modules Tag 0CAL
(proof of `lemma-constructible-in-constant`) and Sheaves Definition Tag 009A.

No mismatch was found, so no source, node, dependency, or Lean statement was changed.
The module compiles with `scompile.py` (exit 0, no warnings).
