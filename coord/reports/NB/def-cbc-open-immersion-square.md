## Worker report

The module `lean/Sheaf/AlgebraicGeometry/OpenImmersionSquare.lean` defines
`AlgebraicGeometry.OpenImmersionSquare` by extending the recorded
`AlgebraicGeometry.ChosenCartesianSquare`. It contains no theorem, proof, or `sorry`.
Only the item's `lean` record changes; no statement correction or extra node is needed.

Clause-by-clause reading:

- The four schemes are `{U' U X' X : Scheme.{u}}`, with explicitly declared universe `u`.
- The four arrows and their orientation are `(gU : U' ⟶ U) (j' : U' ⟶ X')
  (j : U ⟶ X) (g : X' ⟶ X)`.
- The Cartesian-square datum is inherited by
  `extends ChosenCartesianSquare gU j' j g`.
- The equality `j ∘ g_U = g ∘ j'` is the inherited `CommSq.w`,
  `gU ≫ j = j' ≫ g` (Lean composition is written in diagrammatic order).
- The chosen isomorphism is the inherited `isoPullback : U' ≅ pullback j g`.
- Compatibility with both projections is inherited as `hom_fst` and `hom_snd`,
  respectively `isoPullback.hom ≫ pullback.fst j g = gU` and
  `isoPullback.hom ≫ pullback.snd j g = j'`.
- The right open immersion is the field `isOpenImmersion : IsOpenImmersion j`.
- The left open immersion is the field `isOpenImmersion' : IsOpenImmersion j'`.
- The bottom morphism `g` has no property hypothesis; neither horizontal arrow is
  required to be an open immersion.

Dependencies read in full and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (the category's arrows).
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including its full inherited commutativity,
  chosen isomorphism and two projection equations.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  the open-immersion predicate on the underlying locally ringed spaces.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
  Scheme pullbacks exist by `Mathlib.AlgebraicGeometry.Pullbacks`, publicly imported by
  the chosen-square module. No second definition of any component notion is made.

The source blueprint definition was opened at
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-p1/def-cbc-open-immersion-square.md`.
It agrees with the DAG statement. The existing upstream `Etale.openImmersionSquareIso`
was also read: it is an inverse-image functor isomorphism from a commutative square,
not the geometric square datum requested here.

Edge cases checked mathematically before writing: empty schemes and the empty open
subscheme are allowed; identity open immersions are allowed; no nonemptiness,
Noetherian, finiteness, separatedness or flatness condition is present. Arbitrary
base change `g` is allowed, including morphisms that are not open immersions.
The Cartesian condition prevents an arbitrary unrelated `U'` from being supplied.
Both open-immersion fields remain explicit even though the left condition follows
from base change of the right one. The chosen comparison is actual isomorphism data,
not merely `IsPullback` or an existential. One explicit universe covers every scheme
universe, with no testing over an artificially smaller universe.

Searches made on 2026-10-15:

- `msearch.py ... leansearch "A cartesian square of schemes with both vertical maps
  open immersions"`: unavailable, Internal Server Error; no search verdict inferred.
- `msearch.py ... leanfinder "A cartesian square of schemes with chosen pullback
  isomorphism and both vertical maps open immersions"`: eight hits, including
  `IsOpenImmersion.isPullback`, pullback existence and projection instances,
  and `Scheme.pullback_map_isOpenImmersion`. These give component properties,
  not this bundled chosen-square datum.
- `msearch.py ... loogle '"IsPullback", "IsOpenImmersion"'`: four hits:
  `IsOpenImmersion.isPullback`, `isPullback_lift_id`,
  `image_preimage_eq_preimage_image_of_isPullback`, and
  `Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`. No exact definition.
  The signature of `isPullback` was opened: it deduces a pullback property from
  commutativity and an equality of open ranges, without chosen identification data.
- `msearch.py ... grep
  'structure.*(Open.*Square|Square.*Open)|def.*openImmersionSquare'`: zero Mathlib hits.
- `rg` in `WeilConjectures` for `OpenImmersionSquare|openImmersionSquare` and
  the blueprint id found only the upstream functor isomorphism and derived maps;
  their signatures were read and do not define the requested geometric datum.
- `rg` in `lean/Sheaf` for those names found no bundled open-immersion square.
  Searching Cartesian-square names found the recorded chosen-square module, reused here.
- `rg` in `dag/lean_names_upstream.json` for the proposed names found no conflict.

No node fault or disputed statement was found. All writes are confined to the named
sandbox; compilation is through `scompile.py` on the server only. The independent
second reading is left to the designated second worker.

## Second reading by NB

I independently read the node, its blueprint source at order 1172, the sandbox module,
all four statement-dependency nodes, and their recorded declarations. The source is
the blueprint definition, not a Stacks statement; it assumes no ambient base field,
Noetherian condition, or other standing hypothesis. I also checked the open-immersion
component directly in `schemes.tex`, definitions with tags 01HE and 01IO: these impose
exactly the locally ringed space open-immersion condition used by Mathlib.

The complete object/hypothesis/clause list and its Lean match is:

- Four schemes U', U, X', X: `{U' U X' X : Scheme.{u}}`. Exact; the dependency's
  `Scheme` is a locally ringed space locally isomorphic to a ring spectrum, and
  `Scheme.Hom` is a morphism of the underlying locally ringed spaces.
- Four scheme morphisms, in the displayed orientation: `(gU : U' ⟶ U)` and
  `(j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)`. Exact; no arrows are reversed.
- Cartesian square with chosen identification: `extends ChosenCartesianSquare gU j' j g`.
  I opened that module: it extends `CommSq`, with `isoPullback : U' ≅ pullback j g`
  under this substitution. Exact, actual isomorphism data rather than existence alone.
- Commutativity j composed with gU equals g composed with j': inherited `CommSq.w`
  is `gU ≫ j = j' ≫ g`. Exact, using diagrammatic composition.
- Compatibility with both projections: inherited `hom_fst` and `hom_snd` assert
  `isoPullback.hom ≫ pullback.fst j g = gU` and
  `isoPullback.hom ≫ pullback.snd j g = j'`. Exact. I opened the recorded Mathlib
  pullback, its two projections, and the unconditional scheme pullback instances;
  the import supplies existence without an extra hypothesis on the square.
- Right vertical open immersion j: `isOpenImmersion : IsOpenImmersion j`. Exact.
- Left vertical open immersion j': `isOpenImmersion' : IsOpenImmersion j'`. Exact.
  Both fields use the dependency's abbreviation for locally ringed space open
  immersions, rather than an open embedding of topological spaces alone.
- No hypothesis on g: g has only the morphism binder. Exact; there are no extra
  typeclass assumptions on it or on gU.

Edge cases: empty schemes, the empty open subscheme, identity open immersions and
arbitrary non-open base changes remain permitted. The common arbitrary universe u
is the category-of-schemes convention of the dependencies and does not introduce a
smaller test universe. There are no index sets, coefficients, characteristic
restrictions, degree parameters, or nonemptiness assumptions. There is no hollow
data, theorem proof, sorry, hidden local notation, or unbound variable. The module
and main declaration docstrings identify the source and blueprint node. The node
has no proof steps to reproduce. Its `lean.statement` agrees verbatim with the
structure signature up to `where`.

Independent searches on 2026-10-15, with different wording from the first worker:

- LeanFinder via msearch: "Bundled pullback diagram of schemes equipped with a chosen
  isomorphism to the fibre product and open embeddings on the vertical sides".
  Eight hits, mainly scheme pullback existence, gluing and `Scheme.Pullback.Triplet`.
  I opened `Triplet`: it bundles points of X, Y, S and their image equalities, not
  schemes or a square. No exact match.
- Mathlib grep via msearch:
  `structure.*(Immersion|Cartesian|Pullback).*Square|def.*open.*[Ss]quare`.
  Zero hits. The worker's recorded LeanSearch unavailability and successful Loogle
  component search were also inspected; neither establishes an existing package.
- Direct rg over the source project's `WeilConjectures` and this repository's
  `lean/Sheaf`, using structure/diagram/square and open/Cartesian/pullback variants.
  The reused `ChosenCartesianSquare` is the general square datum without open
  conditions. The upstream `Etale.openImmersionSquareIso`, whose binders and return
  type I opened, is a functor isomorphism from a `CommSq`, not a geometric square.
  Other hits concern a fixed pair of opens, overlaps, or module comparison maps;
  they do not define this notion. No proposed-name conflict in the upstream names
  index. The recorded dependency definitions are used rather than copied.

No mismatch was found. I changed only this report; the module and node record are
preserved. There are no new nodes, dependency modules, or statement corrections in
this delivery. Server-only scompile passed cleanly for the delivered module
(1.4 seconds), also checking its chosen-square dependency in the private overlay.
