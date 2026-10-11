## Worker report

`FiniteEtaleDescentData.lean` defines the finite-etale full subcategory of
`Over.DescentDataCategory g`. `FiniteEtaleDescent.lean` states the equivalence
of this category with `Y.FiniteEtale`, with the canonical base-change action
specified on objects, descent data, and morphisms. The theorem proof is `sorry`.

Clause matching for the item:

- Schemes `Y`, `Y'` and the map `g` are `{Y Y' : Scheme.{v}} (g : Y' ⟶ Y)`.
  Surjectivity and etaleness are `[Surjective g] [Etale g]`.
- The finite-etale category over `Y` is `Y.FiniteEtale` from
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`.
  `FiniteEtaleDescentData g` is the full subcategory of
  `CategoryTheory.Over.DescentDataCategory g` whose underlying map is finite
  and etale; its morphisms are exactly compatible `Y'`-morphisms.
- `F : Y.FiniteEtale ⥤ FiniteEtaleDescentData g` is the functor in the node.
  `Nonempty F.IsEquivalence` is its equivalence-of-categories clause.
- For each `P`, `q P` and `hq` give the commutative square, and `IsPullback`
  identifies `(F.obj P).obj.V` with `P ×_Y Y'`. The displayed transport
  equation says the datum on this pullback is the canonical comparison:
  transporting a point does not change its image in `P`.
- The final equation for every `f : P ⟶ Q` says `F.map f` is the unique
  morphism over `Y'` induced by base change of `f` through the two pullback
  squares. Thus the functor acts on morphisms as `f ×_Y Y'`.

Dependencies used: `AlgebraicGeometry.Scheme` (Mathlib),
`AlgebraicGeometry.Surjective` (Mathlib), `AlgebraicGeometry.Etale` (Mathlib),
`CategoryTheory.Limits.IsPullback` (Mathlib),
`AlgebraicGeometry.Scheme.FiniteEtale`
(`WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`),
`CategoryTheory.Over.DescentDatum`
(`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`), and
`CategoryTheory.Over.DescentDataCategory`
(`Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful`). The recorded Mathlib
match `MorphismProperty.Over` for the finite-etale category is general;
`Scheme.FiniteEtale` is the source's equivalent specialized category and
has the same objects and all `Y`-morphisms.

Edge cases: `Y` and `Y'` may be empty; no nonempty or connected assumption
appears. The empty finite-etale scheme is allowed. No finiteness assumption
on `g` is added, so infinite etale covers remain included. A single scheme
`Y'` covers the coproduct-cover example in the node. `Scheme.{v}` matches
the source category's universe and imposes no characteristic restriction.

Searches: `msearch.py leansearch` for the finite-etale descent-data category
was unavailable (Internal Server Error). `msearch.py leanfinder` for finite-etale descent equivalence and
for its descent-data category found etale morphism and site declarations but
no matching statement or category. `msearch.py loogle` for
`ObjectProperty.FullSubcategory, DescentDataCategory` found no Mathlib match.
`msearch.py grep` for `FiniteEtaleDescent|FiniteEtale.*DescentData` found
none in Mathlib. `rg` over `WeilConjectures` found the general transport
datum and `Scheme.FiniteEtale`, but no finite-etale descent-data category or
equivalence; `grep -rn lem-galois-descent` found no source declaration. `rg`
over `lean/Sheaf` found the general `Over.DescentDataCategory` only.
`rg` over `dag/nodes` and `blueprint_refs.py search` found no node defining
the finite-etale descent-data category.

Second-reader correction to the worker's initial proof-route assessment:
a surjective etale morphism need not itself be quasi-compact, but its
singleton family IS an fpqc covering in Stacks and Mathlib. Stacks Tag 022C
and `Scheme.fppfPrecoverage_le_fpqcPrecoverage`, applied after
`Scheme.Hom.singleton_mem_fppfPrecoverage`, give this without a
`QuasiCompact g` hypothesis. The initial claimed node fault was mistaken.

## New nodes

`def-galois-finite-etale-descent-data` defines the full subcategory of the
existing `Over.DescentDataCategory g` selected by finite and etale underlying
structure maps. Its source is the category `DD` in the blueprint statement
and Stacks Tag 023V. The node, Mathlib, and source searches above found no
such specialized category. The definition reuses the project's descent datum
and its compatible morphisms, so it introduces no second descent datum.

## Second reading by F1

I opened the item node, its two delivery modules, every statement dependency,
and the source definition at Stacks Tag 023V. The item has the following
objects and clauses, with the corresponding Lean rendering and verdict:

1. `Y`, `Y' : Scheme.{v}`, `g : Y' ⟶ Y`, with `[Surjective g]` and
   `[Etale g]`: the theorem binders `{Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
   [Surjective g] [Etale g]` match exactly, including universes and allowing
   empty schemes and arbitrary characteristic.
2. `Y''`, `Y'''`, their projections, and fibre products: these are represented
   by the existing `Over.DescentDataCategory g` and
   `CategoryTheory.Over.DescentDatum`; its source declaration uses transport,
   which its docstring identifies with the pullback isomorphism and cocycle of
   Tag 023V. No private fibre-product or descent-datum notion was introduced.
3. The finite-etale descent-data category `DD`: the module's
   `FiniteEtaleDescentData g` is precisely the full subcategory selected by
   `IsFinite A.V.hom ∧ Etale A.V.hom`; `ObjectProperty.FullSubcategory`
   preserves exactly the compatible `Y'`-morphisms of the dependency category.
4. The base-change functor and canonical datum: the existential functor
   `F : Y.FiniteEtale ⥤ FiniteEtaleDescentData g`, together with the pullback
   witness `q` and its transport equation, renders the node's specified
   canonical object action and descent datum. The final equation
   `(F.map f).hom.hom.left ≫ q Q = q P ≫ f.hom.left` renders the stated
   base-change action on every `Y`-morphism `f : P ⟶ Q`.
5. Equivalence: `Nonempty F.IsEquivalence` is exactly the equivalence-of-
   categories conclusion, with no additional finiteness, connectedness,
   nonemptiness, or characteristic hypothesis.

The empty index/family case is represented by an arbitrary single morphism
`g`; zero or empty schemes are not excluded, and there is no `n` parameter.
The universe `v` is shared by all schemes and test schemes in the transport
clause, as in the dependency declaration. A finite-etale object may be empty.

I repeated the worker's searches: LeanFinder found only generic étale and site
declarations; Loogle found no matching descent-data category; grep over
Mathlib, `WeilConjectures`, and `lean/Sheaf` found no specialized category or
equivalence. The source search found only Tag 023V and the generic transport
declaration. Thus the new definition node is required, and its module uses
the recorded dependency declaration rather than a copy.

No mismatch in the theorem signature or definition was found. I expanded
the theorem docstring: it now gives all six proof steps, their DAG dependencies,
and the sources, rather than only a compressed summary of Steps 3--6.
I also corrected the worker's claimed proof-route fault: non-quasi-compactness
of `g` does not prevent its singleton from being an fpqc covering. In Stacks
Tag 022C, openness permits finitely many affine source opens to cover each
affine target open; in Mathlib `fppfPrecoverage_le_fpqcPrecoverage` proves the
same inclusion. No node statement, hypotheses, or proof record was changed.

Further source and dependency checks: I read Stacks `descent.tex` lines
8101--8170 (023V and `remark-easier`), 9148--9205 (0245), 6102 (02LA),
6209 (02VN), and `topologies.tex` lines 3044--3071 (022C), from the local
Stacks source copy `/home/ubuntu/c1-stacks-review/`. The source definition
has no background finiteness, Noetherian, separatedness, or field assumption.
The transport datum's naturality, identity, and cocycle fields encode the
isomorphism/cocycle of 023V: opposite transports are inverses by its cocycle.
For the theorem's canonical datum, `IsPullback` makes each transported
T-point the unique point with the new base coordinate and the same `q`
coordinate; hence the displayed transport equation determines the canonical
comparison, not merely some effective datum. The morphism equation similarly
determines the unique base-change map, since its other projection is fixed
by being a morphism over `Y'`.

I opened `Scheme.FiniteEtale` in the source module: it is the full subcategory
of `Y.Etale` selected by `IsFinite P.hom`; the small etale category is
`MorphismProperty.Over @Etale ⊤ Y`, so its morphisms are all Y-morphisms.
The new node and module specialize the already existing general
`Over.DescentDataCategory` (whose `Hom.commutes` I also read) to finite etale
structure maps. The new node's source, self-contained statement, dependency
citations, exact fields, ancestor and via agree with the required node shape.
There are no additional dependency modules in this delivery, no hollow
construction, and only the main theorem is `sorry`.

Independent searches used different wording: `msearch.py leanfinder
"equivalence finite étale schemes effective descent along étale covering"`
returned only etale morphism/site declarations; `msearch.py loogle
'"DescentDatum"'` returned no results. `rg` for
`FiniteEtale.*[Dd]escent|[Dd]escent.*FiniteEtale|finite.etale.*equivalence`
across Mathlib, `WeilConjectures`, and `lean/Sheaf` found no matching theorem
or specialized category. Searches for `descent data` and `descent-data`
in DAG definition nodes found only the existing general datum notion;
there is no pre-existing node for its finite-etale category. Name searches
for `finiteEtaleDescent` and `lem-galois-descent` likewise found no source
replacement. Both modules compile cleanly together via `scompile.py` with
all universes and variables explicitly bound. The dry-run preflight is the
final check of module names, node records, line widths and delivery shape.

Both `lean.statement` records were synchronized verbatim with the multiline
signatures in their modules; this only fixes record formatting.
