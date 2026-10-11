## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful` defines
`CategoryTheory.Over.DescentDataCategory`: an object is a scheme over `X`
together with a `CategoryTheory.Over.DescentDatum` relative to `a : X ⟶ S`.
Its morphisms are morphisms over `X` satisfying the transport compatibility
equation for every test scheme, pair of maps to `X`, equality over `S`, and
point of the source object.  The category instance uses the identity and
composition laws of `Over.DescentDatum`.

It states
`CategoryTheory.fpqc_singleton_pullback_fullyFaithful`: for schemes `S`, `X`,
`X'`, a structure map `a : X ⟶ S`, a morphism `r : X' ⟶ X`, and the hypothesis
`Presieve.singleton r ∈ Scheme.fpqcPrecoverage X`, there exists a functor from
the descent-data category over `X/S` to that over `X'/S`; it has a
fully-faithful structure (`Nonempty F.FullyFaithful`), and it is the pullback
functor: maps `q A` exhibit each `(F.obj A).V` as `X' ×_X A.V` (`IsPullback`),
its datum as the base change of `A.datum` (`Over.DescentDatum.IsBaseChange`),
and `F.map f` as `id_{X'} ×_X f`.  The theorem proof is `sorry`, as required for stage 2.

### Statement correspondence

* `S` and `X` are explicit `Scheme.{u}` binders; `a : X ⟶ S` is the given
  morphism of schemes.
* `X'` and `r : X' ⟶ X` are explicit; the singleton fpqc-cover hypothesis is
  exactly `Presieve.singleton r ∈ Scheme.fpqcPrecoverage X`.
* `Over.DescentDataCategory a` represents `DD(X/S)`: objects contain the
  scheme over `X` and its descent datum; `Hom.commutes` is the required
  equation for morphisms of descent data.
* The codomain `Over.DescentDataCategory (r ≫ a)` uses the prescribed
  structure map on `X'` obtained by composition.
* `F` is the pullback functor; `Nonempty F.FullyFaithful` renders “fully
  faithful”; `q`, `IsPullback`, `IsBaseChange` and the final equation make `F`
  the pullback functor on objects, data and morphisms.

### Dependency declarations used

* `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and its category
  instance, imported through `Mathlib.AlgebraicGeometry.Sites.Fpqc`.
* `def-weil-pbc-fpqc-covering`: Mathlib `AlgebraicGeometry.Scheme.fpqcPrecoverage`
  and `Presieve.singleton`, from `Mathlib.AlgebraicGeometry.Sites.Fpqc`.
* `def-pd-descent-datum`: `CategoryTheory.Over.DescentDatum` and its transport
  fields, from `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`.
* `def-pc-fibre-product`: no recorded declaration; rendered by Mathlib's
  `CategoryTheory.IsPullback` (the declaration of def-weil-pbc-category-fibre-product).

### Edge cases checked

The singleton identity cover `r = 𝟙 X` is represented by the identity
presieve and gives the identity pullback situation.  Empty schemes and zero
objects are not excluded by any binder.  The universe is explicit (`u`) and
the same universe is used for all schemes and test schemes.  No separatedness,
quasi-compactness, or characteristic hypothesis is added beyond membership in
the fpqc precoverage.

### Searches

* `msearch.py ... leanfinder "fully faithful pullback functor on descent data for an fpqc covering of schemes"`:
  generic `CategoryTheory.Pseudofunctor` descent declarations were returned;
  no scheme-specific match.
* `msearch.py ... loogle "Functor.FullyFaithful, Over.DescentDatum, fpqc"`:
  zero hits (the query identifier `Functor.FullyFaithful` was not known).
* `msearch.py ... grep "DescentDatum|fpqcPrecoverage|fullyFaithful" Mathlib/AlgebraicGeometry Mathlib/CategoryTheory`:
  no exact match in the requested paths; direct `rg` inspection found only the
  generic Mathlib descent APIs and the recorded `Over.DescentDatum` project
  declaration.

No existing declaration states the scheme fpqc singleton fully-faithfulness
claim, so a new module is required.

## Second reading by F1

I checked the node against Stacks Project Tags 0241 and 023Y and the compiled
declarations of all four statement dependencies.

* Base `S`, cover base `X`, and structure map `a : X ⟶ S`: the explicit
  `Scheme.{u}` binders and arrow `a`. Exact; no property of either scheme is
  assumed.
* Cover domain `X'`, map `r : X' ⟶ X`, and structure map on `X'`:
  `X' : Scheme.{u}`, `r`, and the codomain's `(r ≫ a)`. Exact; in particular
  `S = S'` from Tag 0241 is encoded by using the same `S`.
* Singleton fpqc hypothesis: `Presieve.singleton r ∈ Scheme.fpqcPrecoverage X`.
  This is the Mathlib match of `def-weil-pbc-fpqc-covering`. Exact; no separate
  flatness, quasi-compactness, surjectivity, or finiteness assumptions.
* Objects of `DD(X/S)`: `Over.DescentDataCategory a` contains `V : Over X`
  and `datum : Over.DescentDatum a V`. The latter is the recorded declaration
  of `def-pd-descent-datum`, whose natural transport and cocycle axioms encode
  the Stacks pullback isomorphism. Exact through the Yoneda equivalence.
* Morphisms of `DD(X/S)`: `DescentDataCategory.Hom.hom : A.V ⟶ B.V` and
  `commutes` express compatibility on all test schemes and points. Exact;
  no morphism is discarded or added.
* Pullback functor on objects: `F` has codomain `DD(X'/S)`. For each `A`,
  `q A` and `hq` give the square over `r`, `IsPullback` makes its underlying
  object `X' ×_X A.V`, and `IsBaseChange rfl hq A.datum ...` makes its datum
  the pullback of `A.datum` along `r × r`. Exact up to the canonical unique
  isomorphism inherent in a chosen fibre product.
* Pullback functor on morphisms: the final universal equation
  `(F.map f).hom.left ≫ q B = q A ≫ f.hom.left` specifies the induced
  morphism `id_{X'} ×_X f` by the pullback universal property. Exact.
* Fully faithful conclusion: `Nonempty F.FullyFaithful`, the standard category
  theory property for this specified `F`. Exact; the `Nonempty` only packages
  the proof-carrying structure as a proposition.

The previous theorem merely asserted an arbitrary fully faithful functor whose
objects were individually isomorphic to pullbacks. It did not specify pulled
back descent data or the action on morphisms. I replaced that condition by
the shared pullback projections `q`, pullback squares, `IsBaseChange`, and the
map equation. I added source and blueprint tags to the two category
declarations, expanded the proof docstring to follow the node's three steps,
removed an unused universe and import, and synchronized `lean.statement`.

Edge cases: the singleton cover can have `r = 𝟙 X`; empty `X`, `X'`, or `S`
are not excluded; neither datum nor morphism need have any test-scheme
points. There is no numerical parameter or characteristic restriction. The
explicit universe `u` is arbitrary, and the common universe for the schemes
and test schemes agrees with the dependency's `Over.DescentDatum` over `Scheme`.

Independent searches: LeanFinder query `pullback of descent data along a
covering functor fully faithful` returned only generic pseudofunctor prestack
results; Loogle query `DescentDatum, FullyFaithful` found no declaration; `rg`
for `DescentDataCategory`, `pullback.*fullyFaithful`, and `fpqc.*descent` in
Mathlib's algebraic geometry tree, `WeilConjectures`, and `lean/Sheaf` found
no exact scheme-specific statement. The generic Mathlib pseudofunctor
declarations require a pseudofunctor and do not state Tag 0241 for these
descent-data objects. No existing declaration replaces this module.

## Reviewer fixes (R-sff0724)

Module docstring gains the `## Main definitions` / `## Main statements` list;
the docstring of `DescentDataCategory.Hom` cited Tag 023W (descent data for a
family) instead of Definition 35.34.1 (3) (Tag 023V, morphisms of descent
data); the worker report's summary, which still described the earlier
`Over.pullback`-isomorphism form of the statement, now describes the delivered one.
