## Worker report

Module: `lean/Sheaf/AlgebraicGeometry/FpqcRefinementFullyFaithful.lean`.
It states the singleton fpqc refinement result from Stacks, Descent, Tag 02W0.
The source checkout on this machine lacks `literature/stacks-project/descent.tex`;
I checked the text and proof at `https://stacks.math.columbia.edu/tag/02W0`.

Hypotheses and clauses:

- `S X X' : Scheme.{u}` renders the three schemes; `f`, `g`, `h` are their stated arrows.
- `hf` and `hg` are membership of the two singleton presieves in
  `Scheme.fpqcPrecoverage S`, the dependency's Mathlib match.
- `hcomp : h ≫ f = g` says that `h` is over `S` and `g = f ∘ h`.
- The first conjunct quantifies over `V : Over X` and `D : Over.DescentDatum f V`.
  It produces `V'`, its projection `q`, the pullback square `IsPullback q ... h`,
  and a datum `D'` satisfying `Over.DescentDatum.IsBaseChange hcomp hq D D'`.
- The second conjunct quantifies over any two original data and any choices of their
  pullback objects and data. The four `IsPullback` and `IsBaseChange` premises ensure
  these are the pullbacks along `h`, with no auxiliary hypothesis on the objects.
- The premise on `u' : V' ⟶ W'` says it commutes with every transport map of the
  pulled-back descent data. `∃! (u : V ⟶ W)` says a unique original morphism
  commutes with every original transport map and obeys
  `u'.left ≫ qW = qV ≫ u.left`. This is the hom-set bijection, i.e. full
  faithfulness, expressed without adding an unrecorded category definition.

Dependency declarations used: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
(Mathlib/AlgebraicGeometry/Scheme.lean); `AlgebraicGeometry.Scheme.fpqcPrecoverage`
(Mathlib/AlgebraicGeometry/Sites/Fpqc.lean);
`CategoryTheory.Over.DescentDatum` and its `IsBaseChange` predicate
(WeilConjectures/CategoryTheory/Comma/Over/DescentDatum.lean). The latter is
the transport form of Stacks Tag 023V as its source docstring explains.

Edge cases checked: `h = 𝟙 X` is covered without a distinctness assumption;
an empty base or empty pullback object is not excluded; no characteristic,
affineness, connectedness, or nonempty index hypothesis is introduced. The
point tests range over `Scheme.{u}`, matching the descent-datum structure.

Searches: `msearch leanfinder` with “pullback descent data along refinement of
fpqc singleton covers fully faithful” found only generic pseudofunctor descent
APIs, no scheme-valued singleton refinement statement. `msearch loogle` with
`CategoryTheory.Pseudofunctor.DescentData,AlgebraicGeometry.Scheme.fpqcPrecoverage`
returned no hit. `msearch grep` for `DescentData|fullyFaithful|refinement` in
`Mathlib/AlgebraicGeometry/Sites` found no match. `rg` over upstream
`WeilConjectures/` found module/sheaf descent results but no result for descent
data on schemes over a base. `grep -rn` for the item id over upstream found none;
`rg` over this project's `lean/Sheaf` found none. The Mathlib generic descent
result uses a different pseudofunctor and does not state this scheme result.

Server single-file compile: clean (1.6 s). No statement dispute found.

## Second reading by M1

I read the node and Stacks, Descent, Tag 02W0 independently. Its ambient assumption is
only that `S` is a scheme; both families are fpqc coverings. The singleton specialization
introduces `X`, `X'`, their arrows to `S`, and a refinement arrow over `S`.

- `S X X' : Scheme.{u}` are precisely the base and two covering schemes. The Mathlib
  `Scheme` dependency is the node's scheme, with no affine or nonempty instance.
- `f : X ⟶ S` and `g : X' ⟶ S` are the two covering arrows. Their singleton fpqc
  hypotheses are `hf` and `hg` in `Scheme.fpqcPrecoverage S`, the recorded Mathlib match
  of the fpqc-covering dependency. Neither cover is assumed finite or surjective by an
  extra binder.
- `h : X' ⟶ X` and `hcomp : h ≫ f = g` are exactly the refinement over `S`.
- For each `V : Over X` and `D : Over.DescentDatum f V`, the first conjunct supplies
  `V' : Over X'`, its arrow `q` and commutativity `hq`, an `IsPullback` square, and
  `D' : Over.DescentDatum g V'` with `IsBaseChange hcomp hq D D'`. The dependency's
  transport datum is equivalent to the node's cocycle-isomorphism datum; its
  `IsBaseChange` predicate compares the two transports through the pullback arrow.
- The second conjunct quantifies over arbitrary `V W`, original data `D E`, pullback
  objects `V' W'`, their arrows, squares and pulled-back data. This covers every pair
  of descent data and every valid choice of pullback, with no selected object or extra
  hypothesis.
- A pulled-back morphism `u' : V' ⟶ W'` is required to commute with all transport
  maps, for every `T : Scheme.{u}`, `a b : T ⟶ X'`, equality over `S`, and point `x`.
  The conclusion `∃! u : V ⟶ W` requires the same compatibility over `X` and
  `u'.left ≫ qW = qV ≫ u.left`. These are precisely existence and uniqueness of a
  compatible original morphism whose pullback is `u'`; no conclusion clause is absent.

Edge cases: no inhabitance assumption excludes an empty scheme or zero ring scheme;
`h = 𝟙 X` is permitted; singleton covers need no nonempty auxiliary index type.
There is no characteristic, Noetherian, affine or finite-type restriction. The
scheme and point quantifiers use the same arbitrary universe `u`.

Independent searches: `msearch leanfinder` for fully faithful restriction of scheme
descent data under fpqc refinement returned generic pseudofunctor descent results,
which have a different datum and require prestack hypotheses. `msearch loogle` for
`Over.DescentDatum.IsBaseChange` found no indexed declaration. `msearch grep` for fpqc
descent/refinement found no scheme statement. `rg` in upstream `WeilConjectures/`,
Mathlib's algebraic-geometry sites, and this project's `lean/Sheaf` found no exact
declaration. I opened the recorded dependency signatures, especially
`Over.DescentDatum` and `IsBaseChange`; no duplicate notion is introduced.

Mismatch found: the theorem docstring only named categorical cancellation, omitting
the node's explicit lifting, recovery and uniqueness steps. I expanded those steps.
The Lean signature and the node's `lean.statement` already agree and needed no edit.
