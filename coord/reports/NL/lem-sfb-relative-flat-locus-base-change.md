## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFlatLocusBaseChange` states
`AlgebraicGeometry.isOpen_flatLocus_and_baseChange`, with its sole proof `sorry`.
It introduces no definitions. The node is unchanged except for its `lean` record.

Source read: `literature/stacks-project/more-morphisms.tex`, lines 4701–4777,
Tag 05VK (`lemma-base-change-flatness-fibres`) and the full statement and proof
of Tag 05VJ (`lemma-base-change-criterion-flatness-fibre`). Tag 05VK is exactly
the structure-sheaf specialization of 05VJ. The six-step proof split of the
live node is included in the declaration docstring.

Hypothesis and conclusion correspondence:

- Schemes S, X, Y are `{S X Y : Scheme.{u}}`, with explicit universe `u`.
- The three morphisms are `(p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)`.
- The required identity q composed with f equals p is `(hf : f ≫ q = p)`;
  categorical composition is written in the order f then q.
- Flatness of p is `[Flat p]`. The definition is equivalent to flatness of
  every stalk map by `AlgebraicGeometry.Flat.iff_flat_stalkMap`.
- Local finite presentation of p is `[LocallyOfFinitePresentation p]`.
- Local finite type of q is `[LocallyOfFiniteType q]`; this imposes no
  quasi-compactness hypothesis.
- The exact set U is `{x : X | (f.stalkMap x).hom.Flat}`. The ring map is
  O_{Y,f(x)} -> O_{X,x}; `RingHom.Flat` is `Module.Flat` for restriction
  of scalars along precisely that map. This uses the pointwise notion of
  `def-weil-flat-morphism`, without needing a new flat-at-point definition.
- The first conclusion is `IsOpen {x : X | (f.stalkMap x).hom.Flat}`.
- Every parameter change is covered by `∀ (T : Scheme.{u}) (h : T ⟶ S)`.
- X_T and Y_T are the chosen `pullback p h` and `pullback q h`.
- The induced morphism f_T is `pullback.map p h q h f (𝟙 T) (𝟙 S)`.
  The two commutativity witnesses use only hf and the identity laws. Thus
  it is the canonical morphism induced by f and the identity on T, rather
  than an arbitrary map. Its projections are pi_X followed by f and pi_T.
- The entire set of points where f_T is flat is the set on the left of
  the equality, using its stalk maps at `x : ↥(pullback p h)`.
- pi_X is `pullback.fst p h`; the right side is its ordinary inverse
  image `(pullback.fst p h) ⁻¹' {x : X | (f.stalkMap x).hom.Flat}`.
  Set equality is precisely the final clause of the node.

All five statement-dependency records were read, followed by their
Mathlib signatures and docstrings:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (lines 35–76).
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` and `AlgebraicGeometry.Flat.iff_flat_stalkMap`
  (lines 25–107). `Scheme.Hom.stalkMap` was read in Scheme.lean, lines 234–238;
  `RingHom.Flat` was read in RingTheory/RingHom/Flat.lean, lines 24–29.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation` (lines 42–50).
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` (lines 39–48).
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  and `pullback.map` (lines 94–115 and 259–275).
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies the scheme pullbacks.

The statement dependencies are public imports. The available proof-dependency
modules are plain imports: the recorded algebraic openness theorem is taken
from `WeilConjectures.RingTheory.OpenFlatLocus`, never copied. Its full signature
and proof docstring were read. The other plain Mathlib imports provide the
finite-presentation algebra lemma, affine stalk localization, flatness over a
localization, fibres, qcqs permanence, residue fields, and faithfully flat
field extension. The two newly split proof prerequisites
`lem-sfb-pointwise-flatness-base-change` and
`lem-sfb-fibrewise-flatness-criterion` currently have neither a `lean` record
nor a Mathlib match, so there is no recorded module to import for either.
They are proof prerequisites only and do not supply a missing statement notion.

Edge cases checked before writing:

- Empty X gives the empty open locus, and every X_T is empty.
- Empty T gives equality of empty sets. No nonempty or surjective hypothesis
  on h is imposed.
- If f is everywhere flat (in particular an identity), U is all of X and
  the equality agrees with ordinary preservation of flatness by base change.
- The map h may select a point, a nonreduced test scheme, an open subscheme,
  or an identity. No reducedness, Noetherian, separatedness, finite type of h,
  flatness of h, or quasi-compactness assumption has been added.
- Flatness of p is essential for reflection through the fibrewise criterion:
  Spec k -> Spec k[t] at zero over S = Spec k[t], followed by the identity
  on S, becomes flat over the zero fibre though the original closed point
  map is not flat. The statement keeps the flatness hypothesis on p.
- The universe is arbitrary; all schemes and test schemes are in the same
  category Scheme.{u}, as required to form its categorical pullbacks. Every
  universe and variable is explicitly bound, with `autoImplicit false`.

Searches actually run via `msearch.py` under group NL and this item:

- LeanFinder: “For X flat locally of finite presentation over S and Y locally
  of finite type over S, the flat locus of an S-morphism X to Y is open and
  commutes with arbitrary base change on S”. Eight hits concern flatness,
  stability under base change, universally open flat maps, or flat monomorphisms.
  None states openness and equality of these relative source flat loci.
- Loogle: `"AlgebraicGeometry.Flat", "IsOpen"`. The two hits concern flatness
  of open immersions, not the assertion here.
- Mathlib grep: `flatLocus|flat_locus|flat.*[Ll]ocus|[Ll]ocus.*flat` in
  `AlgebraicGeometry`: zero hits.
- LeanSearch: “The flat locus of a morphism between schemes over a base is
  open and commutes with base change if the source is flat locally finitely
  presented over the base”. Eight hits concern universally open maps, flat
  monomorphisms, base-change stability, or the definition of flatness.
  No exact match.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for that locus
  pattern and the node id. The algebraic flat-locus modules concern prime
  spectra and localized modules. `UniversalSurjectiveFlatOpen.lean` cites
  this node in a proof docstring but states a different locus in the base.
  No existing declaration states this node. A direct node-id search in
  `lean/WeilConjectures` also found no declaration.

No statement correction, disputed statement, new definition node, or dependency
interface repair is needed. The previous retry reported a stage-1 “already
split and reviewed” rejection. The NN review is indeed a stage-1 review: the
live item has no `lean` or `reviewed_lean` record. This packet supplies the
missing stage-2 statement through the prescribed stage-2 delivery wrapper.

Validation: `scompile.py` compiled this file in sandbox mode and under its
actual library module name, with no errors or warnings (5.5 s and 8.0 s,
respectively). The first attempt exposed an elaboration ambiguity in a set
binder: `pullback p h` needed the explicit scheme carrier `↥(pullback p h)`.
That annotation was fixed without changing the mathematical statement.
A direct search for `isOpen_flatLocus_and_baseChange` in Mathlib and both
project source trees found no prior declaration. All Lean lines are at most
100 characters.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
