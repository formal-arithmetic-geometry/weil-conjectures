## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange` states
`AlgebraicGeometry.Scheme.Modules.isAmple_on_affineOpens_tensorPullback_baseChange`
with `sorry`. It states the scheme-relative ampleness base-change lemma of Stacks
0893, using exactly the affine-open formulation in the DAG. No new definition,
new node, dependency repair, or statement correction is needed.

Hypotheses and conclusion, clause by clause:

- Schemes X, T, T': `{X T T' : Scheme.{u}}`. The universe `u` is explicitly bound
  and arbitrary; the categorical pullback and its module category are in this
  same scheme universe.
- Arbitrary scheme morphisms f and g: `(f : X ⟶ T) (g : T' ⟶ T)`. No finite type,
  separatedness, properness, flatness or affine condition is imposed on them.
- The invertible O_X-module L: `(L : X.Modules) [L.IsInvertible]`, using the
  recorded `Scheme.Modules.IsInvertible`.
- Every affine open V of T: `∀ V : T.Opens, IsAffineOpen V →` in `hL`.
- Restriction of L to f inverse-image V:
  `(tensorPullback (f ⁻¹ᵁ V).ι).obj L`. This is the recorded tensor-formula module
  pullback along the open immersion, rather than a new restriction functor.
- Ampleness of each such restriction is
  `∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj L).IsInvertible,
  @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj L) h`.
  The existential simply supplies the Prop-valued invertibility argument needed
  by the existing `IsAmple`; invertibility is already implied by that of L.
  No geometric data or auxiliary map is chosen.
- X' is the chosen `pullback f g`; g' and f' are exactly `pullback.fst f g` and
  `pullback.snd f g`, with the same orientation as the node.
- Pullback g'^*L is `(tensorPullback (pullback.fst f g)).obj L`.
- The conclusion quantifies over `∀ V' : T'.Opens, IsAffineOpen V' →`.
- Its restricted module is the tensor pullback of g'^*L along
  `((pullback.snd f g) ⁻¹ᵁ V').ι`, and `@IsAmple` is evaluated on the scheme
  `((pullback.snd f g) ⁻¹ᵁ V').toScheme`. The existential invertibility witness
  again only supplies the required proof argument of absolute ampleness.

Recorded statement dependencies opened and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; read their full
  signatures and docstrings in the pinned Mathlib source.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, declaration
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; read the class and its
  open-trivialization field in the upstream source. It is publicly available
  through the recorded Ample module.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, declarations
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; read each signature and
  docstring. `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
- `def-weil-pbc-ample-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Ample`, declaration
  `AlgebraicGeometry.Scheme.Modules.IsAmple`; the current source was read with
  `scompile.py --source`. It includes quasi-compactness and the affine
  nonvanishing-locus criterion with strictly positive tensor power.
- `def-pc-module-pullback`:
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, declaration
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`; read the current live source
  through `scompile.py --source`, including the tensor-formula object and functor.

The module imports the available recorded proof-dependency modules for affine
morphisms, quasi-compact base change, invertible pullback and affine pullback of
ampleness. `lem-trf-scheme-relative-ample-affine-cover` currently has no Lean
record; it is used only in the postponed proof and so has no import yet. The
five proof steps are fully transcribed in the theorem docstring. No proof
prerequisite is used to replace or assume the theorem's conclusion.

Edge cases checked before writing:

- Empty X, T or T' and the empty affine open remain allowed. There is no
  `Nonempty` hypothesis, and absolute ampleness on the empty restriction has
  vacuous point condition and the expected compactness condition.
- The identity base map gives precisely the original relative ampleness under
  the canonical pullback identification. An arbitrary non-affine base map is
  included; no accidental `IsAffineHom g` hypothesis is present.
- The schemes need not be Noetherian or of finite type. The affine-open
  hypothesis implies quasi-compactness of f because the existing absolute
  ampleness includes compactness, as the source and DAG proof explain.
- The conclusion is ampleness over every affine open of T', not just members
  of a chosen affine cover and not absolute ampleness on all of X'.
- No independent test-object universe, characteristic restriction or positive
  dimension restriction has been introduced.

Source check: read `literature/stacks-project/morphisms.tex`,
`definition-relatively-ample` (01VH) and `lemma-ample-base-change` (0893),
including its proof by affine neighbourhoods mapping into affine opens of T.
The DAG statement is the same assertion: its affine-open premise already
implies the explicit quasi-compactness in 01VH.

Searches made (the remote searches are recorded by `msearch.py`):

- LeanFinder: “Relative ampleness of an invertible sheaf on a scheme is
  preserved by arbitrary base change”: eight hits about unrelated morphism
  properties stable under base change; no relative ampleness statement.
- LeanSearch: “An invertible sheaf ample relative to a scheme morphism stays
  relatively ample after arbitrary base change”: eight hits about smoothness,
  affine morphisms and descent of general morphism properties; no match.
- Loogle: `"IsAmple"`: zero hits.
- Mathlib grep: `relatively.?ample|IsAmple|ample.*base.?change` in
  `AlgebraicGeometry`: zero hits.
- Upstream and side-source rg: `IsAmple|relative.*ample|[aA]mple.*[bB]ase[Cc]hange`.
  The upstream projective/field-relative `AlgebraicGeometry.IsAmple` in
  `Modules.VeryAmple` and its field-extension theorem have stronger hypotheses
  and a different notion; they do not match. Side results include affine
  pullback ampleness, Chow-relative ampleness and relative Serre vanishing;
  none states arbitrary relative base change.
- Upstream rg for the exact item id: no result. Read the existing absolute
  ampleness and tensor-pullback interfaces instead of duplicating them.

The previous worker's reported rejection concerned an unchanged stage-1 item.
This packet adds the missing stage-2 Lean record and module, preserving every
other node field. There is no `STATEMENT-DISPUTED` issue.

## Statement corrected

The returned review identified H3: the original prose said arbitrary schemes but the Lean category
`Scheme` requires the source and target of a morphism to have one common universe. The corrected
node statement explicitly quantifies an arbitrary universe `u` and represents `X`, `T`, and `T'` in
`Scheme.{u}`; this is the standard size encoding and does not impose a geometric hypothesis because
any finite diagram of schemes can be universe-lifted to a common universe. The source is Stacks Tag
0893 together with Tag 01VH, which quantifies over arbitrary schemes. The sole citer
`lem-trf-algebraic-space-ample-local` holds: its scheme tests can likewise be represented in an
arbitrary common universe, so its use of this base-change lemma is unchanged.

## Second reading by Q87

I reread the corrected node, the Lean theorem, and the recorded dependency declarations. The Lean
binders `{X T T' : Scheme.{u}}` and explicit `universe u` render the corrected arbitrary common-u
encoding; `(f : X ⟶ T)` and `(g : T' ⟶ T)` render the two arbitrary morphisms. `L` and
`[L.IsInvertible]` render the invertible module. The premise quantifies exactly over affine opens
`V : T.Opens`, uses the tensor-pullback restriction, and supplies the recorded `IsAmple` predicate.
The conclusion quantifies over every affine `V' : T'.Opens` and uses `pullback.fst`, `pullback.snd`
and tensor pullback exactly for `g'^*L` and its restriction. No geometric hypothesis was added and
no conclusion clause was dropped. The only change from the returned packet is the explicit common
universe correction recorded above; the Lean signature already had this universe-polymorphic form.
