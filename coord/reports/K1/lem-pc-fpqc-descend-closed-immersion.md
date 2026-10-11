## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent` states
`AlgebraicGeometry.isClosedImmersion_of_fpqc_cover`. It introduces schemes `X` and
`S` in universe `u`, a morphism `f : X ⟶ S`, an index type `I : Type v`, a family
`S' : I → Scheme.{u}`, and morphisms `g : ∀ i, S' i ⟶ S`. The hypothesis
`hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S` renders the fpqc covering
condition. The hypothesis
`h : ∀ i, IsClosedImmersion (pullback.snd f (g i))` renders that every base change
`X ×_S S' i → S' i` is a closed immersion. The conclusion `IsClosedImmersion f`
renders that `f` is a closed immersion.

The dependency notions are used as follows: `Scheme` is Mathlib's
`AlgebraicGeometry.Scheme` (node `def-pc-scheme`); the fpqc covering is Mathlib's
`AlgebraicGeometry.Scheme.fpqcPrecoverage` (node `def-weil-pbc-fpqc-covering`);
the fibre product and base-change projection are Mathlib's
`CategoryTheory.Limits.pullback` and `pullback.snd` (node `def-pc-fibre-product`);
and closed immersion is Mathlib's `AlgebraicGeometry.IsClosedImmersion` (node
`def-weil-closed-immersion`).

Edge cases checked: `I` is an arbitrary universe-polymorphic type, including the
empty family (which can only cover an empty target); singleton covers and identity
covers reduce to the expected base-change statements; `pullback.snd` has the
required source and target even when schemes are empty; no finiteness or
nonemptiness hypothesis was added.

Searches for an existing declaration: `msearch.py ... leanfinder "closed immersion
descends along fpqc covering"` found only generic descent declarations for open
immersions, universally closed morphisms, and composition lemmas, with no exact
closed-immersion theorem. `msearch.py ... loogle "IsClosedImmersion fpqc"` returned
no hits. `rg` over Mathlib AlgebraicGeometry, `WeilConjectures/`, and `lean/Sheaf/`
found no theorem with this family-level fpqc descent statement. The resulting
declaration is therefore new.

The proof is intentionally `sorry` at stage 2, as required. Its source is Stacks
Project `descent.tex`, Lemma Tag 02L6.

## Second reading by K1

Independent comparison with the node and Stacks Project, Descent, Lemma Tag 02L6:

- The schemes `X` and `Y` are `{X S : Scheme.{u}}`; `S` is the node's `Y`.
- The morphism `f : X \to Y` is `(f : X ⟶ S)`, with no property assumed of it.
- The indexing set is `{I : Type v}`; the schemes `Y_i` and arrows `g_i : Y_i \to Y`
  are `(S' : I → Scheme.{u})` and `(g : ∀ i, S' i ⟶ S)`.
- The fpqc covering hypothesis is
  `(hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)`. The dependency node
  `def-weil-pbc-fpqc-covering` records this Mathlib precoverage as equivalent to
  the Stacks Tag 022B condition: flat arrows and a finite affine refinement above
  every affine open. The Mathlib source gives the same condition via
  `propQCPrecoverage @Flat` and `QuasiCompactCover`.
- For each `i`, the node's base change `f_i : X ×_Y Y_i → Y_i` is
  `pullback.snd f (g i)`; the predicate in
  `(h : ∀ i, IsClosedImmersion (pullback.snd f (g i)))` is the dependency node's
  closed immersion. Stacks writes `Y_i ×_Y X`, canonically isomorphic to this
  pullback, with the same projection to `Y_i`.
- The sole conclusion, `f` closed immersion, is `IsClosedImmersion f`.

Verdict: every object, hypothesis, and conclusion clause matches; no stronger
assumption or weaker conclusion was found. The source lemma imposes no ambient
field, Noetherian, separated, or finite-type condition. Universes `u` and `v`
leave the scheme and index types polymorphic. `I` may be empty; then an fpqc
cover can only cover an empty target. Empty source and target schemes are allowed.
There is no numerical parameter or characteristic restriction. The chosen
pullback works for empty schemes as well.

I reopened the four dependency node signatures and checked Mathlib's
`fpqcPrecoverage`, `QuasiCompactCover`, and `IsClosedImmersion` definitions, as
well as `pullback.snd`. Independent searches used LeanFinder for "closed embedding
schemes fpqc local on target" (only Zariski-local and unrelated results), Loogle
for `AlgebraicGeometry.IsClosedImmersion fpqc` (no matching declaration), and `rg`
for `IsClosedImmersion` with `fpqc`, `descend`, or `DescendsAlong` across Mathlib,
`WeilConjectures/`, and `lean/Sheaf/` (no matching theorem). No new notion or
dependency module is needed. The only repair was to expand the theorem docstring
to carry all three node proof steps and their named dependencies. The Lean
signature and node's `lean.statement` were already verbatim equal and unchanged.

## Earlier second reading (a previous round; superseded)

I reread the node and module independently. The binders match the node's `f`,
indexed fpqc family, and all base-change closed-immersion hypotheses exactly. The
conclusion is exactly `IsClosedImmersion f`; no hypothesis or clause is added,
dropped, or weakened. The pullback projection is `pullback.snd f (g i)`, so its
source is the base change and its target is `S' i` as required.
