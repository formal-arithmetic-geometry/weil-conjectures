## Worker report

Item: `lem-trf-geometric-reducedness-algebraic-closure-test`.
Module: `Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest`.
Declaration: `AlgebraicGeometry.geometricallyReduced_iff_isReduced_pullback_algebraicClosure`.
This is one theorem statement with `sorry`; no definitions or proofs are added.
Only the item's `lean` record is changed. No statement correction is needed.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`.
- An arbitrary scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
  Its structure map is `X ↘ Spec (.of k)`.
- A fixed but arbitrary algebraic closure: `(Ω : Type u) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`. This retains the actual chosen extension, rather than replacing it
  by `AlgebraicClosure k`. The class states both algebraic closedness and algebraicity.
- Geometric reducedness: `GeometricallyReduced (X ↘ Spec (.of k))`.
  The read definition is `geometrically IsReduced`; the read lemma
  `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` identifies it with
  reducedness of the pullback for every field extension `L/k`.
- Base change to the specified closure: `pullback (X ↘ Spec (.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))`.
- Reducedness of that scheme: `AlgebraicGeometry.IsReduced` of the displayed pullback.
- Both directions, with no extra clause: the connective is `↔`.
- No finite-type, quasi-compactness, or nonemptiness hypothesis appears. There is no
  characteristic restriction, irreducibility assumption, or implicit auxiliary object.

Dependency declarations read and reused:

- `def-pc-field-extension`: `Algebra` and `algebraMap`,
  `Mathlib.Algebra.Algebra.Defs` (transitively imported).
- `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over`,
  `Mathlib.AlgebraicGeometry.Over`.
- `def-weil-algebraic-closure`: `IsAlgClosure`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`.
- `def-pc-geometrically-irreducible`: recorded module
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`, which publicly imports
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced`; the used declaration is
  `AlgebraicGeometry.GeometricallyReduced`, exactly the reduced variant in its record.
- `def-pc-base-change`: recorded module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, read with
  `scompile.py --source` because it is absent from the older local checkouts. Its module
  docstring explicitly identifies scheme base change as `Limits.pullback f T.hom`, with
  `pullback.snd` its structure map; the statement uses precisely this existing construction.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced`,
  `Mathlib.AlgebraicGeometry.Properties` (transitively imported), defines reducedness on
  all section rings. The accompanying stalk comparison gives the equivalent local form.

Proof-only imports: `Mathlib.AlgebraicGeometry.Pullbacks` supplies the recorded
`pullbackSpecIso`; `Mathlib.RingTheory.Nilpotent.GeometricallyReduced` supplies the affine
geometric-reducedness infrastructure. The reducedness/open-cover and affine-spectrum
criteria are already imported through the statement dependencies. The proof dependency
`lem-trf-reducedness-tensor-chosen-algebraic-closure` has no recorded module yet, so there
is none to import. All four steps of the node's proof are included in the docstring.

Source and edge cases: read `literature/stacks-project/varieties.tex` at
`lemma-geometrically-reduced` (Tag 035X), equivalences (2), (6), (7), and
`lemma-perfect-reduced` (Tag 020I). These impose no finiteness or nonemptiness on X.
The empty scheme is allowed: reducedness is sectionwise and the affine-cover argument
works with an empty cover. A nonreduced scheme is not excluded by a hypothesis; its
closure base change is nonreduced. Positive characteristic and characteristic zero are
both included, as are algebraically closed k with the identity closure extension.
The common universe u is arbitrary and is the universe of the scheme, field, chosen
closure and field tests in Mathlib's definition; there is no smaller independent test
universe that could make the universal condition vacuous.

Searches performed before writing:

- `msearch.py leanfinder`, query: "A scheme over a field is geometrically reduced if and
  only if its base change to a chosen algebraic closure is reduced". Eight hits, chiefly
  `Algebra.isGeometricallyReduced_iff`, `Algebra.IsGeometricallyReduced`, and
  `AlgebraicGeometry.IsReduced`; none is the scheme-level statement.
- `msearch.py leansearch`, query: "A scheme is geometrically reduced over a field iff its
  base change to an algebraic closure is reduced". Eight hits, all algebra-level classes
  and tests or reducedness of schemes; no scheme-level closure criterion.
- `msearch.py loogle`, query: `AlgebraicGeometry.GeometricallyReduced, IsAlgClosure`.
  Zero hits.
- `msearch.py grep`, query: `[Gg]eometrically[Rr]educed|[Gg]eometrically_[Rr]educed`,
  directory `AlgebraicGeometry/Geometrically`. Ten hits: the reduced class and integral
  implications, no closure test.
- Direct `rg` over Mathlib's geometric-property modules and field-theory modules;
  read the full reduced class and generic `geometrically` definition and comparison
  lemmas. No matching theorem.
- Direct `rg` over `WeilConjectures/` and `lean/Sheaf/` for geometric reducedness and
  algebraic closures; hits are consumers and algebra-level statements, not this theorem.
  `grep -rn` for this node's id in `WeilConjectures/` has no hit.
- Exact proposed declaration-name search in Mathlib, `WeilConjectures/`, `lean/Sheaf/`
  and `dag/lean_names_upstream.json`: no hit.

Proof-plan advisory (not a statement fault): the Mathlib match of proof dependency
`lem-trf-affine-geometric-reducedness-criterion` calls an older declaration name
`Algebra.isGeometricallyReduced_iff`. The pinned source actually names the closure test
`Algebra.isGeometricallyReduced_field_iff`. Its module also explicitly records a TODO
for the comparison to *all* field extensions. Thus stage 3 must justify that affine
all-extension step, not infer it from the stale search snippet. This does not affect
this delivery's scheme-level statement, which matches Stacks. That proof dependency
is not a statement dependency of this item and is not edited here.

Validation: the prescribed `scompile.py Q25
lem-trf-geometric-reducedness-algebraic-closure-test <module file>` compiled both its
sandbox check and its library module successfully, with no errors or warnings.

## Second reading by Q25

A fresh in-session reading compared the node text with the final Lean file. This is a
self-check, not a claimed independent reviewer: the dispatcher brief prohibits starting
other agents and assigns independent review to the maintainer after delivery.

The field binders, scheme-over-k instance, and arbitrary chosen `IsAlgClosure` match
all hypotheses. The left side is exactly the dependency's geometric reducedness class;
the right side uses the map from the very same k-algebra structure on Ω, in the order
X ×_Spec(k) Spec(Ω). `IsReduced` concerns that scheme, not its underlying topological
space. `↔` preserves both implications. No finite-type, quasi-compactness,
nonemptiness, or characteristic hypothesis is present. The universe is shared with
Mathlib's field tests and cannot make them smaller than X. All variables and u are
explicitly bound. No mismatches were found or changed in this second pass.
