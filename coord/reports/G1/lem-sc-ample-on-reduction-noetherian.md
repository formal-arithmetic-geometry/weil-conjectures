## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AmpleOnReductionNoetherian.lean` states the
ampleness equivalence from Stacks Lemma 09MS.  It also declares the named auxiliary
statement `tensorPullback_isInvertible`, supplying the parenthetical fact in the node
that the pullback of an invertible module is invertible; its proof is `sorry` for stage 2.

The main theorem binds a morphism `i : Z ⟶ X`, the closed immersion instance
`[IsClosedImmersion i]`, local Noetherian hypotheses for both schemes, compactness
(quasi-compactness) hypotheses for both schemes, and `hi : IsHomeomorph i.base`.
It binds `L : X.Modules` with `[L.IsInvertible]`.  Its `letI` installs the auxiliary
invertibility statement for `((Scheme.Modules.tensorPullback i).obj L)`, and the
conclusion is exactly `IsAmple Z (i^*L) ↔ IsAmple X L`, with pullback rendered by the
project declaration `Scheme.Modules.tensorPullback`.

Dependencies used are `AlgebraicGeometry.IsClosedImmersion` from
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
`AlgebraicGeometry.IsLocallyNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`,
`AlgebraicGeometry.Scheme`/`Scheme.Hom` from Mathlib, and
`AlgebraicGeometry.Scheme.Modules.IsInvertible` from
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`.  The project definitions
`Scheme.Modules.tensorPullback` and `Scheme.Modules.IsAmple` are imported from
`Sheaf.AlgebraicGeometry.TensorPullback` and `Sheaf.AlgebraicGeometry.Ample`.

Edge cases checked: `n = 0` and the empty scheme are handled by the imported `IsAmple`
definition; no nonemptiness or positive-dimension assumption is added.  Compactness
is represented by Mathlib's `CompactSpace`, and homeomorphism is the exact underlying
continuous-map condition `IsHomeomorph i.base`.

Searches: `msearch.py ... leanfinder "invertible sheaf is ample if its restriction ..."`
returned no matching theorem; `msearch.py ... loogle "IsAmple, ample reduction"` and
Mathlib AlgebraicGeometry grep found no ampleness notion.  `rg` over
`WeilConjectures/` and project `lean/Sheaf` found no existing 09MS statement; only the
project's `Scheme.Modules.IsAmple` definition and unrelated ample lemmas were present.
The node's recorded dependency declarations were inspected and used as above.

## Earlier second reading (a previous round; superseded)

The theorem signature was compiled remotely with `scompile.py`; the dry run is the
required preflight and server-compile check.

## Second reading by G1

I reread the node statement, its dependency records, the Lean module, and Stacks
Cohomology of Schemes Lemma 09MS (coherent.tex, `lemma-ample-on-reduction`).
The correspondence is:

- `i : Z → X` is rendered by `(i : Z ⟶ X)` with `Z X : Scheme.{u}`.
- Closed immersion is the instance `[IsClosedImmersion i]`, using Mathlib's
  `AlgebraicGeometry.IsClosedImmersion`.
- Noetherian hypotheses are `[IsLocallyNoetherian Z]` and
  `[IsLocallyNoetherian X]`, together with `[CompactSpace Z]` and
  `[CompactSpace X]`.  Mathlib's `IsLocallyNoetherian` is the dependency-node
  notion, and `CompactSpace` is precisely quasi-compactness of the underlying
  scheme topology (the node's separate locally-Noetherian and quasi-compact
  clauses).
- The homeomorphism hypothesis is `(hi : IsHomeomorph i.base)`, exactly the
  underlying continuous-map homeomorphism in the node and source.
- The invertible module is `(L : X.Modules) [L.IsInvertible]`, using the
  dependency declaration `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- Pullback is `((Scheme.Modules.tensorPullback i).obj L)`, the recorded
  `def-pc-module-pullback` declaration, and the auxiliary theorem
  `tensorPullback_isInvertible i L` supplies the parenthetical invertibility
  assertion in the node via the `letI` binder.
- The conclusion is exactly
  `AlgebraicGeometry.Scheme.Modules.IsAmple Z
  ((Scheme.Modules.tensorPullback i).obj L) ↔
  AlgebraicGeometry.Scheme.Modules.IsAmple X L`, preserving the node's
  quantifier order and both directions.

No mismatch was found and no source or Lean change was needed.  The empty scheme
and zero module are admitted by the imported definitions; tensor power index
`n = 0` is handled by `IsAmple`'s explicit positive-index condition, and no
characteristic, nonemptiness, dimension, or universe restriction is added.
The source's Noetherian and homeomorphism assumptions are the same hypotheses.

I searched Mathlib AlgebraicGeometry, the project `lean/Sheaf`, and
`WeilConjectures/` for `09MS`, `ample-on-reduction`, and equivalent
closed-immersion/homeomorphism ampleness statements; none exists.  LeanFinder/
Loogle searches for the same equivalence found only unrelated reducedness or
ampleness declarations.  Thus this module is not an existing declaration.

The module compiles cleanly with `scompile.py`; its only proof obligations are
`sorry`s for the stage-2 statement delivery.
