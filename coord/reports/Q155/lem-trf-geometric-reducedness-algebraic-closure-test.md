## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest` states
`AlgebraicGeometry.geometricallyReduced_iff_isReduced_algebraicClosure_baseChange`.
Its only proof is `sorry`; its docstring carries all four steps of the node's proof.
No definition, additional theorem, or changed mathematical statement is introduced.

Hypotheses and clauses, checked against the node and Stacks `varieties.tex`,
Tags 035X (conditions (2), (6), and (7)) and 020I:

- The base field is `{k : Type u} [Field k]`.
- An arbitrary scheme over that field is `(X : Scheme.{u})
  [X.Over (Spec (.of k))]`. Its actual structure morphism is
  `X ↘ Spec (.of k)`; no alternate or arbitrary structure map is substituted.
- A chosen algebraic closure is `{Ω : Type u} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`. `Algebra k Ω` supplies the embedding `algebraMap k Ω`;
  `IsAlgClosure` asserts both algebraic closedness and algebraicity over `k`.
  This permits every chosen closure, rather than fixing `AlgebraicClosure k`.
- Geometric reducedness is precisely Mathlib's
  `GeometricallyReduced (X ↘ Spec (.of k))`. The class uses
  `geometrically IsReduced`, and
  `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` specializes it to
  reducedness of the pullback for every field extension of `k`.
- The chosen base change is
  `pullback (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))`.
  Its reducedness is `AlgebraicGeometry.IsReduced` of that scheme. Thus the two
  sides of `↔` are exactly the two conditions in the node.
- There are no finite-type, quasi-compactness, separatedness, characteristic,
  Noetherian, or nonemptiness binders. In particular empty schemes are admitted.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, in `Mathlib.Algebra.Algebra.Defs`;
  instantiated for two fields, with its canonical ring map `algebraMap`.
- `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over`, in
  `Mathlib.AlgebraicGeometry.Over`, with its structure-morphism notation.
- `def-weil-algebraic-closure`: `IsAlgClosure`, in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, as specified in the dependency's
  `mathlib_match.how`; also read the canonical `AlgebraicClosure` construction.
- `def-pc-geometrically-irreducible`: the recorded secondary declaration
  `AlgebraicGeometry.GeometricallyReduced`, imported through the recorded module
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`.
  Its full class signature and the generic field-base-change equivalence in
  `Mathlib.AlgebraicGeometry.Geometrically.Basic` were read.
- `def-pc-base-change`: the recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` module is imported.
  Its module documentation explicitly identifies the scheme-level base change
  with `Limits.pullback f T.hom` and its projections. Its primary declaration
  `Scheme.Modules.moduleBaseChange` concerns modules, so it is not incorrectly
  used as a scheme constructor. The live module was read with
  `scompile.py --source` because the old local source checkout lacks that file.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced`, in
  `Mathlib.AlgebraicGeometry.Properties`, with reduced section rings and the
  equivalent reduced-stalk criterion.

Proof-only imports retain the available proof plan: `Mathlib.AlgebraicGeometry.Properties`
provides `IsReduced.iff_of_openCover` and `affine_isReduced_iff`;
`Mathlib.AlgebraicGeometry.Pullbacks` provides `pullbackSpecIso` and its projection
identities; `Mathlib.RingTheory.Nilpotent.GeometricallyReduced` provides the
recorded affine-criterion API. The proof dependency
`lem-trf-reducedness-tensor-chosen-algebraic-closure` currently has no recorded
Lean module and therefore contributes no import. It is not needed to state this
item, and no substitute theorem or definition is introduced.

Edge cases checked before writing: the empty scheme and its empty cover are
allowed, and both reducedness conditions hold; arbitrary disjoint unions and
schemes without a finite affine cover are allowed; nonreduced schemes and
reduced schemes over imperfect fields are not silently assumed geometrically
reduced; characteristic zero and positive characteristic are both included;
when the base field is already algebraically closed, the identity closure is
allowed. The shared universe `u` is the recorded scheme and field-extension
convention: the geometric predicate tests fields in the scheme universe, rather
than an unrelated potentially smaller test universe. Larger mathematical data
can be placed in a common universe. No independent universal test type is added.

Searches for an existing exact statement:

- `msearch.py`, leanfinder, query: “A scheme over a field is geometrically reduced
  if and only if its base change to a chosen algebraic closure is reduced”.
  Eight hits: algebra-level `Algebra.isGeometricallyReduced_iff` and related
  declarations, and scheme-level `AlgebraicGeometry.IsReduced`. No scheme-level
  equivalence matching this item.
- `msearch.py`, loogle, query:
  `AlgebraicGeometry.GeometricallyReduced, IsAlgClosure`. Zero hits.
- `msearch.py`, grep, query `GeometricallyReduced|algebraicClosure`, directory
  `AlgebraicGeometry/Geometrically`. Ten hits concern geometric integrality and
  the geometric reducedness definition; no algebraic-closure test.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf`, by the item id and
  by geometric-reducedness/algebraic-closure combinations: no existing exact
  statement. The project's geometric-connectedness algebraic-closure test is a
  different property. The downstream fibre-locus module cites this node in its
  proof docstring, without stating the equivalence.
- `rg` for the proposed full declaration name in Mathlib, upstream, and
  `lean/Sheaf`: no collision.

Validation: the delivered file compiled through the prescribed `scompile.py`
wrapper, both sandbox and library-path checks, with no errors or warnings.
The item copy changes only `lean`, preserves all dependencies and proof steps,
and uses the UTC date reported by the machine (`2026-10-17`).
No statement dispute, new node, or dependency interface repair was needed.

## Second reading by Q155

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
