## Worker report

The module `Sheaf.AlgebraicGeometry.WeilRestrictionGeometricProperties` states
`AlgebraicGeometry.weilRestriction_geometric_properties`, with its entire proof `sorry`.
No definitions, auxiliary theorems, node corrections, or dependency repairs are needed.
The declaration docstring includes the eleven-step proof plan of the node.

Hypothesis and clause correspondence:

- Schemes S, S', Z, W: `{S S' Z W : Scheme.{u}}`, with the universe explicitly declared.
- Finite locally free p:S'→S: `(p : S' ⟶ S) [p.IsFiniteLocallyFree]`.
  The recorded upstream class extends `IsFinite p`, `Flat p`, and
  `LocallyOfFinitePresentation p`, exactly the dependency definition.
- Z over S' and W over S: `(z : Z ⟶ S') (w : W ⟶ S)`.
- W represents the indicated functor by natural bijections: `hrep : Nonempty
  (yoneda.obj (Over.mk w) ≅ (Over.pullback p).op ⋙ yoneda.obj (Over.mk z))`.
  At X/S the left presheaf is Hom_S(X,W). The right presheaf is
  Hom_{S'}(X×_S S',Z), since the actual `Over.pullback p` has object
  `Over.mk (pullback.snd X.hom p)`. Its map is the canonical pullback lift, so naturality
  is for the specified base-change maps, rather than arbitrary pointwise bijections.
  An isomorphism in Type is exactly a bijection; `Nonempty` states its existence and
  does not construct or choose any scheme or arbitrary map.
- Separated implication: `(IsSeparated z → IsSeparated w)`.
  `IsSeparated` is defined by `IsClosedImmersion (pullback.diagonal f)`.
- Local finite type implication: `(LocallyOfFiniteType z → LocallyOfFiniteType w)`.
- Smooth implication: `(Smooth z → Smooth w)`.
- Quasi-compact implication with locally Noetherian base:
  `(IsLocallyNoetherian S → QuasiCompact z → QuasiCompact w)`.
  The Noetherian hypothesis is confined to this conjunct, so the first three clauses
  apply independently over arbitrary bases. Mathlib's `QuasiCompact` tests inverse
  images of compact opens; the recorded affine criterion identifies this with the
  affine-open finite-subcover definition in the node.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (full class and docstring read).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and their universal-property interface.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- Additional existing interfaces used directly, without a duplicate definition:
  `Mathlib.CategoryTheory.Comma.Over.Pullback`, `CategoryTheory.Over.pullback`;
  `Mathlib.CategoryTheory.Yoneda`, `CategoryTheory.yoneda`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `AlgebraicGeometry.IsSeparated`.

All stated proof-dependency modules (including Mathlib-match modules) are imported
with ordinary `import`; statement dependency modules have `public import`.
Unstated proof nodes are not imported; their roles remain in the proof docstring.

Edge cases checked before writing: no positive rank, nonempty scheme, surjectivity of p,
Noetherian hypothesis on the first three clauses, or finite-type/quasi-compact hypothesis
on Z is imposed. If p has rank zero, its source and Z are empty and the represented
functor is terminal, giving W≅S; every conclusion holds for the identity. The empty base
and empty test scheme remain allowed. With p the identity this is the original scheme
up to its representing isomorphism. All schemes and test schemes use the same arbitrary
universe u, so this does not quantify over an accidentally smaller test universe.

Searches for an existing statement:

- `msearch.py ... leansearch "Weil restriction of scalars along a finite locally free
  morphism preserves separatedness smoothness local finite type and quasi compactness"`:
  eight hits about module scalars and open restrictions; no matching theorem.

- `msearch.py ... leanfinder "Representable Weil restriction along finite locally free
  morphisms preserves separated locally finite type smooth quasi compact"`: eight hits
  about ordinary base change, smooth algebras, and finite morphisms; no Weil restriction.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.weilRestriction,
  AlgebraicGeometry.Smooth"`: zero hits, unknown weilRestriction identifier.
- `msearch.py ... grep "weilRestriction|WeilRestriction" AlgebraicGeometry`: zero hits.
- `rg -n 'weilRestriction|WeilRestriction|weil_restriction'` in both
  `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`: no matches.
- Item-id search in `lean/WeilConjectures`: no matches. Additional case-insensitive
  "Weil restriction / restriction of scalars" search finds only coefficient restriction,
  not a representing functor or a preservation theorem. Upstream-name-index inspected.

Source check: opened the primary-source scan linked by the node,
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
PDF pages 201–204, especially Proposition 5 on pages 201–202. Its four selected
properties and additional assumption for quasi-compactness agree with this node.
The delivery retains the source statement verbatim. No statement dispute identified.

Validation: server per-file compile via the prescribed `scompile.py`; dry-run preflight
and final delivery via `deliver2.py`. Results are recorded below after completion.

Server compile completed successfully for both the sandbox check and library module;
no errors or warnings were reported. Only the `lean` field differs from the base node.

## Second reading by Q124

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
