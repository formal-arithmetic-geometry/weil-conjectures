## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SeparatedEtaleChart.lean` states
`AlgebraicGeometry.AlgebraicSpace.separated_etale_chart` with a `sorry` proof. It
adds no definitions. The node's stage-1 split is preserved; this delivery adds
only the node's `lean` record and this module.

Hypothesis and clause correspondence:

- `{S : Scheme.{u}}` is the base scheme from `def-pc-scheme`; `E :
  AlgebraicSpace S` is the algebraic space from `def-trf-algebraic-space`.
- `U : Over S` is the specified S-scheme chart. `[Scheme.IsSeparated U.left]`
  is absolute separatedness of its underlying scheme, i.e. separatedness over
  the terminal scheme, with no separatedness assumption on `S` or `E`.
- `u : yoneda.obj U ⟶ E.obj.obj` is the map `h_U → E`, and `hu : IsEtale u`
  is the recorded representable étale hypothesis.
- The first conclusion is
  `AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)`
  applied to the canonical diagonal map
  `pullback.lift (𝟙 (yoneda.obj U)) (𝟙 (yoneda.obj U)) : h_U → h_U ×_E h_U`.
  Thus every scheme test of the diagonal is represented by a scheme closed
  immersion, exactly the representable separatedness clause.
- For every `C : Over S` and `c : h_C → E`, the second conclusion supplies
  `W : Over S`, `p : W ⟶ C`, and `q : h_W ⟶ h_U` with
  `IsPullback q (yoneda.map p) u c`; this is the scheme representing
  `C ×_E U`. The conjunct `IsSeparated p.left` says its projection to `C` is
  separated. No condition on `C` beyond being an S-scheme is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (the scheme and scheme morphism types).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`, and
  `AlgebraicGeometry.AlgebraicSpace.IsEtale`; the module docstrings define
  scheme-test representability and representable étaleness.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the recorded
  `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsSeparated`, and
  `AlgebraicGeometry.Scheme.IsSeparated` declarations. The latter is the
  absolute separatedness class used in the hypothesis; `IsSeparated p.left`
  is the separated morphism predicate in the conclusion.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its `lift`, and `CategoryTheory.IsPullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (the recorded
  `def-weil-closed-immersion` match): `AlgebraicGeometry.IsClosedImmersion`.
- Proof leaves `lem-weil-pbc-separated-cancellation` and
  `lem-weil-pbc-closed-immersion-base-change` were read as their recorded
  Mathlib matches `AlgebraicGeometry.IsSeparated.of_comp` and
  `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`; their
  statements are used in the docstring proof route and need no extra module.

Edge cases checked before writing: empty `U` and empty `C` (the represented
fibre products and empty diagonals are allowed), `u` the identity chart of a
scheme, a disjoint union of separated affine charts, and a non-separated target
`E`. The latter confirms that no separatedness of `E` or `S` is smuggled in.
Dropping `[Scheme.IsSeparated U.left]` admits a doubled-origin scheme mapping to
the terminal scheme, so that hypothesis is necessary. No affine,
quasi-compact, finite-type, Noetherian, or nonemptiness hypothesis was added.
Universes are explicit and the test schemes use the same `u` as the site.

Searches made on 2026-10-18:

- `msearch.py ... leanfinder "separated representable etale morphism from an
  absolutely separated scheme to an algebraic space"`: eight scheme-level hits
  (`AlgebraicGeometry.IsEtale`, `IsSeparated`, and related classes), with no
  algebraic-space chart theorem.
- `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace.IsSeparatedPresheafMap,
  IsClosedImmersion, IsSeparated"`: zero hits; Loogle reported the project
  helper as unknown, so it was not used in the final statement.
- `msearch.py ... grep "IsSeparatedPresheafMap|diagonalPresheafMap" Sheaf/`:
  no Mathlib hits. Direct `rg` in the project found the existing helper module,
  which was expanded canonically as the pullback diagonal instead of copied.
- `rg` in `WeilConjectures/` for the item, algebraic spaces, and separated étale
  charts found no matching source declaration. The existing project
  `IsSeparatedPresheafMap` helper was read, but the final statement uses the
  same canonical map and `IsRepresentableWith` expression directly.
- The stage-1 node search records (LeanFinder, Loogle, LeanSearch, and Mathlib
  grep) were read; all reported only scheme/ring separatedness results and no
  algebraic-space theorem.

The source field in the reviewed stage-1 node still mentions Morphisms Tag
01UA, although the stage-1 review records that 01UA is the unrelated
fppf-open lemma and identifies the correct 01KV/01QR inputs. The source field is
maintainer-owned and is unchanged by this stage-2 delivery.

No `STATEMENT-DISPUTED` issue, dependency repair, new node, or statement
correction was needed. The module compiled cleanly with the prescribed
`scompile.py` wrapper and has only the expected `sorry` proof.

## Second reading by N9

I reread the node, its four clauses, and the compiled declaration. The
`Scheme.IsSeparated U.left` instance is exactly absolute separatedness; `hu`
is the representable étale assumption; the first conjunct is the diagonal
closed-immersion test after every scheme base change; and the second conjunct
introduces precisely a representing scheme and its separated projection for
an arbitrary `C` and `c`. The pullback square has the same four maps and order
as the algebraic-space definition. No hypothesis or conclusion was added,
dropped, weakened, or strengthened, and no private copy of a project notion
remains in the statement.
