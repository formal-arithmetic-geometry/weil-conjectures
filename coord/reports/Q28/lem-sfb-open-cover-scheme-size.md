## Worker report

Recorded the exact existing declaration
`AlgebraicGeometry.Scheme.cardinalSize_le_openCover` in
`Sheaf.AlgebraicGeometry.SchemeSizeOpenCoverBound` (source file
`lean/Sheaf/AlgebraicGeometry/SchemeSizeOpenCoverBound.lean`, lines 42–48).
This declaration is already attached to `lem-sfb-scheme-size-open-cover-bound`.
No Lean module is added, no theorem is proved, and only the item's `lean` field changes.
The existing declaration has a `sorry` proof, as appropriate for stage 2.

Hypothesis and clause matching:

- The arbitrary scheme Y is `(X : Scheme.{u})`; only the name changes.
- The arbitrary indexing set I is `{I : Type v}`, with independent explicit universe v.
  No finiteness or nonemptiness condition is imposed.
- Open subsets Y_i are `(U : I → X.Opens)` and the covering equation is
  `(hU : (⨆ i : I, U i) = ⊤)`.
- Their induced open scheme structures are exactly `(U i).toScheme`.
  Mathlib's `Scheme.Opens.toScheme` is `X.restrict U.isOpenEmbedding`, not an
  independently chosen scheme or a chart with extra presentation data.
- The inline invariant s(Z) is `Scheme.cardinalSize Z`, whose full definition is
  `max Cardinal.aleph0 (max (Cardinal.mk Z.affineOpens)
  (⨆ V : Z.affineOpens, Cardinal.mk ↥Γ(Z, V.1)))`.
  `Z.affineOpens` consists of actual affine open subsets, and Γ denotes structure
  sheaf sections, exactly as in the item. The node's max of three cardinals is
  rendered by nested `max`.
- The conclusion is `Cardinal.lift.{v} X.cardinalSize ≤ max Cardinal.aleph0
  (max (Cardinal.lift.{u} (Cardinal.mk I))
  (⨆ i : I, Cardinal.lift.{v} (U i).toScheme.cardinalSize))`.
  The lifts merely compare cardinals in universe max(u,v); neither scheme nor
  index universe is restricted, and no cardinal bound is changed.
- The empty covering is permitted: with I empty its union is bottom, so hU forces
  top = bottom and X has no points. The index cardinal and supremum are zero;
  the right side is aleph0. The definition also gives cardinalSize of the empty
  scheme equal to aleph0 (its only open has a singleton section ring).

Declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, the recorded declarations of `def-pc-scheme`.
  The structure supplies local affine presentations as a locally ringed space.
- `Sheaf.AlgebraicGeometry.SchemeCardinalSize`:
  `AlgebraicGeometry.Scheme.cardinalSize`, recorded by
  `def-sfb-scheme-cardinal-size`; its signature, body, and docstring were read.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `Scheme.affineOpens` and
  `IsAffineOpen`, used by the preceding invariant.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, whose signature,
  definition, docstring, and `toScheme_presheaf_obj` were read.
- `Sheaf.AlgebraicGeometry.SchemeSizeOpenCoverBound`:
  `AlgebraicGeometry.Scheme.cardinalSize_le_openCover`, whose full signature,
  imports, universe declarations, and docstring were read.

Source checked: `literature/stacks-project/sets.tex`, section-categories-schemes
(lines 310–327) for the invariant, and lemma-bound-size, Tag 000Q (lines 524–563)
for the covering bound and finite-affine refinement argument. The item and existing
Lean declaration both already include aleph0 to cover the empty covering; no
statement correction is needed. The theorem's existing docstring refers to this
item as its proof-plan prerequisite. Reusing that exact statement introduces no
new theorem or import cycle: the mathematical proof to implement is the six-step
proof already recorded on this item (finite affine refinements, finite-list
counting, and injectivity of sheaf restrictions), rather than invoking the same
declaration as its own proof. This delivery does not change that existing module.

Edge cases checked: empty I; empty X with either empty or nonempty cover;
repeated opens and empty cover members; singleton identity covering;
non-quasi-compact and non-quasi-separated X; and index universe independent of the
scheme universe. All are admitted without extra assumptions. No node fault or
STATEMENT-DISPUTED condition remains.

Searches (2026-10-24):

- msearch.py / LeanFinder: “The cardinal size of a scheme is bounded by the maximum
  of aleph zero the size of any open covering and the supremum of the cardinal
  sizes of its open subschemes”. Eight hits concern open covers, their open ranges,
  affine covers, and covering equations; none states this bound.
- msearch.py / Loogle: `"Scheme", "Cardinal"`. Zero hits.
- msearch.py / grep, Mathlib/AlgebraicGeometry:
  `(size|cardinal).*(openCover|open.cover)|(openCover|open.cover).*(size|cardinal)`.
  Zero hits.
- msearch.py / LeanSearch: “Bound the cardinal size of a scheme by the cardinality
  of an open cover and the supremum of the sizes of its open subschemes”. Eight
  hits concern compactness, covers, and structural SizeOf, not the cardinal bound.
- rg over `lean/WeilConjectures` and `lean/Sheaf`:
  `cardinalSize|cardinal.*[Oo]pen|[Oo]pen.*cardinal`. Found the exact existing
  `SchemeSizeOpenCoverBound.lean` declaration and the invariant in
  `SchemeCardinalSize.lean`; other hits are consumers or unrelated results.
- grep over `lean/WeilConjectures` for the item id: no hit.
- rg for `cardinalSize_le_openCover` in Mathlib, WeilConjectures, and
  `dag/lean_names_upstream.json`: no competing declaration. Read the existing
  node `lem-sfb-scheme-size-open-cover-bound` and verified it names the exact
  project declaration. No missing definition or dependency module is needed.

Validation: the prescribed deliver2.py dry run checks the existing declaration
with a server-side module-mode #check through scompile.py, and runs server
preflight. No standalone Lean file is delivered.

## Second reading by Q28

Author's second pass, not an independent review: reopened the item, its existing
counterpart node, SchemeSizeOpenCoverBound.lean, SchemeCardinalSize.lean, and
Mathlib's open-restriction definition. Compared every binder and term against the
clause mapping above. The Y-to-X renaming is immaterial; the independently sized I,
actual open subsets, covering equation, induced restrictions, all three terms of
the size invariant, all three terms of the upper bound, and the empty-cover case
match. No compactness, separatedness, or nonempty-index assumption is added.
No mismatch or code change was needed. The maintainer supplies the independent
review, as specified in the worker brief; no other agent was started.
