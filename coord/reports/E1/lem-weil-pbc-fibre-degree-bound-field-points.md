## Worker report

The module `Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints` states
`AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_iff_fieldPoints`. Its sole theorem has a
`sorry` proof; no definitions or additional theorems are introduced. The node is unchanged
except for `lean`.

Hypothesis and clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`; arbitrary scheme morphism: `(f : X ⟶ Y)`.
  No affine, finite type, separated, quasi-compact, or finite assumption on f is added.
- Nonnegative integer n: `(n : ℕ)`, including zero.
- Condition (1): `BoundsFiberDegrees f n`, using the recorded dependency directly.
  Its body is `∀ y : Y, IsFinite (f.fiberToSpecResidueField y) ∧
  (f.fiberToSpecResidueField y).finrankΓ ≤ n`.
- Equivalence of (1) and (2): `↔`.
- Every field and every field-valued point: `∀ (K : Type u) [Field K]
  (g : Spec (CommRingCat.of K) ⟶ Y)`. The universe u is explicit and arbitrary, as in the
  dependency and Mathlib's category `Scheme.{u}`; K is not restricted to finite,
  algebraically closed, or residue fields.
- The fibre product X_K: `pullback f g`; its K-structure is specifically
  `pullback.snd f g`, the second projection, not the first projection.
- Finiteness over K: `IsFinite (pullback.snd f g)`.
- Dimension at most n: `(pullback.snd f g).finrankΓ ≤ n`.
  The source definition of `Scheme.Hom.finrankΓ` is
  `letI := h.ΓAlgebra; Module.finrank R Γ(Z, ⊤)` for `h : Z ⟶ Spec R`.
  Its `ΓAlgebra` is `((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom.toAlgebra`, exactly the
  algebra structure induced by the projection. The separate finiteness conjunct prevents
  `finrank` on an infinite-dimensional space from satisfying the condition spuriously.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FiberDegreeBound`,
  `AlgebraicGeometry.Scheme.Hom.BoundsFiberDegrees` (also read the recorded main declaration
  `HasUniversallyBoundedFibers`, which existentially quantifies this bound).
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.finrankΓ` and `ΓAlgebra`.

The one import of the recorded dependency supplies all these transitively. All signatures
and docstrings were read in the local source trees (the dependency in `lean/Sheaf`).
The local `literature/stacks-project/morphisms.tex` is absent; the source was instead read
at https://stacks.math.columbia.edu/tag/03J5. The node is precisely the equivalence (1)/(2),
not the further point-count and residue-degree consequences. No correction is needed.
The theorem docstring gives all six proof steps of the node, with their dependency IDs.

Edge cases checked: n = 0 is allowed; an empty source has zero-dimensional global sections
on every base change, while a nonempty finite fibre has positive dimension. An empty target
makes both quantifications vacuous (and any morphism to it has empty source). Finite
nonreduced fibres are allowed and their full algebra dimension, not cardinality of their
underlying points, is used. Arbitrary characteristics and field extensions are allowed.
The morphism f need not itself be finite or affine.

Searches for an existing statement:

- LeanFinder via `msearch.py`: "A bound on degrees of fibres of a scheme morphism holds if
  and only if its pullback to every field-valued point is finite with bounded dimension of
  global sections". Eight hits: finite underlying fibre, finite preimage of singleton,
  finite_appTop_of_universallyClosed, finite-type and finite pullback projections, and
  discrete_fiber. None states the equivalence.
- LeanSearch via `msearch.py`: "scheme fibre degree bounded for every field valued point".
  UNAVAILABLE (Internal Server Error); no absence verdict inferred.
- Loogle via `msearch.py`: `AlgebraicGeometry.Scheme.Hom.finrankΓ`. Zero hits, unknown
  identifier; this is a source-project definition, verified by reading its implementation.
- Mathlib grep via `msearch.py`: `03J5|universally.?bounded|BoundsFiberDegrees`, in
  AlgebraicGeometry: zero hits.
- `rg` of the source `WeilConjectures` and project `lean/Sheaf` for
  `03J5|BoundsFiberDegrees|boundsFiberDegrees|universally.?bounded`: only the recorded
  bound definition and the composition-of-bounds module in `lean/Sheaf`; no equivalence.
- `grep -rn` of the item's ID in source `WeilConjectures`: no hits.
- `rg` for `fiberDegree|FibreDegree|fibreDegree|FibreDegreeBound|fiberDegreeBound` in
  source AlgebraicGeometry and `lean/Sheaf`: the source's affine fibre-degree definition,
  base-change facts, finite-flat comparisons and applications, but no statement matching
  this general scheme-morphism equivalence. Read `finrankΓ` and `ΓAlgebra` there for reuse.

No new nodes, dependency modules, statement corrections, or disputed statements.

## Second reading by E1

I independently read the node, Stacks Tag 03J5, the dependency records, and
`Sheaf/AlgebraicGeometry/BoundsFiberDegreesFieldPoints.lean`.

The node introduces arbitrary schemes `X` and `Y`, a morphism `f : X ⟶ Y`, and
`n ≥ 0`.  These render as `{X Y : Scheme.{u}}`, `(f : X ⟶ Y)`, and `(n : ℕ)`;
there are no additional finiteness, separatedness, affine, or characteristic
assumptions.  Clause (1), that `n` bounds every fibre degree, renders as
`BoundsFiberDegrees f n`, whose dependency expands to
`∀ y, IsFinite (f.fiberToSpecResidueField y) ∧
(f.fiberToSpecResidueField y).finrankΓ ≤ n`.  Clause (2) quantifies
`∀ (K : Type u) [Field K] (g : Spec (CommRingCat.of K) ⟶ Y)` and requires
`IsFinite (pullback.snd f g) ∧ (pullback.snd f g).finrankΓ ≤ n`.  Here
`pullback.snd f g : pullback f g ⟶ Spec (CommRingCat.of K)` is exactly the
second projection specified by the node, and `finrankΓ` uses its induced
`K`-algebra structure.  The outer connective is exactly `↔`, with the same
quantifier order and no omitted or strengthened clause.  The signature in the
node's `lean.statement` is verbatim the theorem signature.

The source page says “for every morphism Spec(k) → Y, where k is a field” and
that the fibre product is finite over k of degree at most n (Stacks Tag 03J5,
Lemma 29.58.2).  The Lean orientation `X ×_Y Spec K` is canonically the same
pullback as the source's displayed `Spec K ×_Y X`; the node explicitly fixes
its structure map as the second projection, so this orientation is intentional.

I checked edge cases: `n = 0` is admitted; arbitrary field characteristic and
field extensions are admitted; no algebraic-closedness or finite-field
hypothesis is present; empty schemes and empty fibres satisfy the same vacuous
quantifiers; finite nonreduced fibres are measured by the full global-sections
vector-space dimension; and no assumption that `f` itself is finite or affine
is introduced.  The universe `Type u` matches `Scheme.{u}` and permits every
field occurring as an object of this scheme category.

The dependency declarations were checked in their defining files.  `BoundsFiberDegrees`
is the recorded fibrewise predicate in `FiberDegreeBound.lean`; `Spec`, scheme
pullbacks and `pullback.snd` are the recorded Mathlib notions; and `IsFinite`
and `finrankΓ` are used with exactly the projection and algebra structure named
by the node.  No dependency record was unusable and no private replacement is
present.

I searched the source repository, project `lean/Sheaf`, and Mathlib with `rg`
for `03J5`, `BoundsFiberDegrees`, `boundsFiberDegrees`, and fibre-degree/`finrankΓ`
variants.  I also ran LeanFinder (only unrelated finite-fibre results), Loogle
(unknown identifier/no match), LeanSearch (service unavailable), and Mathlib
grep (no match).  No existing declaration states this equivalence.  The
Stacks page was read directly at https://stacks.math.columbia.edu/tag/03J5.

No mismatch was found, so no source, statement, dependency, or module change
was needed.  The theorem compiles cleanly with only its permitted `sorry`.
