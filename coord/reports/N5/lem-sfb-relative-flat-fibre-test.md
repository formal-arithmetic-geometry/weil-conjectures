## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFlatFibreTest` states
`AlgebraicGeometry.Scheme.Hom.relative_flat_fibre_test`, with one `sorry` and
no new definitions. Only the item's `lean` field changes.

Source read: `literature/stacks-project/more-morphisms.tex`,
`theorem-criterion-flatness-fibre` (Tag 039C), including its hypotheses,
and `lemma-base-change-criterion-flatness-fibre` (Tag 05VJ), including the
fibrewise description and the sentence that all assumptions persist after
arbitrary base change. The structure sheaf is finitely presented over itself;
its stalk at an actual scheme point is nonzero, so the nonzero-stalk proviso
in 039C adds no hypothesis here. No openness assertion is part of this node.

Hypotheses and clauses, in order:

- The schemes are `{S X Y : Scheme.{u}}`; the three morphisms are
  `(p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)`.
- The triangle commutes by `(hf : f ≫ q = p)`, the categorical expression for
  q composed with f equals p.
- Flatness and local finite presentation of p are `[Flat p]` and
  `[LocallyOfFinitePresentation p]`. Local finite type of q is
  `[LocallyOfFiniteType q]`.
- The first conjunct quantifies `∀ x : X`. Its base point s is literally `p x`.
  The source and target fibres are `p.fiber (p x)` and `q.fiber (p x)`, expanded
  by Mathlib as pullbacks along `S.fromSpecResidueField (p x)`.
- The fibre morphism is the actual `pullback.map` with components f, the identity
  of the residue-field spectrum, and `𝟙 S`. Its first commutativity proof is
  `by simpa only [Category.comp_id] using hf.symm`; the second is `by simp`.
  These are only witnesses needed to form the canonical map, not new hypotheses.
- The unique fibre point is `p.asFiber x`. Mathlib defines it by the inverse
  homeomorphism `p.fiberHomeo (p x)` applied to `⟨x, rfl⟩`; its projection is x.
  Thus `(f.stalkMap x).hom.Flat ↔ (... .stalkMap (p.asFiber x)).hom.Flat`
  is exactly the first flatness equivalence.
- The second conjunct quantifies `∀ (T : Scheme.{u}) (h : T ⟶ S)`. It imposes no
  flatness, finite type, finite presentation, Noetherian or compactness condition
  on T or h. Universe u is arbitrary and common to all schemes, as in Mathlib's
  pullback API; every finite collection of schemes fits in a common universe.
- The base changes are literally `pullback p h` and `pullback q h`; their maps
  to T are `pullback.snd p h` and `pullback.snd q h`.
- The three stated preservation conclusions are respectively
  `Flat (pullback.snd p h)`,
  `LocallyOfFinitePresentation (pullback.snd p h)`, and
  `LocallyOfFiniteType (pullback.snd q h)`.
- The final quantifier is `∀ x' : ↥(pullback p h)`. The induced f_T is
  `pullback.map p h q h f (𝟙 T) (𝟙 S) ...`; its components specify the canonical
  map of these pullbacks. The base point t is `(pullback.snd p h) x'`.
- The final fibre map is again `pullback.map`, now between the pullbacks of
  the two projections along `T.fromSpecResidueField ((pullback.snd p h) x')`.
  Its first component is the canonical f_T above. The proof `by simp` certifies
  f_T commutes with the projections to T, from the defining pullback equations.
- The unique point of the iterated fibre is `(pullback.snd p h).asFiber x'`.
  The last equivalence asserts flatness of the actual stalk map of f_T at x'
  if and only if flatness of its actual fibre stalk map at that point.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`,
  `Flat.iff_flat_stalkMap` and `Flat.stalkMap`; pointwise flatness is
  `(f.stalkMap x).hom.Flat`. The same module provides the proof dependency
  `Flat.isStableUnderBaseChange` and its pullback-projection instances.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; this module also publicly imports
  `Morphisms.QuasiSeparated`, exposing the Mathlib proof dependencies of
  lem-weil-pbc-qcqs-morphism-permanence, including
  `locallyOfFinitePresentation_isStableUnderBaseChange`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  proof dependency `locallyOfFiniteType_isStableUnderBaseChange`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`, `asFiber`, `fiberι_asFiber`.
  Its imported `ResidueField` module defines `Scheme.fromSpecResidueField`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`.
- Proof-only import `Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange`:
  `AlgebraicGeometry.pointwise_flatness_base_change`.
- Proof-only import `Sheaf.AlgebraicGeometry.FibrewiseFlatnessCriterion`:
  `AlgebraicGeometry.Scheme.Hom.flatAt_and_base_flatAt_of_fiber_flatAt`.

All six statement dependencies have usable records. No dependency repair or
additional DAG node is needed. The theorem docstring supplies all five proof
steps and the relevant proof-dependency IDs.

Edge cases checked: when X is empty the pointwise clauses are vacuous and the
three base-change properties still hold. When T is empty the last pointwise
clause is vacuous; empty schemes are not excluded. Identity base change gives
the same criterion through the canonical pullback isomorphism; no literal
identification of that pullback with X is assumed. Nonflat or non-finite-type
h is permitted because only the base-changed p and q have class conclusions.
There are no restrictions on residue characteristic or reducedness. The
unique fibre point uses the existing homeomorphism, with no arbitrary choice
of point and no extra point-lifting hypothesis.

Searches performed using the prescribed `msearch.py N5 lem-sfb-relative-flat-fibre-test`:

- LeanFinder: "For X flat locally of finite presentation over S and Y locally
  of finite type over S, flatness of X to Y at x is equivalent to flatness on
  the fibre, also after arbitrary base change". Eight results: global Flat,
  Flat.isStableUnderBaseChange, Flat.iff_flat_stalkMap, Flat.stalkMap,
  Flat.of_stalkMap and related ring-map locality results. None states the node.
- Loogle: `"Flat", "fiber"`. Zero results.
- Mathlib grep: `flat.*fiber|fiber.*flat|flat.*fibre|fibre.*flat`, subdirectory
  AlgebraicGeometry. Three hits in Morphisms/SmoothFiber.lean, about deducing
  smoothness from flatness and smooth fibres; no matching statement.
- LeanSearch: "Flatness of a morphism between schemes over a base can be tested
  on the fibre if the source is flat locally of finite presentation and the
  target is locally of finite type". Eight results, including RingHom.Flat,
  Flat, Flat.of_stalkMap, finite-presentation implies finite-type, and locality;
  none is the pointwise fibre equivalence or its arbitrary-base-change clause.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` for fibre/flat
  phrases, then the narrower `relative_flat_fibre_test`,
  `flatAt_and_base_flatAt_of_fiber_flatAt`, and flat/iff/fibre patterns, and a
  check of `dag/lean_names_upstream.json`. No existing public declaration says
  this node. The existing FibrewiseFlatnessCriterion is the converse input.
  RelativeFlatLocusBaseChange.lean has a private local theorem for the first
  equivalence, under a private map abbreviation; it is not an accessible public
  declaration and does not state the additional base-change-property clauses.
- `grep -rn 'lem-sfb-relative-flat-fibre-test' lean/WeilConjectures`: no hits.
  Searched existing canonical-map names as well; the statement uses Mathlib's
  `pullback.map` directly, with no new definition of a fibre or pullback map.

No statement dispute or source correction. The shared repository is read-only;
all delivery files are under the assigned sandbox. The corrected point coercion
`↥(pullback p h)` avoids elaborating a categorical pullback in Type. The server
wrapper compiled both its sandbox module and the final module cleanly, with
only the permitted theorem `sorry`.

## Second reading by N5

Author's second pass, for the maintainer's independent review: reopened the
node and the compiled file and checked each hypothesis and clause above. The
triangle has the correct composition order, both fibre maps use the identity
on the correct residue-field spectrum, and both fibre points are Mathlib's
canonical `asFiber`. The second conjunct includes all three required property
conclusions before quantifying every base-changed point. Neither equivalence
asserts that flatness descends along h; the fibre test is separately over S and
T, so arbitrary h is retained. The statement has no `let` binders, local
notation, private helper or automatic implicit variables. The only repair in
the compile cycle was making the base-changed point's type coercion explicit;
no mathematical statement changed. No missing or additional hypothesis or
conclusion was found.
