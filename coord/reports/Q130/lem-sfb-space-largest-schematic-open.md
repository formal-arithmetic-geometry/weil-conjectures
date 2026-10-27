## Worker report

Delivered statement: `AlgebraicGeometry.AlgebraicSpace.exists_largest_schematic_open`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceLargestSchematicOpen`. There is one theorem,
with proof `sorry`, and no new definitions. The node is changed only in `lean`.

Source read in full: `literature/stacks-project/spaces-properties.tex`,
lemma-subscheme, Tag 03JH, lines 1564–1593, including the preceding explanation that
the largest open can be empty (the example A¹_Q/Z). Its proof constructs the open
union and applies the Zariski representability criterion. The declaration docstring
reproduces the six steps of the node's accepted proof, with their dependency IDs.

Hypothesis and clause correspondence:

- “Let S be a scheme”: `{S : Scheme.{u}}`, with the universe explicitly declared.
- “X an algebraic space over S”: `(X : AlgebraicSpace S)`, the recorded full
  subcategory of fppf sheaves with representable diagonal and an étale surjective atlas.
- “There is an open subspace X_sch ⊆ X”: `∃ J : OpenSubspace X`. This is the recorded
  subtype of subfunctors whose inclusions are representable by open immersions on
  every scheme test; it is not an arbitrary subset or arbitrary morphism.
- “represented by an S-scheme”: `J.val.toFunctor.IsRepresentable`. The underlying
  presheaf is on `(Over S)ᵒᵖ`, so its representing object is an actual `Over S`,
  rather than just a scheme without an S-structure. Mathlib's `Functor.IsRepresentable`
  asserts existence of that object and a natural Hom equivalence.
- “contains every open subspace ... represented by an S-scheme”:
  `∀ A : OpenSubspace X, A.val.toFunctor.IsRepresentable → A ≤ J`.
  The derived partial order is exactly subfunctor inclusion, as the dependency states.
- “Its point set is the union of the point sets of all such open subspaces”:
  `pointImage J.val.ι = ⋃ (A : OpenSubspace X)
  (_ : A.val.toFunctor.IsRepresentable), pointImage A.val.ι`.
  Both sides are subsets of the same recorded field-valued point-class set of X;
  `pointImage` uses field-valued representatives. The second index restricts the
  union to precisely the representable opens, without choosing representations.
- “No separation or quasi-compactness hypothesis ... this open may be empty”:
  there are no other hypotheses, and no `Nonempty`, density or compactness conclusion.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (local affine
  locally ringed spaces), with its category and morphisms; node `def-pc-scheme`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, and its scheme-test `IsRepresentableWith`; node
  `def-trf-algebraic-space`. The signature of the latter tests all `Over S` schemes
  and requires an actual scheme pullback square.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`,
  `PointRepresentative.map`, `pointTopologicalSpace`; node `def-a1-space-point-topology`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` and its
  inherited partial order; node `def-a1-space-open-subspace`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  the predicate used by `OpenSubspace`; node `def-weil-open-immersion`.
- `Mathlib.CategoryTheory.Yoneda`: `Functor.IsRepresentable`, read at lines 515–521.
  This is the same existing representability notion used in `lem-pc-schemes-criterion`.

Proof dependencies were also read and imported as plain imports where they are not
already public statement dependencies:

- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage`:
  `openSubspace_points_orderIso` and `etale_open_image`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests`:
  `openSubspace_preimage_schemeTests`, `openSubspace_factor_schemeTests`,
  `openSubspace_pullback_image`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`: `point_open_calculus`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`:
  `AlgebraicGeometry.ZariskiCovers` and
  `AlgebraicGeometry.isRepresentable_of_isSheaf_of_zariskiCovers`.
- `Mathlib.CategoryTheory.Sites.SheafOfTypes`: `CategoryTheory.Presieve.IsSheaf`
  (the Mathlib match for `def-pc-zariski-sheaf-property`).
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, retaining Mathlib's sheaf equalizer
  definitions as described in the recorded `def-weil-pbc-sites-and-cohomology` note.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`:
  `Scheme.zariskiPrecoverage_le_fppfPrecoverage` (the Mathlib match for
  `lem-pc-zariski-coverings-are-fppf`).

Edge cases checked before writing: if X is represented by a scheme, the full
subfunctor is an eligible open, so largestness forces J to be full. If X is empty,
the empty scheme represents J and the displayed union is empty. An algebraic space
with no nonempty schematic open, such as the source's A¹_Q/Z, is allowed: the
statement neither asserts density nor selects a nonempty open. An arbitrary base S,
including the empty base, is permitted. Nothing assumes quasi-separatedness,
separatedness, quasi-compactness, or finite type. The only universe is the existing
algebraic-space interface's scheme universe u; no independent small test universe
or extra equality between universes was introduced. The set-indexed union can range
over the full type of open subfunctors without an artificial finite/small index bound.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder "An algebraic space has a largest open subspace
  represented by a scheme"`: 8 results, all scheme or locally ringed space results,
  including `LocallyRingedSpace.IsOpenImmersion.scheme`, `isAffineOpen_top`,
  `Scheme.Opens`; none states this algebraic-space result.
- `msearch.py ... leansearch "Every algebraic space has a largest open subscheme"`:
  8 scheme-only hits, such as `iSup_affineOpens_eq_top` and `isAffineOpen_top`;
  no match.
- `msearch.py ... loogle '"AlgebraicSpace"'`: zero hits.
- `msearch.py ... grep 'schematicLocus|largest.*open.*scheme|AlgebraicSpace'`:
  zero Mathlib hits.
- `rg -n 'schematicLocus|largest.*[Ss]chem|schematic.*[Oo]pen|
  lem-sfb-space-largest-schematic-open' lean/WeilConjectures lean/Sheaf`:
  no declaration of this result. Project hits include the proof docstring of
  `AlgebraicSpaceDenseSchemeOpen`, which cites this node but only states existence
  of a dense scheme open under a quasi-compact diagonal hypothesis, and unrelated
  schematic-density/closure lemmas. The exact node ID has no upstream declaration.
- Read the existing open-subspace, point-image and representability declarations
  in their full signatures and docstrings; reused them without a private copy.

No statement correction, new node, dependency-interface repair or disputed statement
is needed. The prescribed `scompile.py` compiled the file both as the sandbox probe
and under its final library module name (1.9 s and 1.6 s), with no errors or
unexpected warnings.

## Second reading by Q130

Author's separate clause-by-clause rereading, with the DAG node and final Lean file
open; independent review is left to the maintainer as specified in the dispatcher's
brief (no other worker was started). Checked that the existential binds an actual
`OpenSubspace X`, not an open of an unrelated scheme; the representability is on
`Over S`; largestness quantifies over every represented open; and the union is in
the point set of X using the actual inclusions `A.val.ι`. The two union indices
include each represented open and exclude unrepresented ones. The order is the
recorded subfunctor order. The signature has no separation, finiteness, nonempty or
density hypothesis. No mismatch found and no statement change made. The single
postponed theorem has the node's source and complete six-step proof in its docstring.
