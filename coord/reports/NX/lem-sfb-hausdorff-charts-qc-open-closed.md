## Worker report

Item: `lem-sfb-hausdorff-charts-qc-open-closed`. The new module
`Sheaf.AlgebraicGeometry.HausdorffChartsQuasiCompactOpenClosed` states
`AlgebraicGeometry.isClosed_and_isClosedImmersion_of_hausdorff_affine_cover`.
Its whole proof is `sorry`; no definition or proof was added. The node changes only
in `lean`. No new nodes, dependency repairs, or statement correction are needed.

The source was read in Stacks `properties.tex`, Tag 0CKV,
`lemma-dimension-zero`, especially the (1) implies (2) paragraph. The node applies
that paragraph's compact-in-Hausdorff argument to a quasi-compact open and each
chart. Stacks' original dimension-zero hypothesis supplies Hausdorff charts there;
this item explicitly assumes Hausdorff charts instead, exactly as its accepted
statement says. The theorem docstring carries all four proof steps, including
the complement calculation and lifting sections by gluing with zero.

Hypothesis and clause correspondence:

- A scheme `X` is `(X : Scheme.{u})`.
- Quasi-separatedness is `[QuasiSeparated (terminal.from X)]`, the recorded
  morphism predicate on the terminal map. The equivalence with the topological
  scheme condition is `quasiSeparatedSpace_iff_quasiSeparated X`.
- The arbitrary set `J` is `(J : Type v)`, with an explicit universe independent
  of `u`. This is a family of opens, not a limit indexed in an unsuitable universe.
- The open charts are `(V : J → X.Opens)`. Their affine condition is
  `hVaffine : ∀ j : J, IsAffineOpen (V j)`; Mathlib defines `IsAffineOpen` by
  affineness of the actual restricted open subscheme.
- Hausdorffness is `hVhausdorff : ∀ j : J, T2Space (V j).toScheme`.
  The read definition of `T2Space` says precisely that two distinct points have
  disjoint open neighborhoods. This uses each chart's original subspace topology.
- The cover condition is `hVcover : iSup V = ⊤`, meaning the union of the opens
  is all of `X`. It imposes neither finiteness nor nonemptiness on `J`.
- Every open subscheme is quantified by `(U : X.Opens)`, with its original
  structure given by Mathlib's `Scheme.Opens.toScheme`.
- Quasi-compactness of this subscheme is `[CompactSpace U.toScheme]`, precisely
  the dependency's recorded `CompactSpace` notion; it includes no separation
  condition and does not assert compactness of `X`.
- Closedness of its underlying subset is `IsClosed (U : Set X)`.
- The closed immersion is `IsClosedImmersion U.ι`, joined with closedness by `∧`.
  This is the original canonical open inclusion, with domain `U.toScheme`.
  Mathlib's read definitions in `AlgebraicGeometry/Restrict.lean` construct that
  scheme by restricting `X` and set `U.ι := X.ofRestrict _`. Consequently this
  is exactly the given open structure and restricted sheaf, not an existentially
  chosen closed subscheme or a second structure on the same point set.
- There is no `Nonempty`, finite-cover, `CompactSpace X`, Noetherian, or
  dimension hypothesis. No case of the item is excluded.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Scheme.Opens` (statement dependency `def-pc-scheme`).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated` and
  `quasiSeparatedSpace_iff_quasiSeparated` (statement dependency
  `def-weil-quasi-separated-morphism`).
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (statement dependency
  `def-weil-pbc-quasi-compact-scheme`). Its definition explicitly has no
  separation condition.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (statement dependency
  `def-weil-closed-immersion`). It requires a closed embedding and surjective
  stalk maps for the very same morphism `U.ι`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen` (statement charts)
  and `Scheme.compactSpace_of_isAffine` (proof dependency
  `lem-weil-pbc-affine-scheme-qcqs`); the other clause of that dependency,
  `quasiSeparatedSpace_of_isAffine`, is in the imported quasi-separated module.
- `Mathlib.Topology.Separation.Hausdorff`: `T2Space` (statement charts) and
  `IsCompact.isClosed` (proof dependency `lem-sfb-compact-subset-hausdorff-closed`).
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`:
  `AlgebraicGeometry.compactSpace_inter_of_quasiSeparated` (proof dependency
  `pqf-lem-qs-intersection-qc`). Its full signature and docstring were read.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` (proof dependency
  `def-weil-open-immersion`). The same closed-immersion module supplies the
  remaining proof dependency `def-weil-closed-immersion`.

Statement dependencies are public imports. The intersection lemma and the
proof-only open-immersion module are plain imports. The other proof dependencies
already occur among public imports because their definitions occur in the
statement. No proof dependency is missing or cyclic.

Edge cases checked before writing:

- `U = ⊥`: the empty restricted scheme is compact, its image is closed, and
  its original empty open inclusion is a closed immersion. The gluing argument
  uses just zero on the complement.
- Empty `X`: all opens are empty. `J` may be empty, and `iSup V = ⊤` remains the
  correct cover condition. There is no implicit inhabited-index assumption.
- Nonempty `X` with empty `J`: the cover hypothesis fails, as it should.
- Infinite covers and non-quasi-compact schemes are retained. For example an
  infinite disjoint union of spectra of fields has Hausdorff affine charts and
  is quasi-separated; its quasi-compact opens have finite support and are closed.
- A Hausdorff chart need not be finite or discrete: spectra of infinite products
  of fields illustrate that the statement does not replace Hausdorffness by
  discreteness or add a Noetherian hypothesis.
- The hypotheses cannot simply be discarded: a quasi-compact basic open in the
  affine line need not be closed when Hausdorffness is absent. Quasi-separatedness
  is exactly what the node's argument uses to make chart intersections compact.

Searches for an existing statement (before writing):

1. `msearch.py` LeanFinder: "In a quasi separated scheme covered by Hausdorff
   affine open subsets every quasi compact open inclusion is a closed immersion".
   Eight hits: quasi-separated affine-cover/intersection criteria and unrelated
   ideal-sheaf quasi-compactness; none gives this theorem.
2. `msearch.py` Loogle:
   `AlgebraicGeometry.IsClosedImmersion, QuasiSeparatedSpace`.
   Successful query, zero hits.
3. `msearch.py` Mathlib grep, `AlgebraicGeometry`:
   `Hausdorff|T2Space|isClosed.*[Oo]pen`. Eleven hits, including the existing
   closed-image immersion criterion and unrelated closed/open complements.
   None combines Hausdorff affine charts with quasi-compact open closedness.
4. `rg` of the upstream `WeilConjectures` tree for `Hausdorff|hausdorff|T2Space`
   and exact-name searches: no matching statement. The prescribed node-id grep
   in that tree also has no hit.
5. `rg` of `lean/Sheaf` for Hausdorff/chart and closed-immersion patterns:
   no matching theorem. `QcqsZeroDimensionalAffine.lean` is a distinct consumer
   theorem with compactness and closed-point hypotheses and an affine conclusion.
6. Exact proposed-name search in Mathlib algebraic geometry, the upstream and
   Sheaf trees, and `dag/lean_names_upstream.json`: no collision.

The example module `Sheaf.CategoryTheory.CompactObject` is now withdrawn; its
node records `WeilConjectures.CategoryTheory.CompactObject`. That actual module
was read for current header, public-section, namespace, and source conventions.

Validation: the prescribed `scompile.py` compiled this module in sandbox mode
and at its actual library module name with no errors or warnings. All variables
and universes are explicitly bound. No statement dispute was found.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
