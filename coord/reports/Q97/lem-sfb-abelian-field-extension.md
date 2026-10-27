## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.FieldExtension` states
`AlgebraicGeometry.IsAbelianVariety.fieldExtension`, with its whole proof `sorry`.
It states both clauses of lem-sfb-abelian-field-extension and defines no new notion.
Only the item's `lean` field changes; there are no new nodes, dependency repairs,
or statement corrections.

Source read: `literature/stacks-project/groupoids.tex`, Tag 0BFB,
`lemma-abelian-variety-change-field` (lines 1620 onward), and
`literature/stacks-project/morphisms.tex`, Tag 02FY,
`lemma-dimension-fibre-after-base-change`, part (1) (lines 5425 onward).
The node uses the project's proper/smooth/connected group-scheme convention;
its rational identity section supplies geometric connectedness. The source's
geometrically integral convention is equivalent in this setting, as explained
in the upstream abelian-variety definition and characterization modules.

Hypothesis and clause correspondence:

- A field k: `{k : Type u} [Field k]`.
- A field extension K/k: `{K : Type u} [Field K] [Algebra k K]`.
  The specified map is `algebraMap k K`, and the induced scheme map is
  `Spec.map (CommRingCat.ofHom (algebraMap k K))`.
- A group scheme A over k: `(A : Over (Spec (.of k))) [GrpObj A]`.
- A is an abelian variety: `[IsAbelianVariety A]`, exactly the recorded
  proper, smooth, connected predicate, with group structure supplied separately.
- A_K with base-changed group operations: the bundled group object
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj
  (Grp.mk A)`. Its `.X` is definitionally the over-object
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A`;
  its underlying scheme is the pullback of `A.hom` along the field-extension map
  and its structure map is `pullback.snd`. `Functor.mapGrp` supplies actual
  group data, not a choice from an existence theorem: multiplication and unit
  are mapped using the canonical product and terminal comparisons, and inverse
  is the image of the original inverse (`Functor.grpObjObj`). This directly
  implements the node's instruction to give the base change these operations.
- A_K is abelian over K: the first conjunct `IsAbelianVariety (... .X)`.
  The parameter of that predicate is an object of `Over (Spec (.of K))`.
- Equality of dimensions: the second conjunct `(... .X).left.dim = A.left.dim`.
  Both use the recorded `Scheme.dim`, namely the supremum of Krull dimensions
  of stalk rings in `WithBot ℕ∞`, rather than silently substituting the natural
  number `IsAbelianVariety.dim` or topological dimension.

Dependencies read and used:

- def-weil-field: `Field`, `Mathlib.Algebra.Field.Defs`.
- def-pc-field-extension: `Algebra` and `algebraMap`,
  `Mathlib.Algebra.Algebra.Defs`.
- def-sc-abelian-variety: `AlgebraicGeometry.IsAbelianVariety`,
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`.
- def-pc-base-change: the recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` documents
  `Over.pullback`; its object is the scheme pullback with second projection.
  The record's primary `Scheme.Modules.moduleBaseChange` concerns module
  sheaves, not scheme base change, and is not substituted for the scheme object.
- def-sc-group-scheme: `CategoryTheory.GrpObj` and `CategoryTheory.Grp`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; group base change uses `Functor.mapGrp`
  there and the monoidal pullback from
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`.
- def-pc-dimension: `AlgebraicGeometry.Scheme.dim`,
  `WeilConjectures.AlgebraicGeometry.Dimension`.

All stated proof dependencies have direct imports, either public for notions
used by the statement or plain for the proof plan:
`AlgebraicGeometry.IsProper.isStableUnderBaseChange` (Mathlib proper morphisms),
`AlgebraicGeometry.smooth_isStableUnderBaseChange` (Mathlib smooth morphisms),
`AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_section`
(`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`),
`AlgebraicGeometry.exists_field_baseChange_affine_covers`
(`WeilConjectures.AlgebraicGeometry.FieldBaseChangeAffineCovers`),
`AlgebraicGeometry.dim_base_change`
(`WeilConjectures.AlgebraicGeometry.DimensionBaseChange`), and
`AlgebraicGeometry.Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover`
(`WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover`).
Properness itself is `AlgebraicGeometry.IsProper` in the imported proper module.
The theorem docstring contains all five node proof steps, including the
functor-of-points group-law verification, proper/smooth preservation,
connectedness from the identity section, matching affine covers, and the
supremum calculation of dimension.

Edge cases checked: K=k (including a nontrivial specified embedding), the
zero-dimensional abelian variety Spec k, arbitrary characteristic, inseparable
algebraic extensions, and transcendental extensions are all included. No finite,
separable, algebraic, perfect, algebraically closed, or positive-dimensional
hypothesis occurs. The empty scheme is excluded by the original hypotheses,
not by an added assumption: connectedness includes nonemptiness and the group
identity gives a rational point. Empty charts are permitted in the affine-cover
proof and contribute bottom to both dimension suprema. A common arbitrary
universe u is the standard scheme/Spec convention of all recorded geometric
dependencies; it places no mathematical bound on the extension: any specified
fields and scheme fit a sufficiently large common universe.

Searches actually run with msearch.py, group Q97 and this item:

- LeanFinder: "The base change of an abelian variety along a field extension is
  an abelian variety with unchanged dimension". Eight Weierstrass-curve and
  point-base-change hits, no theorem about general abelian varieties.
- Loogle: "IsAbelianVariety, GrpObj, Over.pullback". Zero hits, with the
  diagnostic "unknown identifier 'IsAbelianVariety'"; that project predicate
  is absent from the Mathlib search index, so this search alone cannot exclude
  an upstream match.
- Mathlib grep: `IsAbelianVariety|abelian variety`, subdirectory
  AlgebraicGeometry. Zero hits.
- LeanSearch: "An abelian variety stays an abelian variety of the same dimension
  after any field extension". Eight hits on Galois/invariant rings,
  characteristic, and individual scheme base-change properties; no match.
- Source rg: `IsAbelianVariety.*[Bb]ase|[Bb]ase.*IsAbelianVariety|dim.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*dim`
  in `lean/WeilConjectures`; and grep of the item id in that source tree.
  Read the resulting `AbelianVariety.Basic`, `DimensionBaseChange`, and
  `BaseChangeDimensionExtension` modules. `IsAbelianVariety.pullback` states
  only preservation of abelian varieties; it has no dimension clause.
  `dim_base_change` gives affine ring dimension and a curve clause;
  `baseChange_dim` assumes algebraically closed fields and a curve.
  None states the full node, so an existing-only record would omit a clause.
- Project rg: abelian/base-change and dimension/base-change patterns in
  `lean/Sheaf/AlgebraicGeometry`, followed by `IsAbelianVariety.*pullback|pullback.*IsAbelianVariety|field[Ee]xtension|field_extension`
  in its abelian-variety modules. No full node statement found.
- Declaration-name collision search for `IsAbelianVariety.fieldExtension` and
  `theorem.*fieldExtension` in Mathlib, WeilConjectures and Sheaf: no collision.

No disputed statement or node fault was found. Server compilation and delivery
preflight results are recorded below after validation.

Validation: `scompile.py Q97 lem-sfb-abelian-field-extension` compiled the module
successfully in both sandbox and library modes. After adding explicit imports
for the recorded Mathlib field, algebra and group-object notions,
`deliver2.py Q97 lem-sfb-abelian-field-extension --no-push` recompiled the module
and printed `OK (dry run): commit d0761e472d9 passes the preflight and compiles;
nothing pushed`. The Lean signature in the node was checked byte-for-byte
against the file, and every Lean source line is at most 100 characters.

## Second reading by Q97

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
