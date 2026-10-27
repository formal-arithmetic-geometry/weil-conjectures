## Worker report

The new module `Sheaf.AlgebraicGeometry.PointlikeQuasiseparatedSpaceField` states
`AlgebraicGeometry.AlgebraicSpace.pointlike_quasiseparated_space_field` with one
`sorry`, and no new definitions or other postponed theorems. The docstring carries
all six steps of the node's proof, with their dependency ids. The source read is
Stacks, `literature/stacks-project/spaces-properties.tex`,
`lemma-point-like-spaces` (Tag 03DZ), including its displayed invariant subfield.
The statement of the node is unchanged. No statement dispute or dependency fault
was found.

Hypothesis and conclusion correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; the algebraic space over that
  scheme is `Y : AlgebraicSpace S`.
- The field is `(L : Type u) [Field L]`. Its specified S-structure is
  `a : Spec (CommRingCat.of L) ⟶ S`. The S-map from its spectrum to Y is
  `q : yoneda.obj (Over.mk a) ⟶ Y.obj.obj`.
- Representable étaleness is `hq : IsEtale q`, the recorded scheme-test definition
  `IsRepresentableWith (fun _ _ p ↦ Etale p.left) q`. In particular this supplies
  representability; a redundant separate representability assumption is unnecessary.
  Scheme-test surjectivity is `hsur : IsSurjective q`, using the recorded
  `IsRepresentableWith (fun _ _ p ↦ Surjective p.left) q`.
- Absolute quasi-separatedness is `hY : IsAbsolutelyQuasiSeparated Y`. This is the
  existing affine-test definition: for affine S-schemes U,V with maps to Y,
  `CompactSpace (Point (Limits.pullback a b))`. Its source Tag 0AHR identifies
  this with quasi-compactness of the absolute diagonal, also for an arbitrary base.
  Its already landed definition node `def-sfb-space-absolute-quasi-separated`
  was added to `stmt_deps` as authorized by brief-stage2 §5. It was already a
  proof dependency. No statement or proof text was changed.
- The subfield is `∃ k : Subfield L`, with its actual subtype inclusion `k.subtype`.
  Its S-structure is `∃ b : Spec (CommRingCat.of k) ⟶ S`.
- The equation `h : Spec.map (CommRingCat.ofHom k.subtype) ≫ b = a` makes the
  canonical inclusion-induced spectrum map a morphism over the original S.
- `e : Y.obj.obj ≅ yoneda.obj (Over.mk b)` is the isomorphism Y ≅ Spec k over S:
  this is an isomorphism of their functors of S-points. Both presheaves are fppf
  sheaves, and the sheaf category and algebraic-space category are full, so this
  states precisely the algebraic-space isomorphism without introducing a second
  scheme-to-space construction or additional sheaf-condition assumptions.
- `q ≫ e.hom = yoneda.map (Over.homMk (Spec.map (CommRingCat.ofHom k.subtype)) h)`
  identifies the original specified atlas with the spectrum map of the inclusion.
- `FiniteDimensional k L` means finite vector-space dimension (Mathlib's alias
  for `Module.Finite k L`). `Algebra.IsSeparable k L` says exactly that every
  element's minimal polynomial is separable. The canonical algebra structure
  is the inclusion action: `Subfield.toAlgebra` and `algebraMap_ofSubfield`.
- No finite-type, separation, characteristic, or Noetherian hypothesis is imposed
  on S. There are no `let` binders, implicit unbound variables, arbitrary auxiliary
  maps replacing the inclusion, or file-local instances/notations.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and its morphisms.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, and namespace definitions
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`. Their full signatures and
  docstrings were read; representability is included in both latter predicates.
- `def-weil-field`: Mathlib `Field`, from `Mathlib.Algebra.Field.Defs`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`, used through scheme-test étaleness.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`,
  `CompactSpace`, used inside absolute quasi-separatedness without a Hausdorff
  condition.
- `def-sfb-space-absolute-quasi-separated`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`,
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.

Statement dependencies are publicly available through the public imports;
proof dependencies have ordinary imports, as required:
`Sheaf.AlgebraicGeometry.EtaleAtlasPresentation`
(`AlgebraicGeometry.AlgebraicSpace.etale_atlas_presentation`),
`WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
(`AlgebraicGeometry.Scheme.Hom.etale_fibre_discrete_separable_points`),
`Mathlib.AlgebraicGeometry.Limits` (`AlgebraicGeometry.sigmaSpec`,
`AlgebraicGeometry.ι_sigmaSpec`, and the finite-index isomorphism instance),
`Mathlib.AlgebraicGeometry.Morphisms.Finite` (`AlgebraicGeometry.IsFinite`),
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
(`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`), and
`Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient`
(`AlgebraicGeometry.finiteFlat_affineRelation_quotient`). Étaleness and the
absolute-quasi-separatedness proof input are already publicly imported.

Edge cases checked before writing: Field excludes the zero ring, so Spec L is
nonempty. The empty space cannot admit the asserted surjective field atlas; the
empty base admits no such a. Identity atlases are included, with k = L; no
proper-subfield requirement or degree lower bound was introduced. Finite separable
extensions in every characteristic are included; purely inseparable nontrivial
extensions do not give étale field atlases. The arbitrary base may be
non-quasi-separated and of non-finite type: the hypothesis is absolute, with no
relative replacement. There is one explicit site/scheme/field universe u, the
existing algebraic-space API's size convention, and no smaller independent
universe of test schemes that could make the tests vacuous.

Searches for an existing statement:

- `msearch.py leanfinder`, query “A quasi separated algebraic space with a
  surjective etale atlas Spec L is Spec k for a subfield k with L finite separable
  over k”: 8 hits, concerning field spectra, affine terminal schemes, étale
  algebras, or integral schemes; none is this algebraic-space representability
  theorem.
- `msearch.py leansearch`, query “An algebraic space with a surjective etale
  field spectrum atlas and quasi compact absolute diagonal is the spectrum of a
  subfield”: 8 hits, affine schemes and quasi-separated schemes, no match.
- `msearch.py loogle`, query `"AlgebraicSpace", "IsEtale"`: 0 hits.
- `msearch.py grep`, query `AlgebraicSpace|point.?[Ll]ike`, subdirectory
  `AlgebraicGeometry`: 0 Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `pointlike|pointLike|point_like|lem-sfb-pointlike-quasiseparated-space-field`:
  no existing statement. Broader searches for quasi-separated/field combinations
  returned unrelated results about schemes. `grep -rn` for the item id in
  `lean/WeilConjectures` and `rg` in `dag/lean_names_upstream.json` gave no match.
- Mathlib source searches located and verified `Subfield.toAlgebra`,
  `Subfield.algebraMap_ofSubfield`, `FiniteDimensional`, `IsSeparable`, and
  `Algebra.IsSeparable`; their existing notions are used directly.

Validation: `scompile.py NF lem-sfb-pointlike-quasiseparated-space-field` compiled
this file both as sandbox and library module on the server (10.3 s and 8.5 s),
with no errors or unexpected warnings. All compilation uses the authorized
wrapper and the published live build; no live source was changed.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
