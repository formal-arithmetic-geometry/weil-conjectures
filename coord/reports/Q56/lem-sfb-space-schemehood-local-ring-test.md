## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSchemehoodLocalRingTest` states
`AlgebraicGeometry.AlgebraicSpace.isScheme_of_local_ring_tests`, with its only proof
postponed by `sorry`. No definition or auxiliary theorem is introduced. I read the node
and all six statement dependency records, their signatures/docstrings, and the local
Stacks source `literature/stacks-project/spaces-limits.tex`, lemma-enough-local,
Tag 0B80 (lines 3872–3891). The node matches that source. No statement correction
or dispute is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the S-scheme is `(T : Over S)`.
- The algebraic space is `(X : AlgebraicSpace S)`, using the full subcategory of big
  fppf sheaves with representable diagonal and a representable surjective etale atlas.
- The map to the representable sheaf is `(g : X.obj.obj ⟶ yoneda.obj T)`.
  Natural transformations between the underlying presheaves are the morphisms of
  the full subcategory of sheaves. Representable presheaves are fppf sheaves.
- The size convention is explicit `universe u`, `Scheme.{u}`, the existing algebraic
  space presheaves with values in `Type u`, and the already defined point classes in
  `Type (u+1)`. All scheme tests and local spectra use the same scheme universe.
- `hqc : MapIsQuasiCompact g` unfolds to every affine S-scheme mapping into the target
  having a pullback with `CompactSpace` point space. This uses the existing final atlas
  topology `pointTopologicalSpace`, exactly the node's point-space convention.
- `hqs : MapIsQuasiCompact (pullback.diagonal g)` applies the same affine-test condition
  to the actual relative diagonal into the presheaf pullback `X ×_{h_T} X`.
- `hlocal` quantifies over every `x : Point X.obj.obj` and `t : T.left` satisfying
  `mapPoint g x = schemePointMap (𝟙 (yoneda.obj T)) t`. The right side is the canonical
  residue-field point class of t in h_T. Scheme points biject with the field-valued
  point classes of their representable presheaves, so this is exactly t=g(x), with
  neither a restriction to closed points nor a test at points outside the image.
- The map in the local pullback is the Yoneda image of
  `Over.homMk (U := Over.mk (T.left.fromSpecStalk t ≫ T.hom))
    (V := T) (T.left.fromSpecStalk t) rfl`.
  Its source is Spec of `T.left.presheaf.stalk t`, with the composite structure map
  to S, and its underlying scheme map is the canonical `Scheme.fromSpecStalk`.
  No arbitrary map to T is substituted. The `rfl` supplies only its triangle equality.
- Local representability is `∃ U : Over S, Nonempty (Limits.pullback g ... ≅ yoneda.obj U)`.
  Taking the fibre product in presheaves gives the underlying presheaf of the sheaf
  fibre product, because the inclusion of sheaves preserves limits. Thus this says
  exactly that this algebraic space is represented by an S-scheme.
- The conclusion `∃ U : Over S, Nonempty (X.obj.obj ≅ yoneda.obj U)` says exactly
  that X is represented by an S-scheme, with no affine or finiteness restriction on U.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace` and its fppf sheaf/atlas
  interface, exposed through the imported dependency modules.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  using `Point` and `schemePointMap` from `AlgebraicSpacePointClasses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` supplies closure under the sheaf pullbacks used here.
- `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.fromSpecStalk`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `mapPoint` and `MapIsQuasiCompact`.
  Its already landed owner `def-sfb-proper-curve-moduli` is added to stmt_deps under
  the standing authorization to cite already landed definitions. Its curve-family
  predicates are not assumptions of the theorem.
- `CategoryTheory.Limits.pullback.diagonal` is the canonical relative diagonal.

Proof-only imports are the currently stated dependencies
`Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage`,
`WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests`, and Mathlib's
`Morphisms.QuasiSeparated` (the affine-scheme qcqs Mathlib match). The remaining
proof-only nodes have no recorded declaration yet and are described in the proof
docstring without inventing another statement. The docstring carries all five
steps of the node's proof, including the atlas/point-compactness comparison and
natural sheaf-limit comparison.

Edge cases checked before writing: empty X makes the local hypothesis vacuous and
X is represented by the empty S-scheme; T empty forces X empty. Non-surjective g
requires tests only at its point images. The theorem includes nonclosed and generic
points, local rings of any characteristic, and base schemes not assumed noetherian,
quasi-compact or quasi-separated. The representing local schemes need not be affine.
The field-valued point equality uses no arbitrary choice of representatives.

Searches for an existing statement and existing notions:

- `msearch.py ... leanfinder` query: "A quasi compact quasi separated algebraic space
  over a scheme is a scheme if its pullbacks to local rings at images of all points
  are schemes". Eight results, all scheme quasi-compactness/quasi-separatedness facts;
  no algebraic-space schemehood theorem.
- `msearch.py ... loogle "AlgebraicSpace, IsScheme"`: zero hits; Loogle reported
  unknown identifier AlgebraicSpace (the project notion is not in Mathlib).
- `msearch.py ... grep "scheme.*local.*ring|local.*ring.*scheme|enough_local"
  AlgebraicGeometry`: 25 hits, concerning schemes, locally ringed spaces, spectra
  or local rings; none states this schemehood test for algebraic spaces.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` with
  `lem-sfb-space-schemehood-local-ring-test|scheme.*local.*ring|enough_local|schemehood|IsQuasiCompactPresheafMap|def MapIsQuasiCompact`:
  no copy of this theorem; found the landed compactness and point-map definitions.
  Read their full declarations and owner node before using them.
- Read the declared scheme, spectrum, space, point topology and fibre product APIs.
  The prescribed example CompactObject module is now withdrawn and contains no
  declarations, so the module header follows the live algebraic-space examples.

Validation: scompile.py compiled both its isolated sandbox view and the actual module
with no errors or warnings. An initial compiler error from incorrect parameter names
on Over.homMk was fixed to its actual `U` and `V` binders; the canonical source and target
are both explicit. No local compilation or global build was run.

## Second reading by Q56

I reread the final node and module after compilation as a self-check; this is not a
claim of an independent agent review. The dispatcher forbids starting other agents,
and the maintainer supplies the independent delivery review. The rereading checked
that hqc is the existing point-compactness condition, hqs concerns the relative
rather than absolute diagonal, the point equality is t=g(x), the Over source of the
local-ring map has the composite structure map to S, and both local and final
representability quantify over all S-schemes. The universal quantifier over t has
an implication restricting it to g(x); it does not require tests over all of T.
No mathematical mismatch was found and the statement text was unchanged.
