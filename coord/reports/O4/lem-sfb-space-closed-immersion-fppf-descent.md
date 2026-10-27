## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedImmersionFppfDescent` states
`AlgebraicGeometry.AlgebraicSpace.closedImmersion_iff_fppf_pullback`, with proof `sorry`.
It defines no new notion. Source read: `literature/stacks-project/spaces-descent.tex`,
lemma-descending-property-closed-immersion, Tag 0420, lines 1600–1628. The source proves
fpqc locality by first descending affineness and then using scheme closed-immersion
descent. The node specializes this to fppf families using finite affine refinement.
The docstring includes every step of the accepted node proof.

Clause-by-clause correspondence:

- Base scheme S: `{S : Scheme.{u}}`.
- Algebraic spaces X and Y over S: `{X Y : AlgebraicSpace S}`; this is the existing
  full subcategory of big-fppf sheaves with representable diagonal and an etale
  surjective scheme atlas. Their morphism is `(f : X ⟶ Y)`.
- Size convention: explicit `universe u w`; schemes, field extensions and presheaf
  values use the framework's u, and the covering index type is `{I : Type w}`.
  There is no artificial relation restricting the index universe.
- Set-indexed covering family: `(Yᵢ : I → AlgebraicSpace S)` and
  `(g : ∀ i : I, Yᵢ i ⟶ Y)`.
- Flatness on etale scheme charts: `(hflat : ∀ i : I, MapIsFlat (g i))`.
  `MapIsFlat` is `MapIsLocally (@Flat)`, testing all compatible etale scheme charts.
- Local finite presentation on the same charts:
  `(hlfp : ∀ i : I, MapIsLocallyOfFinitePresentation (g i))`.
  This is the existing `MapIsLocally (@LocallyOfFinitePresentation)`.
- Joint surjectivity: `(hsurj : IsJointlySurjective (fun i : I ↦ (g i).hom.hom))`.
  Its existing definition says that every field-valued representative lifts after a
  field extension to one member, exactly the union-of-images condition on point classes.
- Closed immersion of f: `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
  f.hom.hom`. Unfolding the recorded predicate quantifies over EVERY scheme T over S
  and EVERY Yoneda map to Y, giving a scheme U, its projection p to T, a representing
  pullback square, and the scheme closed-immersion condition on p. Thus it includes
  representability, rather than assuming it or merely asserting a topological condition.
- The words "if and only if" are the displayed `↔`.
- Every base change is a closed immersion: the right side is `∀ i : I,
  IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
  (Limits.pullback.snd f.hom.hom (g i).hom.hom)`. This is the second projection
  X times_Y Y_i to Y_i of the underlying presheaf fibre product. Limits of sheaves
  are computed objectwise, so it is the underlying presheaf of the sheaf fibre product
  in the recorded fibre-product node. No arbitrary comparison map or schematicity
  assumption on X, Y, or Y_i is introduced.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsAlgebraicSpace`, `IsEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`, `MapIsFlat`,
  `MapIsLocallyOfFinitePresentation`. The already landed definition node
  `def-sfb-space-morphism-properties` is added to stmt_deps to cite this interface.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`:
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding plus surjective stalk maps).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`.
- Size-convention node is explicitly a metatheoretic convention with no declaration.

Available proof dependencies are imported without public visibility:
`AlgebraicSpaceFourPropertyFppfDescent.four_property_fppf_descent` (in the namespace
`AlgebraicGeometry.AlgebraicSpace`),
`AlgebraicGeometry.AlgebraicSpace.exists_finite_affine_fppf_refinement` from
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfFiniteAffineRefinement`,
`AlgebraicGeometry.isClosedImmersion_of_fpqc_cover` from
`Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent`, and
`AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage` plus fppfPrecoverage
from `Mathlib.AlgebraicGeometry.Sites.Fpqc`.
`lem-sfb-space-affine-locality` currently has no recorded Lean declaration; it is
only a proof dependency, not a prerequisite for typing this statement, and has no
module to import. Its use is retained in the complete proof docstring for stage 3.
The declaration is stated directly on the existing presheaf pullback, so it needs
neither an extra bundled fibre-product construction nor a new helper node.

Edge cases checked before writing: I may be empty, with no Nonempty/Fintype
assumption; joint surjectivity then forces an empty target. Empty X or empty test
schemes are allowed, and the closed-immersion scheme-test predicate correctly includes
empty closed subschemes. Singleton identity coverings recover the same property.
Neither f nor g_i is assumed representable, separated, quasi-compact or finitely
presented. Local finite presentation is required only of the covering maps.
Arbitrary non-quasi-compact fppf covering members are included. All scheme tests
and extension fields have the same universe as the existing algebraic-space framework.

Searches (2026-10-24; raw service responses are in sandbox searches.jsonl):

- msearch LeanFinder: "A morphism of algebraic spaces is a closed immersion if and only
  if its pullbacks to a jointly surjective flat locally finitely presented family are
  closed immersions": 8 hits, all scheme closed-immersion facts or universally-closed
  scheme descent; no algebraic-space statement.
- msearch Loogle: `"IsClosedImmersion", "Flat"`: 0 hits.
- msearch grep, AlgebraicGeometry: `closed.*immersion.*(descend|fppf|fpqc)|
  (descend|fppf|fpqc).*closed.*immersion`: 0 hits.
- msearch LeanSearch: "Closed immersions of algebraic spaces descend along jointly
  surjective flat locally finitely presented covering families": 8 hits on scheme
  closed immersions and scheme-property descent, no requested space statement.
- rg on lean/WeilConjectures and lean/Sheaf for closed-immersion descent and this
  item's ID: scheme fpqc descent exists in Morphisms/FlatDescent and
  FpqcClosedImmersionDescent; the space four-property node descends separatedness,
  not closed immersion of an arbitrary space map. Other matches were proof references.
- rg for the proposed full declaration name and plausible variants in Mathlib,
  lean/WeilConjectures and lean/Sheaf: no declaration-name collision.
- Read the recorded IsRepresentableWith and MapIsLocally definitions and the existing
  sheaf fibre-product theorem; these already provide every notion required.

No disputed statement, correction, new definition node or dependency repair is needed.
All variables are bound explicitly, with `set_option autoImplicit false`.
Server scompile.py compiled both sandbox and library forms cleanly (1.5 seconds each),
with no errors or unexpected warnings.

## Second reading by O4

A separate clause-by-clause rereading by this worker (no other agent was started,
per dispatcher instructions) compared the source node, the complete Lean file and
all definitions occurring in the signature. The maintainer supplies the independent
review. The second projection is to Y_i, not X; the closed-immersion assertion
includes a representing scheme on every test, not only a condition on an atlas;
the cover hypotheses use chartwise flatness/local finite presentation, not stronger
representability hypotheses. The index universe is arbitrary and no empty case is
excluded. The only metadata adjustment was adding the already landed chartwise
morphism-property definition node to stmt_deps; the natural-language statement,
proof and proof_deps are unchanged. No semantic mismatch was found or repaired.
