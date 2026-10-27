## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupProductIdealComparison` states
`AlgebraicGeometry.AlgebraicSpace.existsUnique_blowupPresentation_product_iso`, with
one whole-proof `sorry` and no new definitions. I read Stacks Spaces Divisors,
`lemma-blowing-up-two-ideals` (Tag 085Y), including its proof, in the local source.
The current blueprint unit is `sk-thm-sf-ctf-stability`; this is an auxiliary
blowup comparison below its direct-image prerequisite chain, not a unit statement.
No statement correction or dispute is needed. The source allows arbitrary
quasi-coherent ideals; the node requests its finite-type specialization, retained here.

Clause-by-clause rendering:

- The base scheme is `{S : Scheme.{u}}`; the arbitrary algebraic space is
  `(T : AlgebraicSpace S)`. All universes and variables are explicitly bound, and
  autoImplicit and relaxedAutoImplicit are disabled. The existing algebraic-space
  interface fixes scheme and section universe `u`, with small-site object universe
  `u+1`. No new universe equality or smallness hypothesis is imposed.
- The two quasi-coherent ideals are `(I H : QuasiCoherentIdeal T)`. This existing
  subtype consists of actual subobjects of the existing structure module satisfying
  the recorded local-presentation predicate, not unrelated modules or arrows.
- Finite type is `(hI : (I.val : T.Modules).IsFiniteType)` and the corresponding
  `hH`. Mathlib's predicate means finitely many generators locally; there is no
  global finite-generation or finite-presentation hypothesis.
- The first blowup and its structure map are `(B : BlowupPresentation I)` and
  `B.projection`. The existing presentation requires its affine etale chart squares
  to be cartesian squares of ordinary scheme blowups, hence describes precisely
  the descended Rees Proj used in the node. No extra chart data are assumed.
- The extended ideal H1 is existentially named as `H₁ : QuasiCoherentIdeal B.space`.
  Its defining clause is a factorization of the existing canonical
  `idealTensorMap B.projection H` through `H₁.val.arrow` with
  `PresheafOfModules.IsLocallySurjective B.space.etaleTopology a.val`. Because the
  second map is the subobject inclusion, this says exactly that H1 is the sheaf
  image of the tensor map: its sections locally lift to pulled-back sections.
  It neither chooses an arbitrary map nor assumes sectionwise surjectivity.
  A generic `imageSubobject` spelling did not synthesize `HasImage` on this large
  small-site encoding; the locally-surjective factorization expresses the same
  image with no extra hypothesis and no new helper definition.
- The product ideal is existentially named as `L : QuasiCoherentIdeal T`. For
  EVERY etale test `V`, its inclusion's range equals
  `idealPowerSubsheafSections I.val.arrow (SheafOfModules.unit T.structureSheaf)
    (fun W ↦ Set.range (H.val.arrow.val.app (op W))) 1 V`.
  By the read definition, this is the sheaf of sections locally in the span of
  products i*h. It is exactly the image of I tensor H -> O, including on nonaffine
  tests where global sections need not commute with tensor or image. The ideals
  are determined as subobjects by these two image descriptions; the existential
  binders merely name these canonical objects, with no hollow data construction.
- The second blowup is any `(C : BlowupPresentation H₁)`, with structure map
  `C.projection`; the product blowup is any `(D : BlowupPresentation L)`, with map
  `D.projection`. Quantifying over presentations expresses the statement for the
  node's specified blowups, independently of their isomorphic models.
- The canonical isomorphism is `∃! e : C.space ≅ D.space` satisfying
  `e.hom ≫ D.projection = C.projection ≫ B.projection`. This is precisely
  b_(IH) composed with e = p composed with q, in Lean's left-to-right notation.
  Uniqueness expresses canonicity: any over-base map to the product blowup is the
  same universal lift. Its proof is already the node's final uniqueness step,
  rather than an additional geometric condition.
- No quasi-compactness, quasi-separatedness, reducedness, density, nonemptiness,
  or Noetherian hypothesis occurs. The opening immersion and qc/qs conventions are
  contextual definitions, not additional assertions or hypotheses; their existing
  modules are available through the public imports.

Existing statement interfaces used (all source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its small etale site, structure sheaf and `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and
  Mathlib's `SheafOfModules.IsQuasicoherent`, used by `QuasiCoherentIdeal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`:
  `QuasiCoherentIdeal` and `idealTensorMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleTensorPullback`, `moduleTensorAdjunction`;
  the canonical tensor map uses this recorded adjunction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees`: `idealPowerSubsheafSections`
  and `idealSectionImage`, with existing definition-node ownership
  `def-sfb-space-ideal-power-products`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation`:
  `BlowupPresentation` and `blowupChartIdeal`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`,
  used by the chart presentation.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: the existing
  `PresheafOfModules.IsLocallySurjective`, the underlying additive local-image
  predicate. This is generic image vocabulary, not a new independent notion.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`
  and the chartwise properties. These render the node's contextual conventions;
  none creates an extra condition on T.
- `def-weil-size-convention` is metatheoretic and has no declaration to import.

The three additional stmt_deps are existing landed definition nodes:
`def-sfb-space-quasi-coherent-ideal`, `def-sfb-space-blowup-presentation`, and
`def-sfb-space-ideal-power-products`. No new node and no dependency module is supplied.

Proof dependencies imported without public visibility:
`AlgebraicSpaceModulePullbackQuasiCoherent.isQuasicoherent_moduleTensorPullback`,
`AlgebraicSpaceAffineChartCalculus.quasiCoherent_affine_chart_calculus`,
`SpaceChartTensorRealization.space_chart_adjunction_tensor_realization`,
`AlgebraicSpaceFibreProductsEtaleCovers.fibreProduct_isAlgebraicSpace` and its
etale-cover clauses (all declarations in namespace AlgebraicGeometry.AlgebraicSpace);
`WeilConjectures.Blowup.BlowupUniversal` for
`Scheme.IdealSheafData.IsInvertible.comap_blowupMap` and `of_mul_left`; and
`AlgebraicSpaceBlowupUniversalProperty.existsUnique_lift_blowupPresentation`.
Their read signatures supply the proof plan documented in five steps above the theorem.
`lem-sfb-space-blowup-chart-properties` has no recorded Lean module at this time,
so its not-yet-stated proof import is omitted under stage 2 rule 7. It is only a
proof dependency and is not required to type this statement.

Edge cases checked mathematically: the empty space has its unique ideals and
empty blowups. If I or H is zero, the appropriate iterated and product blowups
are empty. If I is the unit ideal, the first blowup is the identity and the
comparison is the H blowup; if H is the unit ideal the second blowup is the
identity and the comparison is the I blowup. Nilpotent centres (including on a
nonreduced scheme) give empty blowups when nilpotent, compatibly on both sides.
Empty generating families and the zero ring are not excluded. On nonaffine tests
both image clauses use local lifting/generation; neither replaces a sheaf image
by its pointwise range on global sections. The uniqueness clause holds also in
these cases by the existing universal lifting property.

Searches for an existing statement, using msearch.py (full returned records in
sandbox searches.jsonl): LeanFinder query "For two finite type quasi coherent
ideals on an algebraic space, blowing up one then the extension of the other is
the blowup of their product" returned eight scheme ideal-inclusion/quotient
results, none this statement. Loogle query `"blowup", "mul"` returned zero hits.
Mathlib grep `[Bb]lowup.*(mul|prod)|blowing.*two.*ideals` in AlgebraicGeometry
returned zero hits. LeanSearch query "Successive blowups of two quasi coherent
ideals on an algebraic space agree with the blowup of their product" returned
basic-open multiplication, product ideals and quotient results, none a blowup
comparison. Project rg searches for blowup/product/mul/iso and
`BlowupPresentation` found only the scheme comparison
`Scheme.IdealSheafData.exists_blowup_mul_iso` and consumers referring to this
unstated algebraic-space node. The scheme result has schemes as its objects,
so is not an existing match for arbitrary algebraic spaces. Searching the item
id in WeilConjectures and the proposed declaration name in WeilConjectures,
Sheaf and dag/lean_names_upstream.json found no declaration. Existing ideal,
ideal-power and blowup notions found in Sheaf are reused without copies.

Validation: prescribed scompile.py compiled both the sandbox and the actual
library module cleanly (1.8 s and 2.3 s), without warnings. The sole theorem has
`by sorry`; all dependency data come from the existing library. Dry-run and
final delivery results follow below.

The final dry run passed: `OK (dry run): commit f35c8de687d passes the preflight
and compiles; nothing pushed`. An earlier dry run identified one overlong proof-docstring
line; it was wrapped and the clean dry run above was repeated. Signature/JSON
identity and the 100-character line limit were also checked locally.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
