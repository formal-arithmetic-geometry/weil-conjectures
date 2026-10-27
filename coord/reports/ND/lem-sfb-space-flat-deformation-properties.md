## Worker report

States `AlgebraicGeometry.AlgebraicSpace.flat_deformation_properties` in
`Sheaf.AlgebraicGeometry.SpaceFlatDeformationProperties`. Its proof alone is `sorry`.
The auxiliary `flatDeformationMap` has actual data: Mathlib's `pullback.map` on
fppf sheaves, bundled by `ObjectProperty.homMk`. Its components are the identity
of B and the given morphism; its square equation comes from `Over.w`. This is
the canonical reduction map, not a chosen or independently assumed morphism.

Source read: `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-deform-property`, Tag 0CG6, statement and chart-reduction proof.
The node selects the first-order case of this finite-order result and the
isomorphism, properness and finite-presentation conclusions. No mathematical
statement correction is needed. The module docstring contains all eight steps
of the accepted node proof and identifies their dependencies.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| A scheme S and its algebraic spaces | `{S : Scheme.{u}}`, `{B B' : AlgebraicSpace S}`; this is the existing fppf-sheaf category with its small etale site and structure sheaf. |
| Size convention | Explicit `universe u`; the imported space model uses `Scheme.{u}`, the big site `Over S`, and `Type u` sheaves. No universe equality or smallness assumption is added. |
| First-order thickening B into B' | `(i : B ⟶ B') (hi : IsSpaceFirstOrderThickening i)`. The imported predicate tests every scheme base change with `IsFirstOrderThickening`: closed immersion and square-zero kernel ideal sheaf. Nilpotence implies its closed image is the whole underlying space, including the empty case. |
| P' and Q' over B' | `{P' Q' : Over B'}`; their total spaces are `P'.left` and `Q'.left`, with structure maps `P'.hom` and `Q'.hom`. These are algebraic spaces, not schemes. |
| P' flat over B' | `(hflat : MapIsFlat P'.hom)`. The existing predicate is the universal test on compatible etale scheme charts with Mathlib `Flat`. |
| A B'-morphism h' | `(h' : P' ⟶ Q')` in the slice. Its underlying map is `h'.left`, and `Over.w h'` is exactly its base compatibility. |
| P and Q are base changes to B | The helper's domain and codomain are `enlargedFibreProduct i P'.hom` and `enlargedFibreProduct i Q'.hom`, the actual sheaf pullbacks bundled using `fibreProduct_isAlgebraicSpace`. |
| h is the restriction of h' | `flatDeformationMap i h'` is `pullback.map` with identity on B and h' on the other factor, over the identity of B'. It is defined without using any deformation theorem. |
| Isomorphism iff | First conjunct: `IsIso h'.left ↔ IsIso (flatDeformationMap i h')`. |
| Proper iff | Second conjunct: `MapIsProper h'.left ↔ MapIsProper (flatDeformationMap i h')`. |
| Proper means separated, qc, lft, universally closed | Imported `MapIsProper` unfolds to separatedness, finite type and universal closedness; `MapIsFiniteType` is qc and chartwise Mathlib `LocallyOfFiniteType`. `MapIsSeparated` tests the relative diagonal by closed immersions. `MapIsUniversallyClosed` tests closedness on points after every algebraic-space base change. |
| Finitely presented iff | Last conjunct compares, on each side, `MapIsLocallyOfFinitePresentation`, `MapIsQuasiCompact` of the map, and `MapIsQuasiCompact` of its `pullback.diagonal`. |
| Local finite presentation | Imported `MapIsLocallyOfFinitePresentation` tests every compatible pair of etale charts using Mathlib `LocallyOfFinitePresentation`. |
| Quasi-separated means qc diagonal | The third finite-presentation factor is explicitly `MapIsQuasiCompact (pullback.diagonal ...)`. |

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, and its small etale site and structure sheaf.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` (the bundled pullback's property).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  `IsSeparated`, `UniversallyClosed` as the scheme conventions implemented by the
  existing space predicates.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact`; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion`, used by the representable chart tests and thickening predicate.
- Added the already landed owning nodes `def-sfb-space-morphism-properties`,
  `def-sfb-space-square-zero-extension-data`,
  `def-sfb-space-sheaf-fibre-product`, and `def-sfb-proper-curve-moduli` to
  `stmt_deps`. These own `MapIsFlat`, `MapIsProper`,
  `MapIsLocallyOfFinitePresentation`, `IsSpaceFirstOrderThickening`,
  `enlargedFibreProduct` and `MapIsQuasiCompact`. The public import of
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` is retained for the concrete
  fibre-product definition, whose owner is the existing definition node, not the
  enlarged-ringed-site theorem. `MapIsQuasiCompact` is publicly available through
  `AlgebraicSpaceMorphismProperties`. No duplicate definitions or dependency repairs
  are needed.
- Plain imports retain all the recorded proof modules: representable etale scheme
  tests, flat/proper/fp locality, chart tests, quotient base-change ideals,
  locally finite type across thickenings, relative flat algebra fp lifting,
  flat-fibre etale neighbourhoods, scheme etale source/target locality, and
  source-atlas detection. `Mathlib.CategoryTheory.Limits.MorphismProperty` supplies
  the proof dependency for etale base-change finite limits. Four proof-only nodes
  have no declaration yet: space thickening base change, thickening topological
  properties, nilpotent-fibre flat modules, and etale-thickening isomorphism detection;
  their proof steps remain documented, and no new theorem is assumed for the statement.

Edge cases checked mathematically before writing: identity base thickening (zero
ideal), empty base or total spaces, arbitrary characteristic, non-Noetherian bases,
non-quasi-compact atlases, and targets Q' not flat over B'. None are excluded by the
binders. Only P' is assumed flat; no separation, finite presentation, representability
of h', or flatness of Q' is assumed. The finite-presentation clause retains qc and
quasi-separatedness and thus does not silently reduce to local finite presentation.

Existing-statement searches:

- `msearch.py ... leanfinder "An isomorphism, proper morphism, or finitely presented morphism of algebraic spaces lifts across a square zero base thickening when its source is flat"`:
  eight hits, including scheme flatness and universal openness; no deformation result.
- `msearch.py ... loogle "AlgebraicGeometry.Flat, CategoryTheory.IsIso"`:
  six hits about scheme pushout sections, flat monomorphisms, and finite flat rank;
  none gives these three equivalences over a thickening of algebraic spaces.
- `msearch.py ... grep "deform|Thickening" AlgebraicGeometry`:
  one Mathlib hit in `FormallyUnramified.lean` about uniqueness of infinitesimal lifts;
  no matching theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for flat deformation, deformation
  properties, `flat_deformation_properties`, `flatDeformationMap`, and `deform.*property`:
  related ring deformation and relative algebra fp results only, no same statement.
  The grep for this item's blueprint id in `lean/WeilConjectures` returned no hit.
- `rg` in `dag/lean_names_upstream.json` for the new names and deformation-property
  names returned no hit. Inspection of existing space modules found the reused
  interfaces above; no new independent notion is introduced.

Validation: prescribed `scompile.py` compiled both the sandbox probe and the named
library module cleanly (1.9 and 1.8 seconds respectively), with no unexpected warnings.
Only the item's `lean` and the four definition-node additions to `stmt_deps` are changed.
No STATEMENT-DISPUTED issue or source fault was found.

## Repair of returned head 480214d3dd72

H2 repaired exactly as requested: replaced the statement dependency
`lem-trf-space-enlarged-etale-ringed-site-model` with its existing definition owner
`def-sfb-space-sheaf-fibre-product`, and added `def-sfb-proper-curve-moduli`, the
owner of `MapIsQuasiCompact` used directly in the finite-presentation clause.
Read both current owner nodes and the declarations in `EnlargedEtaleRingedSite`
and `ProperCurveModuli`. The fibre product is a plain definition with concrete
sheaf-pullback data, not a choice from the enlarged-site theorem.

Compared the retained returned node with current main: before repair only `lean`
and `stmt_deps` differed. Rebased the node copy on current main, preserving all its
other fields. The public imports and all Lean bytes are unchanged from the returned
delivery. The retained Lean file SHA-256 is
`4148cb39dc0646cd971ca2c9d0394f1bc421c948fd063e461b964a4df0078deb`.
The mathematics, signature, canonical map, eight proof steps and single postponed
proof remain exactly those accepted in the return. Compilation and delivery
preflight are rerun for this repair.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
