## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence`
states `AlgebraicGeometry.AlgebraicSpace.ideal_closedSubspace_correspondence`, with
`by sorry` as its entire proof. No mathematical theorem is proved. Two definition
modules supply the exact source and target of the correspondence; all their data
are actual Mathlib subobjects, predicates and the existing adjunction hom equivalence.
No statement correction or dependency-interface replacement is needed.

The inherited previous BLOCKED ending concerned stage 1. The current queue assigns
this item to stage 2 and it has no Lean record. `coord/brief-stage2.md` section 0 now
explicitly permits this handoff from a reviewed stage-1 split. The accepted statement,
proof and reviewed split are preserved.

Clause-by-clause check against the node and Stacks Tag 03MB:

- The base scheme is `(S : Scheme.{u})`. Every `X`, `Y` is an `AlgebraicSpace S`.
  The same universe `u` as the recorded dependency interfaces is used; no equality
  between unrelated universes or auxiliary size hypothesis is imposed. Site objects
  retain universe `u+1`, module carriers universe `u`.
- Small-etale module sheaves are the existing `X.Modules`, namely
  `ringedSiteModules.{u} X.structureSheaf`. Quasi-coherence is exactly
  `SheafOfModules.IsQuasicoherent`; tensor/direct image and the adjunction are exactly
  `moduleTensorPullback`, `moduleDirectImage`, `moduleTensorAdjunction`.
- A closed subspace is `ClosedSubspace X`: a `Subobject X` with
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)` on its arrow.
  Categorical subobjects of these set-valued sheaves identify precisely isomorphic
  presentations of the same subfunctor, and retain scheme structure. They are not
  just closed subsets of points. The ordering is Mathlib's subobject ordering.
- A quasi-coherent ideal is `QuasiCoherentIdeal X`: an O_X-submodule of O_X, represented
  as `Subobject (SheafOfModules.unit X.structureSheaf)`, with the existing predicate on
  its domain. Since O_X is commutative, an O_X-submodule of O_X is exactly an ideal.
  No finiteness hypothesis on the ideal is imposed.
- `corr X : ClosedSubspace X ≃ QuasiCoherentIdeal X` is the bijection. The first
  universal clause fixes its value by equality with
  `kernelSubobject (moduleStructureMap C.val.arrow)`; hence it is the stated kernel
  operation, rather than an unspecified bijection. The second clause
  `C ≤ D ↔ corr X D ≤ corr X C` makes it inclusion-reversing in both directions.
- The inverse construction is `(corr X).symm I`. The factorization clause is
  `∃ l : Y ⟶ ..., l ≫ ...arrow = h ↔ idealTensorMap h I = 0`. It holds for every
  algebraic-space source `Y`; in particular, use the recorded actual Yoneda sheaf
  `schemeSpace T` for a scheme test `T : Over S`. The Yoneda correspondence identifies
  its maps with sections of the subfunctor, so this is also precisely the scheme-test
  formula for V(I), not merely a test on points or on an atlas. Factorizations are
  unique because the subobject inclusion is monic. Thus the stronger-source version
  includes the node's initial scheme-test formula without an extra assumption.
- The canonical `idealTensorMap h I` is the adjoint of the exact composite
  `I.val.arrow ≫ moduleStructureMap h`; it uses the specified adjunction and not an
  arbitrary map. The next iff states the equivalent direct-image zero criterion.
- The first clause also gives `Epi (moduleStructureMap C.val.arrow)` for every closed
  subspace. Epi here is surjectivity as a module sheaf, not necessarily surjectivity
  on sections of every chart. Together with kernel equality this states the required
  quotient map for the inverse image of every ideal as well.
- For arbitrary `h : Y ⟶ X`, the last clause gives a closed subspace `P` and an actual
  `IsPullback a P.val.arrow ...arrow h`. Algebraic spaces form the recorded full
  subcategory of fppf sheaves and their sheaf fibre products are algebraic spaces by
  `fibreProduct_isAlgebraicSpace`; this square therefore is the required sheaf fibre
  product. It uses no extra representability hypothesis on h.
- Its ideal is the image of `idealTensorMap h I`: the quantified `q` is epi onto the
  ideal `corr Y P`, and `q ≫ (corr Y P).val.arrow = idealTensorMap h I`. In module
  sheaves an epi-mono factorization specifies exactly the image subobject. This
  formulation avoids imposing existence of an ambient Abelian instance at the
  original site universe, and does not assume that h^* preserves monomorphisms.
- If `hh : IsEtale h.hom.hom`, the final `r` identifies that ideal with the existing
  restriction `(pullback h hh).obj I`. The displayed equality for every chart V and
  every section m identifies its inclusion with the restricted ideal inclusion.
  Thus the clause specifies the ideal as a subsheaf, not just its abstract module.

Dependency declarations actually used in the statement and definitions:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `Modules`, `structureSheaf`, `pullback`, `etaleMap`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (the transparent underlying module category, publicly imported by AlgebraicSpace).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the recorded slice
  instances and Mathlib's `SheafOfModules.IsQuasicoherent`, also used by `QCoh`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  `moduleTensorPullback`, `moduleTensorAdjunction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`: `moduleStructureMap`;
  the owning landed definition node is explicitly added to stmt_deps.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, specifying the sheaf-pullback interpretation.
- Mathlib `Subobject`, `kernelSubobject`, `Equiv`, `Epi` and `IsPullback`.

All already-stated proof-dependency modules are imported with plain `import`, except
those already public statement dependencies. The Mathlib scheme ideal construction,
lift, separated/integral/universally-closed facts and adjoint-colimit facts are imported
from their recorded source modules. The currently unstated proof nodes
`lem-trf-space-chart-adjunction-tensor-realization`,
`lem-sfb-space-qcoh-kernels-colimits`, and `lem-sfb-presheaf-space-target-bootstrap`
have no module to import; their exact roles remain in the theorem's proof docstring.
They are proof inputs, not missing notions needed to write this statement.

Edge cases checked before writing: I=0 corresponds to X and I=O_X to the empty
subspace, with both factorization tests correct. X or Y empty is allowed. Ideals of
arbitrary rank, nonreduced spaces (e.g. Spec k[epsilon]/epsilon^2) and non-Noetherian
spaces remain included. For the non-flat base change k[t] to k and I=(t), h^*I need
not inject into O_Y, whereas its image is zero; the epi-mono clause correctly uses
the image and imposes no flatness. For etale h the inclusion is preserved and the
componentwise restriction formula is correct. Identity maps and arbitrary ideals
are included. Neither topology alone nor radical ideals replace scheme structure.

Searches: msearch.py LeanFinder queried the full closed-subspace/ideal correspondence;
its eight hits were scheme results, led by
`AlgebraicGeometry.IsClosedImmersion.overEquivIdealSheafData`. Loogle queried that
name and found only the equivalence for a scheme X. Mathlib grep
`ClosedSubspace|QuasiCoherentIdeal|overEquivIdealSheafData` found only that scheme
module (three hits). LeanSearch queried quasi-coherent ideals and representable
closed subfunctors: eight hits for the existing general quasi-coherence predicate
and scheme ideals, no algebraic-space correspondence. For the new definitions,
LeanSearch queried subobjects of an algebraic space representable by closed
immersions and quasi-coherent subobjects; eight scheme-only hits. LeanFinder queried
quasi-coherent ideals on an algebraic space as structure-module subobjects: eight
hits for scheme ideal data and general module presentations. Mathlib grep
`ClosedSubspace|QuasiCoherentIdeal|moduleStructureMap` in AlgebraicGeometry: zero hits.
Exact queries and returned search metadata are preserved in the new nodes and in
searches.jsonl. Local rg of WeilConjectures and Sheaf found no matching algebraic-space
notion or theorem, but did locate the existing canonical moduleStructureMap, reused.
The node-id search in WeilConjectures found no hit. A scan of DAG definition statements
and blueprint_refs search (`closed subspace`: zero blueprint hits;
`quasi-coherent ideal`: 38 scheme-oriented blueprint hits) found no definition of
either new notion. The existing closed-ideal-filtration node defines powers for a
given immersion; it does not define the arbitrary ideals or closed subspaces here.
No exact existing theorem was found; the scheme equivalence is not a match for spaces.

All three files compiled through scompile.py against the published live build.
The initial main-file coercion error was repaired with explicit algebraic-space types
for the two domains of the base-change arrow; final compiles are clean.

## New nodes

`def-sfb-space-closed-subspace` owns
`Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`: the subtype of Mathlib subobjects
with the exact scheme-test closed-immersion condition. Source: Stacks 03MB, left side
of the bijection. There is no new quotient construction or postponed data. The
searches above found only scheme or unrelated spectral-topology notions.

`def-sfb-space-quasi-coherent-ideal` owns
`Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`: the subtype of structure-module
subobjects with the existing quasi-coherence predicate, and the canonical adjoint
`idealTensorMap`. Source: Stacks 03MB, right side and its final vanishing criterion.
The searches above found no algebraic-space ideal definition. The canonical structure
map is reused from its existing node, not redefined; no new theorem is needed.

## Second reading by Q75

This is a local second pass by the same worker, not an independent-agent review:
the dispatcher explicitly forbids starting agents, and the maintainer independently
reviews this delivery. I reopened the node and all three files and checked the
hypothesis/clause mapping above. I checked that subobjects retain nonreduced structure,
that the hom-equivalence direction is the inverse taking a direct-image map to its
tensor adjoint, that kernelSubobject pins the bijection, and that the etale isomorphism
also commutes with inclusions. The first compiler pass detected the category ambiguity
in P.val to C.val; explicitly coercing both objects to AlgebraicSpace S repaired it.
The arbitrary-base-change clause uses an epi onto a monic ideal, hence exactly the
image, rather than incorrectly identifying h^*I itself with an ideal. No statement
mismatch or source correction was found. No dependency node was changed.
