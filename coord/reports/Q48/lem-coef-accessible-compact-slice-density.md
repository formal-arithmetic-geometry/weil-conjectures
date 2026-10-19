## Worker report

The module `lean/Sheaf/CategoryTheory/AccessibleCompactSliceDensity.lean` defines
`SSet.Presentability.compactObjects`, the replete full subcomplex on all
`IsKappaCompact` objects; `compactSourceSlice`, the coherent full slice of arrows into a
fixed `x` whose sources are compact; `compactSourceProjection`, the canonical source
projection to `C`; and `IsTautologicalCocone`, which records that a cocone has apex `x`.
It states `SSet.Presentability.accessible_compact_slice_density` with proof `sorry`.

The theorem hypotheses are rendered as follows. The first binder is an infinite regular
cardinal `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`. The accessible quasicategory is
`(C : SSet.{max (u + 1) v}) [SSet.Quasicategory C]`, and
`(hC : IsKappaAccessible C κ)` is the stated accessibility hypothesis. The first
conclusion is `IsEssentiallySmall (compactObjects (C := C) κ).toSSet`, expressing
essential smallness of the compact-object subcategory. For every `x : C _⦋0⦌`, the
second conclusion gives essential smallness of `compactSourceSlice (C := C) κ x`; it
then supplies a quasicategory witness `hSlice` and
`@IsKappaFiltered κ (compactSourceSlice (C := C) κ x) hSlice`, including the empty
indexing simplicial set through the dependency definition. Finally it supplies a cocone
`t` on `compactSourceProjection (C := C) κ x`, requires
`IsTautologicalCocone (C := C) κ x t` (apex `x`, with the slice's canonical legs), and
requires `SSet.Enhanced.IsColimiting ... t`, which is the density/colimit clause.

Dependencies used:

- `def-coef-presentable-infinity-category`: `SSet.Presentability.IsKappaSmall`,
  `IsKappaFiltered`, `IsEssentiallySmall`, `IsKappaCompact`, and
  `IsKappaAccessible` from `Sheaf.CategoryTheory.PresentableInfinityCategory`.
- `def-cbc-enhanced-diagrams-cones`: `SSet.Enhanced.fullSubcomplex`, `coneCategory`,
  `coconeCategory`, `IsColimiting`, and `SSet.Enhanced`'s coherent simplicial-set
  conventions from `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
- The proof dependency `lem-cbc-enhanced-functor-cone-calculus` supplies
  `SSet.Enhanced.calculusApex` for the canonical source projection.

I checked the empty indexing simplicial set (it is included by `IsKappaFiltered`), the
terminal indexing shape, and `κ = ℵ₀` (accepted by `Cardinal.IsRegular`). The compact
source predicate is vertexwise and therefore includes the empty slice and all identity
arrows; no nonemptiness or extra colimit hypothesis was added.

Searches made: `msearch.py ... leanfinder "compact source slice of an accessible infinity
category is essentially small filtered and dense"` returned ordinary-category
presentability/density declarations but no coherent quasicategory statement; `msearch.py
... loogle "IsKappaAccessible, IsKappaFiltered, IsEssentiallySmall"` returned no exact
Mathlib identifier; `msearch.py ... grep "compact.*slice|accessible.*quasicategory|IsKappaFiltered"
CategoryTheory` returned no hits. `rg` over `WeilConjectures/` and project `lean/Sheaf/`
found only the recorded presentability interface and no declaration of this theorem.
The recorded Mathlib searches in the node similarly found only ordinary-category results,
which do not retain coherent mapping spaces. The module was compiled with
`scompile.py` and had no errors or warnings.

## Earlier second reading (a previous round; superseded)

The statement was checked against each clause of the node. `compactObjects` is the full
subcomplex on exactly the `IsKappaCompact` vertices; `compactSourceSlice` is the full
coherent slice on arrows whose source is compact; and `compactSourceProjection` is the
canonical apex/source map from that slice into `C`. The existential `hSlice` supplies the
quasicategory structure required by the recorded `IsKappaFiltered` definition, including
its empty-shape case. The final cocone has apex `x` through `IsTautologicalCocone` and is
required to be colimiting. Universes are explicit and preserve the smaller cardinal
universe in `Cardinal.{u}` while allowing `C` in `SSet.{max (u + 1) v}`. The module was
recompiled cleanly after this review.


## Second reading by Q48

I read the node statement against HTT Proposition the project server(2)--(3), Lemma the project server,
and Corollary the project server (HTT pp. 424--425; the source is not archived locally). The
objects and clauses are rendered as follows.

* The infinite regular cardinal is `(κ : Cardinal.{u})` with
  `hκ : κ.IsRegular`; the accessible quasicategory is
  `C : SSet.{max (u + 1) v}` with `[SSet.Quasicategory C]` and
  `hC : IsKappaAccessible C κ`. This has the node's smaller-cardinal and containing
  universe convention and adds no finiteness or nonemptiness assumption.
* The replete full subcategory (D) of all (kappa)-compact objects is
  `compactObjects (C := C) κ`, defined by the dependency's
  `IsKappaCompact` predicate and `Enhanced.fullSubcomplex`. The first conclusion
  is exactly `IsEssentiallySmall ...toSSet`.
* For each `x : C _⦋0⦌`, the coherent slice (D_{/x}), whose objects are arrows
  from compact sources into `x) and whose higher simplices retain the coherent
  triangles, is `compactSourceSlice (C := C) κ x`. Its source projection to
  `C` is `compactSourceProjection`, extracting the cone apex and then including it
  in `C`. The second conclusion is its essential smallness.
* The existential `hSlice : SSet.Quasicategory (compactSourceSlice ...)` supplies
  the quasicategory structure needed by
  `@IsKappaFiltered.{u, max (u + 1) v} κ ... hSlice`; the definition tests every
  (kappa)-small coherent simplicial set, including the empty one. This is the
  node's filteredness clause.
* The final existential is a cocone over the source projection. Its apex equation is
  `t.1.1 = x`, and `IsTautologicalCocone` now also requires equality of the whole
  `coconeHomotopy` with the canonical coherent transformation extracted from the
  arrows in the compact-source cone category. Thus all components and higher
  coherences are fixed, rather than only the apex. The final conjunct is exactly
  `SSet.Enhanced.IsColimiting ... t`, giving the density colimit.

The previous module's `IsTautologicalCocone` only checked the apex and therefore
allowed a colimiting cocone with arbitrary legs (for example, postcomposition by an
automorphism of `x`). I repaired it by adding
`compactSourceTautologicalEdge` and
`compactSourceTautologicalHomotopy`, using the canonical
`Enhanced.calculusCommaArrow` of the cone construction, evaluation at
`Delta[0]), and the existing `Enhanced.coconeHomotopy`. The node copy records
these declarations and adds the existing
`lem-coef-infinity-final-index-colimit` interface as a statement dependency.
No target-unit statement was changed.

Edge cases checked: the empty indexing simplicial set is included by
`IsKappaFiltered`; (kappa=aleph_0) is admitted by `Cardinal.IsRegular);
the terminal/one-object slice and degenerate identity arrows are included; empty
`C), empty compact subcategory, and empty slices are not excluded by any binder.
The source projection and canonical cocone retain the zero-simplex and all higher
coherent data.

Searches were repeated with `msearch.py` LeanFinder/Loogle/grep queries for
compact-source slices, accessible quasicategories, and filtered coherent slices;
Mathlib's ordinary-category presentability and costructured-arrow declarations were
inspected and rejected as they use set-valued Hom rather than coherent mapping spaces.
`rg` over the slopmaster2 source and project `lean/Sheaf` found no duplicate
definition or theorem. The existing dependency modules
`PresentableInfinityCategory`, `EnhancedDiagramsCones`,
`EnhancedFunctorConeCalculus`, and `FinalIndexColimit` were read at their exact
declarations. The repaired module compiles cleanly with `scompile.py`.


## Maintainer review fix (cc second reader, 2026-10-17)

The delivered theorem left the universe of both `IsEssentiallySmall` clauses unconstrained.
Lean generalized them into two extra universe parameters `u_3`, `u_4`, so the theorem
claimed essential smallness in *every* universe, universe 0 included. That is stronger than the node
and false in general. Both clauses are now `IsEssentiallySmall.{u}`, so they mean `U`-small with
`κ : Cardinal.{u}`. The theorem now has exactly the universes `u v`.

The statement also used `SSet.Enhanced.calculusApex` and `calculusCommaArrow` of
`lem-cbc-enhanced-functor-cone-calculus`, which is not a statement dependency of the item.
They are replaced by the module's own `compactSourceApex` / `compactSourceArrow`, defined
from the `def-cbc-enhanced-diagrams-cones` declarations as `commaSubcomplex.ι ≫ fst` and `≫ snd`. These
are definitionally equal to the previous projections (checked by `rfl`). The
`EnhancedFunctorConeCalculus` import is dropped. That node remains a proof tool (`tool_uses`).
Nothing else changed. The module compiles clean.
