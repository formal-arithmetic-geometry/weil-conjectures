## Worker report

This repairs the immutable returned head b020bc0ed8ef. The saved packet's initial
prescribed dry run passed mechanically at b7663ac87c, but the self-check confirmed
that its free fields still had the mathematical defect identified in the return.
The module has therefore been repaired substantively, rather than re-pushed unchanged.

Module: `lean/Sheaf/CategoryTheory/AlgebroidCotensorNerveExchange.lean`.
The sole postponed theorem remains `SSet.Enhanced.Algebroid.cotensor_nerve_exchange`.
Every helper definition has actual data; no additional postponed theorem, independent
notion, dependency module, new node, or informal statement correction is introduced.
The helpers are constructions belonging to this item's comparison, recorded in
`lean.declarations` under the owning node as permitted by brief-stage2 section 1.

The binders remain unchanged. `EV`, `p`, `hV`, and `unitV` are the presentably
monoidal coefficient presentation and unit section. `ES`, `q`, `hS`, `spaces`, and
`unitS` are the cartesian-space coefficient presentation. `SpatialCotensorData`
supplies the spatial action, normalized finite unit diagrams, cotensor, its coherent
mapping-space adjunction, and its unit equivalence. Universes remain independent
`u,v`, with the same small and containing levels as the dependencies. No completeness,
symmetry, inhabitedness, or new equality of universes is assumed.

Clause-by-clause correspondence:

* `cotensorFiniteObject ... C n` is exactly D_n = C^{E^n}, using the dependency's
  `spatialCotensorAt` and `unitAlgebroid`, rather than an arbitrary object.
* `cotensorNerveSmallBifunctor` is the coherent functor
  (m,n,C) ↦ Map(E^m,C^{E^n}) in `data.mapping.hom.bifunctor`'s small presentation.
  It is defined by precomposition with the two existing `unitCosimplicial` diagrams,
  the opposite functor, and `data.cotensor`. `mapping_exchange` states
  `AreNaturallyEquivalent` between this actual functor and its parameter swap.
  All maps and higher simplices in C,m,n are part of these functors. There are no
  independently specified finite operators or algebroid-map fields.
* `cotensorNerveBifunctor` presents the same spaces in the dependency's canonical
  containing-universe `nerveBifunctor`, whose final map is the canonical coherent
  Hom pairing `CategoryTheory.Spaces.yonedaPairing`. `cotensorNerveFamily` is the
  actual lifted cotensor on `nerveSource unitS`, and `exchange` states its coherent
  parameter-swap equivalence. These are two universe presentations of the same
  mapping spaces, not new definitions of the algebroids, Hom, nerve, or cotensor.
* `cotensorNerveSwap` exchanges only the two simplex parameters, retaining C.
  `AreNaturallyEquivalent` means an equivalence edge in the full coherent functor
  category, so it retains faces, degeneracies, their higher coherences, and
  naturality in all algebroid simplices at once. In particular it supplies the
  requested equivalences in every bidegree, including zero.
* `nerve_restriction`, `nerve_colimit`, and `nerve_apex` give precisely the existing
  `IsNerveRealization` interface: a coherent augmented extension of `nerveBifunctor`,
  colimiting for every C, whose apex is the actual `iota unitV C`.
* `realization_restriction` fixes the entire base of `realization` to
  `cotensorNerveBifunctor`. `cotensorNerveColumn realization m C` is therefore the
  augmented diagram whose base is n ↦ I_m(C^{E^n}), not an arbitrary constant diagram.
  `realization_colimit` requires the actual cocone to be colimiting.
* `realization_comparison` is an equivalence of ENTIRE augmented diagrams to
  `nerveRealization` evaluated on C^{E^m}. Its base restricts to the exchanged
  bisimplicial functor; its apex is the induced colimit comparison
  |I_m(D_bullet)| ≃ I(C^{E^m}). Since the remaining index and C are full functor
  variables, the comparison and realization remain natural in them. This is stronger
  bookkeeping of the stated coherent comparison, not an extra mathematical hypothesis.
* `cotensorNerveCollapse` is literally `spatialCotensorEdge data.cotensor C
  (data.finiteS.edge m 0 (fun _ ↦ 0))`. It is the specified edge
  C^{E^0} → C^{E^m}. The canonical cotensor unit identifies its source with C.
  `IsCotensorNerveCollapse` fixes the unit equivalence to the witness of the supplied
  `data.cotensor_unit`. Two inverse triangles fix b:C → C^{E^0} as its inverse;
  the third triangle fixes a_m as b followed by this actual collapse edge.
  Thus the existential a_m in `normalized_collapse` is a composite determined up to
  the coherent homotopy used in the statement, not a free choice of an algebroid map.
* `cotensorNerveCollapseIndex m` is the opposite of the actual ordinal collapse
  [m] → [0]. Its image under `cotensorNerveApex realization` is the actual realized
  arrow |I_0(D_bullet)| → |I_m(D_bullet)|. `collapse_correspondence` identifies it
  with the coherent realization of the canonical unnormalized cotensor edge.
  `normalized_collapse` also explicitly identifies it with
  `cotensorNerveRealizedArrow nerveRealization a.edge`, i.e. I(a_m), with the source
  identified via the unit inverse just specified. This supplies the missing clause.
  `cotensorNerveRealizedArrow` applies the existing realization functor at its apex
  to the actual algebroid edge; it never supplies an independent map on I.
* `normalized_collapse` requires `IsWeakHomotopyEquivalence` of the dependency's
  canonical target leg `iotaMorphismLeg ... (algebroidArrow a.edge) 1`, the recorded
  span model for I(a_m). `collapse_equivalence` retains the corresponding assertion
  before unit normalization. Both conclusions are consequences of the same finite
  categorical-equivalence and fully-faithful/essentially-surjective criteria.

Dependency declarations used (their recorded source signatures and docstrings were read):

* `Sheaf.CategoryTheory.CompleteAlgebroid`: `total`, `UnitSection`, `unitAlgebroid`,
  `unitCosimplicial`, `iota`, `iotaMorphismLeg`, `IsPresentablyMonoidal`.
* `Sheaf.CategoryTheory.AlgebroidCategoricalHomotopy`: `SpatialCotensorData`,
  `CartesianSpaceCoefficients`, `spatialCotensorAt`, `spatialCotensorEdge`, and its
  normalized `finiteS` diagram and `cotensor_unit` equivalence.
* `Sheaf.CategoryTheory.AlgebroidEquivalenceNerve`: `nerveSource`, `nerveBifunctor`,
  `algebroidArrow`, and its `IsNerveRealization` interface.
* `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus` is retained as the recorded
  proof dependency for transferring equivalences of whole cocones and their colimits.

Source checked: [GH arXiv:1312.3178v4](https://arxiv.org/html/1312.3178v4),
Corollary 4.3.17 and the last completeness paragraph of Theorem 5.6.2, together
with the node's five-step expansion to arbitrary m. The theorem docstring now
carries all five proof steps and explains the normalization triangles explicitly.

Edge cases checked before repairing: m=0, n=0, m=n, every face and degeneracy,
empty C and empty mapping spaces, nonsymmetric V, and independent small/containing
universes. The collapse still has the nonempty finite sets m+1 and 1 as its labels
at m=0. There is no chosen object of C, so the empty case remains admitted.

Searches retained and repeated: the inherited LeanSearch, LeanFinder, Loogle and
Mathlib grep searches were read. Fresh `msearch.py` LeanFinder query was
“coherent natural equivalence between the bisimplicial spaces Map(E_m, C cotensored
with E_n) and its exchange, preserving realization and the collapse map”: eight hits
on standard-simplex products, ordinary Dold-Kan, and simplicial closed structure;
none states this operadic result. Loogle `AreNaturallyEquivalent, cotensor` returned
zero hits (the first name is project-specific). Mathlib grep
`cotensor|Cotensor|bisimplicial` in CategoryTheory/Enriched and project `rg` searches
for cotensor/nerve/exchange and the node id found no existing statement. The recorded
dependencies supply all required constructions. No duplicate notion was introduced.

## Second reading by Q20

Author self-check, as required for direct worker delivery; the maintainer supplies
the independent reading. Compared the saved returned packet with its named defects,
the item node, and the current dependency source modules. The original free exchange
maps, unused finite-function and algebroid-edge binders, arbitrary realization base,
and free collapse map were removed. The new comparison functors use actual maps in
all three variables. The realization base is fixed by equality of whole functors;
a constant diagram can no longer witness an unrelated realization. The collapse
uses the supplied finiteS edge and cotensor unit, and both its unnormalized and
unit-normalized I-arrow correspondences are explicit. The statement and its
hypotheses, dependency list, and proof plan have not changed.

Every definition was checked for real data and every universe and binder is explicit.
The only `sorry` is the target theorem. No `STATEMENT-DISPUTED` remains.
Compilation and final delivery preflight are recorded by the prescribed wrappers.
