## Worker report

The module `Sheaf.AlgebraicTopology.CoherentFixedVertexCofibrations` states
`SSet.PinchedCube.coherent_fixed_vertex_cofibrations`, with its sole proof `sorry`.
It defines no new notion and leaves the node unchanged except for `lean`.

Clause-by-clause reading:

- Small simplicial sets and their map: `{K L : SSet.{u}} (f : K ⟶ L)`.
  The universe `u` is explicit and arbitrary, as are all binders.
- Degreewise injectivity: `hinj : ∀ n : SimplexCategoryᵒᵖ,
  Function.Injective (f.app n)`. This directly states the node's hypothesis,
  rather than relying on a monomorphism conversion.
- Bijection on vertices: `hvertices : Function.Bijective
  (f.app (Opposite.op ⦋0⦌))`.
- Fixed object set `O = K₀`: both `A` and `B` are
  `Bergner.Fixed (K _⦋0⦌)`. The recorded `FixedHom`, used by `g : A ⟶ B`,
  has identity object function and maps preserving enriched identity/composition.
- The coherent realization is exactly the recorded
  `SSet.PinchedCube.rigidification`, the left Kan extension of the subset-poset
  coherent simplex along standard simplices. No second realization is defined.
- The colimit implementation's object type need not literally reduce to `K₀`.
  Thus `eK : Bergner.bundle A ≅ rigidification.obj K` and
  `eL : Bergner.bundle B ≅ rigidification.obj L` express relabelling as actual
  enriched isomorphisms, rather than equivalences or uncharacterized replacements.
  The first universal equation pins `eK.hom.obj x` to the canonical object of the
  zero-simplex `x`, computed with `coherentSimplexUnit` and `yonedaEquiv.symm`.
  The second pins `eL.hom.obj x` to the canonical vertex `f₀(x)`.
  Since `f₀` is bijective, this is exactly the target identification by `f₀⁻¹`
  specified in the node. These are representation data for the named realizations,
  not extra mathematical assumptions or a different object set.
- The induced functor is fixed by the commuting equation
  `Bergner.bundleMap g ≫ eL.hom = eK.hom ≫ rigidification.map f`.
  Since `eL` is an isomorphism, this determines `g` exactly for these labels.
- The final clause is `Bergner.fixedCofibrations (K _⦋0⦌) g`.
  Its recorded definition is `(fixedFibrations O ⊓ fixedWeakEquivalences O).llp`.
  `fixedFibrations` tests `SSet.modelCategoryQuillen.J.rlp` on each mapping set;
  `J` includes every horn of dimensions `n+1`, `n : ℕ`, with all indices
  `Fin (n+2)`, hence every horn in positive dimension, including both outer horns.
  `fixedWeakEquivalences` tests `Enhanced.IsWeakHomotopyEquivalence` on every
  mapping set. This is exactly the node's definition of a trivial Kan fibration.
  Mathlib `MorphismProperty.llp` is `HasLiftingProperty` against every such map;
  it supplies fillers of all commutative squares making both triangles commute.
- The fixed-object model structure is the recorded prerequisite
  `Bergner.simplicial_interval_lifting`; the statement uses its independently
  defined cofibration class and does not assume a new model structure.
- There is no quasicategory, local Kan, nonempty, finite-dimensional, or
  dimension-zero horn hypothesis.

Dependency declarations read and used:

1. `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
   `SSet.Enhanced.IsWeakHomotopyEquivalence`, used through the fixed-object
   weak-equivalence class. Its full definition is bijectivity on realized path
   components and every positive based homotopy group.
2. `Sheaf.AlgebraicTopology.PinchedCubeLatching`:
   `SSet.PinchedCube.coherentSimplex`, `rigidification`, `coherentSimplexUnit`.
   Read their complete definitions/docstrings and `pinched_cube_latching`.
   The coherent simplex uses Mathlib's subset-poset `SimplicialThickening`;
   the realization is its actual simplex-colimit left Kan extension.
3. `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
   `SSet.Bergner.Fixed`, `FixedHom`, `fixedCategory`, `bundle`, `bundleMap`,
   `fixedFibrations`, `fixedWeakEquivalences`, `fixedCofibrations`, and
   `simplicial_interval_lifting`. Read the full definitions and the full theorem
   signature. `bundle` uses the common `CategoryTheory.CoherentNerve.SCat`.

Edge cases checked before writing: empty `K` has empty `L` by vertex bijectivity
(every positive simplex has a vertex); the fixed category on the empty object set
and its unique arrow remain allowed. Identity maps and arbitrary vertex
permutations are covered. For a one-simplex boundary extension, the new mapping
space is the zero-cube with empty boundary, so no false nonempty-boundary condition
appears. Repeated endpoint labels and loops are allowed: `Fixed` uses all ordered
pairs, including equal endpoints. Infinite simplicial sets are allowed at arbitrary
universe `u`. No fibrancy of the two simplicial sets or their realizations is used.

Source read: Lurie, Higher Topos Theory, proof of Theorem 2.2.5.1, first paragraph,
printed p.90 / PDF p.107, and its Appendix A.3.2 reference:
https://people.math.harvard.edu/~lurie/papers/HTT.pdf . The source checks positive
boundary extensions by the boundary of the `(n-1)`-cube; the theorem docstring
expands this into the fixed-object relative-cell lifting argument. The node's
`proof` (five steps) and `proof_deps` remain unchanged; no downstream comparison
or Joyal model-structure theorem is invoked.

Searches for an existing declaration (2026-10-17):

- `msearch.py ... leanfinder` query: "Coherent realization of a monomorphism
  bijective on vertices is a cofibration of simplicial categories with fixed
  objects". Eight hits, all SSet cofibration/model-category declarations; none
  states the coherent-realization assertion.
- `msearch.py ... loogle` query: `"SSet", "cofibration"`. Seven hits about
  cofibrations inside SSet, not fixed-object simplicial categories.
- `msearch.py ... leansearch` query: "Coherent realization carries inclusions
  bijective on vertices to fixed object simplicial category cofibrations".
  Eight hits, including SSet cofibrations, fibrations and cofibrant objects;
  no realization theorem.
- `msearch.py ... grep` query:
  `rigidification|coherent.*cofibration|fixedCofibrations`: zero Mathlib hits.
- `rg` with `rigidification|fixedCofibrations|fixed.vertex|coherent.*cofibration`
  over the upstream WeilConjectures and project `lean/Sheaf` found the recorded
  constructions and uses, not the requested theorem. Upstream rigidification
  hits concern Artin-Schreier sheaves, unrelated to this notion. A search for the
  exact node id in upstream sources returned no match.
- Read Mathlib `AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean`:
  `cofibration_of_mono` concerns SSet itself, so cannot replace this theorem.
  Read `CategoryTheory/Enriched/EnrichedCat.lean` and the thickening object
  constructor to verify the labelled-isomorphism types. Searched the proposed
  declaration name in Mathlib, upstream and `lean/Sheaf`: no match.

Validation: the prescribed `scompile.py NN
lem-coef-coherent-fixed-vertex-cofibrations <file>` compiled both its sandbox and
library paths cleanly (1.2s and 1.3s), with no errors or non-sorry warnings.
No new nodes, dependency repairs, statement correction, or disputed statement.

## Second reading by NN

I opened the node `lem-coef-coherent-fixed-vertex-cofibrations`, its source place
(Lurie, HTT, proof of Theorem 2.2.5.1, printed p. 90 / PDF p. 107), and the module
`Sheaf/AlgebraicTopology/CoherentFixedVertexCofibrations.lean`.

The node's objects and hypotheses render in Lean as follows. Small simplicial sets
and the map are `{K L : SSet.{u}}` and `f : K ⟶ L`; degreewise injectivity is
`hinj : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (f.app n)`; and the vertex
bijection is `hvertices : Function.Bijective (f.app (Opposite.op ⦋0⦌))`. The
fixed vertex set is `K _⦋0⦌`, and the fixed-object categories are
`A B : Bergner.Fixed (K _⦋0⦌)`, with object-preserving map `g : A ⟶ B`.
The coherent realization is the recorded `rigidification`, and its vertex maps
are the recorded `coherentSimplexUnit` followed by `rigidification.map` and
`yonedaEquiv.symm`. The two displayed universal equations in Lean identify
`eK.hom.obj x` with the canonical vertex of `K` and `eL.hom.obj x` with the
canonical vertex of `L` labelled by `f.app _ x`; this is exactly the node's
identification of `L_0` with `K_0` through the inverse vertex bijection. The
commuting equation
`Bergner.bundleMap g ≫ eL.hom = eK.hom ≫ rigidification.map f` identifies the
fixed-object map with the induced realization map. Finally,
`Bergner.fixedCofibrations (K _⦋0⦌) g` is the recorded LLP against mappingwise
trivial Kan fibrations. Its dependencies expand triviality to Kan horn lifting
for every `n ≥ 1` and weak homotopy equivalence, and the LLP definition supplies
the diagonal satisfying both triangles. No extra hypothesis occurs in the Lean
signature, and the conclusion has no omitted clause.

The explicit `A`, `B`, `eK`, and `eL` witnesses are representation data forced by
the colimit implementation of `rigidification`: its object carrier need not be
definitionally `K _⦋0⦌`. The object equations and commuting square make this
data precisely the node's fixed-object interpretation, rather than a different
cofibration assertion. The Lean conclusion therefore matches the node without a
statement correction.

Edge cases checked: the empty simplicial set (then vertex bijectivity forces both
vertex sets empty), the empty fixed-object category, zero-dimensional attachments
(the node's `n = 1` cube is `∅ ⟶ Δ^0`), identity maps, arbitrary permutations of
vertices, repeated endpoints and loops, arbitrary universe `u`, and the absence
of any Kan, quasicategory, finiteness, or characteristic assumption. All are
covered by the binders and the dependency definitions.

I repeated the existing-declaration searches with `msearch.py`: LeanFinder query
“fixed-object cofibration of coherent rigidification for a vertex-bijective
monomorphism”, Loogle query `fixedCofibrations`, and grep queries
`coherent_fixed_vertex_cofibrations|rigidification|fixedCofibrations` over Mathlib,
the upstream source, and `lean/Sheaf`. The results were only the recorded
coherent-realization/fixed-object constructions and generic simplicial-set
cofibration declarations; no declaration states this theorem. The dependency
modules and signatures were read in full. No new definition node, dependency
repair, duplicate notion, or mismatch was found, so no file or node change was
needed. `scompile.py` compiled the module with no errors or non-sorry warnings.

## Reviewer fix (maintainer review, 2026-10-17)

The statement, its signature and the `lean` record are unchanged. The theorem docstring
now carries the node's proof step by step (delivery-errors H8), citing all four
`proof_deps` (`lem-coef-infinity-monomorphism-boundary-cells`,
`lem-coef-pinched-cube-latching`, `lem-coef-rigidification-boundary-cube`,
`lem-coef-kan-quillen-model-right-proper-core`). Before the fix it gave only a summary
without three of them. In this report, two garbled source references now read
"Theorem 2.2.5.1", and the false sentence saying the node's `proof` is empty now
says that it is unchanged.
