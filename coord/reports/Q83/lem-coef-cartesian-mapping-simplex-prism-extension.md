## Worker report

The new module `Sheaf.AlgebraicTopology.CartesianMappingSimplexPrismExtension` states
`SSet.Marked.cartesian_mapping_simplex_prism_extension`, with its sole proof `sorry`.
There are no new definitions, dependency repairs, or changes to the natural statement.

Source checked: Lurie, *Higher Topos Theory*, Proposition the project server, proof, printed
pp. 184–185, especially the final-vertex factorization and dotted arrow f₀; also
Proposition the project server. The IAS URL timed out. The official Harvard PDF
https://people.math.harvard.edu/~lurie/papers/HTT.pdf was downloaded and the relevant
passage read. It has exactly the prescribed factorization, the marked pushout-product
inclusion, extension over the simplex, and endpoint equality. The apparent `Sv` in
its factorization display refers to the final fiber denoted `Xv` in the preceding line.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- All simplicial sets are `SSet.{u}`, with an explicit arbitrary universe `u`.
  `n : ℕ` includes n = 0; `Δ[n]` is Mathlib's representable standard simplex.
- `p : Y ⟶ Δ[n]` and `hp : Over.relativeFibration false p` give the Cartesian
  fibration in the arbitrary-base horn convention exported by the recorded relative
  marked-anodyne dependency. No additional quasicategory or fibrancy assumptions occur.
- The final vertex is `stdSimplex.obj₀Equiv.symm (Fin.last n)`.
  `Enhanced.fiber p` at this vertex is the existing strict pullback of p along
  `SSet.const (X := Δ[0])` of that vertex. Thus the codomain of h is exactly Yₙ.
- `s : product (flat A) (sharp Δ[n]) ⟶ cartesianNatural p` is precisely the marked
  map in the node. The existing natural marking includes Cartesian edges and
  degeneracies; the relative dependency identifies these with exactly Cartesian edges
  under hp. `hs : s.val ≫ p = snd A Δ[n]` is the over-the-simplex condition.
- `j : A ⟶ Aₙ` and `[Mono j]` are exactly the monomorphism in the factorization.
  For simplicial sets monomorphisms are degreewise injective.
- `h : Aₙ ⟶ Enhanced.fiber p (...)` and `hh : modelCategoryQuillen.I.rlp h` express
  the trivial Kan fibration. I is the family of all boundary inclusions, including
  the empty boundary in dimension zero, and the recorded Kan–Quillen theorem
  identifies its right orthogonal with the trivial fibrations. The hypothesis on h
  is retained although the extension argument itself only uses j's monicity.
- `hfac` says `j ≫ h ≫ pullback.snd ... p` equals the final-endpoint restriction
  of s. The latter uses `lift (𝟙 A) (SSet.const finalVertex)` into the product.
  This is exactly factorization of the induced final-fiber map: s is over the
  simplex, so its endpoint restriction factors uniquely through the displayed
  strict pullback. The map from the point Δ[0] is monic, so `pullback.snd` is
  monic and equality after that inclusion is equivalent to equality in Yₙ.
  Thus the statement neither chooses an arbitrary fiber map nor drops compatibility.
- The existential s' is a marked map `product (flat Aₙ) (sharp Δ[n]) ⟶ cartesianNatural p`.
  Its first conjunct `s'.val ≫ p = snd Aₙ Δ[n]` says it is over the simplex.
- Its second conjunct `productMap (flatMap j) (𝟙 (sharp Δ[n])) ≫ s' = s` is the
  required restriction along j times the identity, as a strict equality of marked maps.
- Its third conjunct restricts s' using `lift (𝟙 Aₙ) (SSet.const finalVertex)` and
  equates it to h followed by the canonical `pullback.snd` inclusion. Both sides
  already lie over the final vertex, so this is exactly the required equality
  with h on Aₙ times that vertex, equivalently in the strict fiber. These are
  strict simplicial-map equalities, not equivalences or unspecified homotopies.

Recorded dependency interfaces read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: Mathlib `SSet`, `stdSimplex`, and
  the degreewise Cartesian monoidal product imported there. Its module docstring
  explicitly binds these Mathlib primitives to `def-cbc-enhanced-diagrams-cones`.
- `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus`:
  `SSet.Marked.cartesianNatural`, `SSet.Marked.cartesianNaturalOver`, and
  `SSet.Marked.Over.relative_marked_anodyne_calculus`, with the existing
  `Over.relativeFibration` from `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`.
  `Enhanced.fiber` comes from the imported `Sheaf.CategoryTheory.InfinityFibrations`.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`:
  `SSet.Marked.marked_anodyne_lifting_calculus`; the imported existing
  `SSet.Marked.flat`, `sharp`, `product`, `productMap`, `flatMap` from
  `MarkedPointCartesianModel` supply the actual markings and maps.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`, specifically the exact
  trivial-fibration characterization `trivialFibrations SSet = modelCategoryQuillen.I.rlp`.
- Proof-only imports `Sheaf.AlgebraicTopology.MarkedSimplexSpineExtension` and
  `Sheaf.AlgebraicTopology.MarkedCoanodyne` supply
  `SSet.Marked.marked_simplex_spine_extension` and `SSet.Marked.markedCoanodyne`.
  The theorem docstring records all four DAG proof steps and the endpoint reversal.

Edge cases checked before writing: n = 0 makes the endpoint restriction the entire
prism and forces s' to be h followed by its fiber inclusion. The unique vertex is
still `Fin.last 0`. For n = 1 the final vertex is 1, with Cartesian, not coCartesian,
orientation. Empty A is allowed; an empty Aₙ forces A empty by the existence of j.
An empty Yₙ forces Aₙ empty when h exists, without an added nonemptiness premise.
For nonempty Yₙ, the dimension-zero boundary lifting requirement prevents an empty
Aₙ from satisfying hh. Identity j and arbitrary large input universe u are covered.
No hypothesis or endpoint has been silently removed.

Searches actually run:

- `msearch.py`, LeanFinder: "A marked map into a Cartesian fibration over a simplex
  extends from a subcomplex and the final fiber": 8 hits, including
  `SSet.RelativeMorphism.ofSimplex₀`, `SSet.Subcomplex.lift`, and
  `SSet.RelativeMorphism.const`. These concern ordinary simplicial restrictions,
  not extension of a marked Cartesian prism with a prescribed final fiber.
- `msearch.py`, Loogle: `"SSet", "stdSimplex"`: 12 hits for standard simplices,
  their faces and instances; no marked extension theorem.
- `msearch.py`, Mathlib grep in AlgebraicTopology:
  `marked.?anodyne|MarkedAnodyne|CartesianFibration`: 0 hits.
- `rg` in the source `WeilConjectures` for prism/Prism/Marked and Cartesian-simplex
  patterns, and `grep -rn` for this exact node id: no exact theorem found.
- `rg` in project `lean/Sheaf` for prism/Prism, fiber/vertex interfaces,
  `PrismExtension|prism_extension`, and `cartesian_mapping_simplex_prism_extension`:
  existing invertible/equivalence prism theorems and other Cartesian-simplex lemmas
  have different hypotheses/conclusions. None states this prescribed final-fiber
  extension. Existing `Enhanced.fiber` and marked products were reused directly;
  no helper notion or new definition node is necessary.
- Read Mathlib `SimplicialSet/Basic.lean` constant maps, `StdSimplex.lean`
  constant simplices and `obj₀Equiv`, `Monoidal.lean` endpoint inclusions,
  `CategoryWithFibrations.lean` boundary/horn classes, and the Cartesian-monoidal
  `lift` interface to confirm that the explicit restrictions use existing maps.

Validation: the single delivered module is compiled through `scompile.py`; the
required dry run and delivery are performed through `deliver2.py`. No project
source or compiled library was edited, and no global build was run.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
