## Worker report

The module `Sheaf.CategoryTheory.FibrantPatternHomotopyInverse` states
`SSet.Enhanced.CategoricalPattern.fibrant_pattern_homotopy_inverse`, with `sorry`
as its entire proof. It introduces no definitions, no assumptions on a chosen
model-structure witness, no new nodes, and no dependency repairs. The node is
unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- Fixed but arbitrary small universe: the explicit `universe u`,
  `P : CategoricalPattern.{u}`, and `F G : Object P` keep all simplicial sets in
  the same universe. `CategoricalPattern` already packages the small base
  quasicategory, its marking containing degeneracies, full scaling, the small
  cone family, quasicategory cone shapes and marked cone maps.
- The specified map between marked objects over `(B,S)` is `f : F ⟶ G`.
  The published `CategoricalPattern.Hom` contains exactly an underlying
  simplicial map, the equation commuting with the structure maps, and marking
  preservation.
- Both objects are P-fibered: `hF : IsCategoricalPatternFibered P F` and
  `hG : IsCategoricalPatternFibered P G`. The predicate is used verbatim,
  including both cone conditions and their empty-shape cases.
- Weak equivalence in the pattern model structure is `weak f`. This is the
  published predicate, identified with the model's weak-equivalence field by
  `ModelStatement.weak_equivalences`; no particular model is selected.
- The first displayed equivalence is the first conjunct `weak f ↔ ∃ g H J, ...`.
  The inverse is `g : G ⟶ F`, again a marked map over the same base.
- The H and J binders have domains
  `(tensor (SSet.Marked.sharp (Δ[1] : SSet.{u}))).obj F` and its G analogue.
  The published tensor is precisely the marked product with structure map
  obtained by projection to F or G. Their codomains are F and G. Because these
  binders are morphisms in `Object P`, both homotopies preserve markings and
  commute with the base map.
- `H|₀ = gf` is `SSet.ι₀ ≫ H.map = (f ≫ g).map`.
  `H|₁ = id_F` is `SSet.ι₁ ≫ H.map = 𝟙 F.underlying.underlying`.
  `J|₀ = fg` is `SSet.ι₀ ≫ J.map = (g ≫ f).map`.
  `J|₁ = id_G` is `SSet.ι₁ ≫ J.map = 𝟙 G.underlying.underlying`.
  Lean categorical composition is left-to-right, accounting for f then g.
  `SSet.ι₀` and `SSet.ι₁` insert the literal constant zero and one vertices.
  Their underlying product is definitionally that of the published marked
  tensor. Equality on underlying maps is equality of the slice morphisms:
  the other fields are proofs, and those endpoints preserve the marking
  because the interval is sharp. No unmarked homotopy has been substituted.
- The final sentence's equivalence is the second conjunct. Its left side
  repeats exactly the same inverse/homotopy existential; its right side is
  `∀ Z : Object P, IsCategoricalPatternFibered P Z →
  IsWeakHomotopyEquivalence (mapSharpPre f Z)`.
- The stated mapping-complex formula is the already recorded `mapSharp`:
  `Marked.Over.mapSharp (expand T) (expand Z)` has n-simplices the actual
  marked maps from T times the sharp n-simplex over the base. `mapSharpPre`
  is actual precomposition by f, with direction G-to-F on mapping spaces.
  `expand` changes only the codomain marking to sharp: every map to a fixed
  object Z over that base still preserves its original domain and Z markings,
  so its Hom set is the original marked slice Hom set.
- No finiteness condition is present: `P.index : Type u` and the simplicial
  cone shapes of the recorded pattern are unrestricted. There is no `Finite`,
  `Fintype`, bound on dimension, or nonemptiness hypothesis.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CategoricalPatternFibrancy`:
  `SSet.Enhanced.CategoricalPattern`, `.Object`, `.Hom`, and
  `SSet.Enhanced.IsCategoricalPatternFibered`.
- `Sheaf.CategoryTheory.CategoricalPatternModelCalculus`:
  `SSet.Enhanced.CategoricalPattern.tensor`, `productLeft`, `expand`,
  `expandMap`, `mapSharp`, `mapSharpPre`, `weak`, `ModelStatement`, and
  `categorical_pattern_model_calculus`. The model witness is never chosen.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked.sharp`, `product`, and `marked_point_cartesian_model`.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen` and its realization-based weak
  equivalence convention `SSet.Enhanced.IsWeakHomotopyEquivalence`, whose
  definition in `EnhancedDiagramsCones` was read.
- Proof-only imports: `Mathlib.AlgebraicTopology.ModelCategory.Homotopy`
  provides both Mathlib matches of `lem-coef-model-cylinder-whitehead`,
  `HomotopicalAlgebra.RightHomotopyClass.whitehead` and
  `HomotopicalAlgebra.RightHomotopyRel.leftHomotopy`. I read both full
  signatures and the latter's prescribed-good-cylinder docstring.
  `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak` provides
  `SSet.Enhanced.simplicial_homotopy_equivalence_weak`; its actual simplex
  homotopies, endpoint order alternatives, and absence of Kan/nonempty
  hypotheses were checked. All stated proof dependencies are imported.

Edge cases checked before writing: empty pattern family and empty cone shapes
remain covered by the original fibrancy predicate; an empty limit is not
silently dropped. The base and objects may be empty. Inverse data include
both maps, so if one total simplicial set is empty the other must also be
empty; the mapping test and realization-based component/basepoint conditions
remain meaningful. Identities have the constant product-projection homotopies.
The endpoint formula uses the whole simplicial product, not just vertices.
There is no smallness restriction beyond the arbitrary fixed universe.

Searches for an existing exact declaration:

- `msearch.py`, LeanFinder: "Fibrant marked categorical pattern objects are
  weakly equivalent exactly when they have sharp interval homotopy inverses".
  Eight hits include generic Whitehead, homotopy-class, and bifibrant-object
  results. None states the marked-pattern sharp-cylinder criterion.
- `msearch.py`, LeanSearch: "A weak equivalence between fibrant marked
  categorical pattern objects has a sharp interval homotopy inverse".
  Eight generic model-category hits, including `RightHomotopyClass.whitehead`
  and `Cylinder.LeftHomotopy.weakEquivalence_iff`; no exact pattern result.
- `msearch.py`, Loogle: `"whitehead"`. The two generic left/right homotopy-class
  Whitehead theorems were returned. The right-homotopy theorem and its transport
  to a specified good cylinder are the existing proof leaf, not this node's
  marked cylinder construction and mapping-space equivalence.
- `msearch.py`, Mathlib grep:
  `categorical.?pattern|MarkedSSet|marked.*homotopy|homotopy.*marked`: zero hits.
- `rg` of upstream `WeilConjectures` for
  `fibrant_pattern_homotopy_inverse|sharp.*[Hh]omotopy|[Hh]omotopy.*sharp|categorical.?pattern`
  and `grep -rn` of the node id: zero hits. The proposed name was also searched
  in `dag/lean_names_upstream.json`, without a collision.
- `rg` of `lean/Sheaf` found the published model definitions and proof-docstring
  discussions, plus relative-cartesian specializations; no general categorical
  pattern homotopy-inverse declaration. The published dependencies are reused.

Source check: I opened Higher Algebra (2017), printed p.1483, Lemma B.2.4,
conditions (1) and (2), and Definition B.2.1 and Proposition B.1.14 immediately
before it. The source has marked homotopies connecting the two composites to
identities, and no finiteness hypothesis on the cone shapes. Product-factor
order differs only by the cartesian symmetry; the node fixes the A-times-interval
order used here. The theorem docstring contains all five DAG proof steps,
including the explicit formula for the induced mapping-space homotopy.

No statement correction or STATEMENT-DISPUTED issue was needed.

Validation: the delivered module is checked individually through `scompile.py`;
the delivery dry-run and server preflight are run before pushing. No project
build or direct writes to the shared source checkout were used.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
