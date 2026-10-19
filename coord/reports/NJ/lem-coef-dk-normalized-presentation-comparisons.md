## Worker report

The module `Sheaf.CategoryTheory.NormalizedPresentationComparisons` states
`lem-coef-dk-normalized-presentation-comparisons`, with no changes to the natural-language
node, its dependencies, its proof or its reviewed stage-1 fields. Both theorem proofs
are `sorry`. The sole helper definition, `normalizedInversePrecomposition`, is the
actual enriched composition map `lift (SSet.const f) (𝟙 _) ≫ eComp SSet x y x`.
It has real data and is not selected from an existence theorem.

Hypothesis and clause correspondence:

1. The simplicial categories are `A B : SCat.{u}` from the recorded coherent-nerve
   infrastructure. This is the existing `EnrichedCat` on small object types and
   mapping simplices in a common sufficiently large universe. The enriched functor
   is `V : A ⟶ B`; this Hom is exactly `EnrichedFunctor SSet A B`.
2. Local Kan fibrancy is `_hA : IsLocallyKan A` and `_hB : IsLocallyKan B`, whose
   definition is `∀ x y, SSet.KanComplex (hom A x y)` (and likewise for B).
   Local weak equivalence is `_hV : ∀ x y, IsWeakHomotopyEquivalence (V.map x y)`.
   This is the dependency's realization-based weak equivalence, not a substitute
   model-category class or merely a bijection of vertex sets.
3. The first conjunct quantifies over exactly `x y : A` and the fixed vertex
   `b : (hom B (V.obj x) (V.obj y)) _⦋0⦌`. Its conclusion explicitly states BOTH
   `SSet.KanComplex (homotopyFiber (V.map x y) b)` and
   `IsContractible (homotopyFiber (V.map x y) b)`. The second is the existing weak
   contractibility predicate, including the bijection on path components.
4. The displayed normalized comparison space is the existing `homotopyFiber`.
   Unfolding that definition gives `comma ... true` and `commaSubcomplex`:
   its degree-n points are pairs `(a, γ)` in the product of the source mapping
   complex and the internal path object, with initial endpoint `V(a)` and final
   endpoint the constant simplex at b. Thus `.1.1` is the source map simplex and
   `.1.2` is the ENTIRE parameterized path. Neither normalization equation is
   discarded, including in dimensions above zero. This also renders the node's
   sentence describing its points, without an extra noncanonical fibre model.
5. The second conjunct fixes `x y z`, b, and b'. It gives a simplicial map `c`
   from the product of the two normalized comparison spaces to the normalized
   space over `(eComp ...).app _ (b,b')`, exactly b'b. The first coordinate
   equation is enriched composition `(eComp SSet x y z).app _ (p.1.1,q.1.1)`.
   The second equation specifies the path at EVERY degree n and EVERY test
   degree m, restriction α, and interval simplex t. Its value is target enriched
   composition of `p.1.2.app m α t` and `q.1.2.app m α t`.
   This completely characterizes c on both coordinates, rather than supplying
   an unconstrained map or only a composition of vertices.
6. The higher/relative-compatibility sentence is rendered by c being a simplicial
   map, with the same coordinate equations in every degree. Its naturality
   preserves all faces, degeneracies and specified relative restrictions. The
   target is the same normalized homotopy fibre of clause 3, with its explicit
   Kan and contractibility assertions, so higher comparisons have not been
   replaced by equality of components or an unnormalized space.
7. The third conjunct assumes b has a reverse vertex g and edges H,K with
   source/target equations `δ 1 H = gb`, `δ 0 H = 1`, `δ 1 K = bg`,
   `δ 0 K = 1`. This is enriched invertibility up to homotopy. In a Kan mapping
   complex the orientation makes no restriction: edges can be reversed and
   concatenated. For EVERY point p of the normalized fibre, the conclusion
   supplies a reverse vertex and both source inverse homotopies for `p.1.1`.
   It does not assume essential surjectivity of V or strict inverses.
8. `normalized_inverse_comparisons` quantifies over a locally Kan A, x,y and
   the fixed enriched vertex f. Its `_hf` is exactly the existence of a reverse
   vertex and two inverse edges, with the four endpoint equations as above.
   `normalizedInversePrecomposition A f` has domain `hom A y x`, codomain
   `hom A x x`, and value `h ∘ f`. The fibre is taken over the actual identity
   vertex `(eId SSet x).app _ PUnit.unit`. Its contractibility is the first
   conclusion. A point p contains h and its specified homotopy hf to the identity
   by the unchanged fibre definition. The second conclusion gives, for every
   such p, an edge K from `(eComp SSet y x y).app _ (p.1.1,f)` = fh to `1_y`.
   The original first inverse homotopy is retained in p, not replaced by a
   freshly existentially chosen first homotopy.
9. No assertion about contractibility of all unnormalized equivalences occurs.

Dependencies read and used:

- `def-cbc-enhanced-diagrams-cones`: public import
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`; declarations `SSet.Enhanced.homotopyFiber`,
  `comma`, `commaSubcomplex`, `evaluation`, `IsWeakHomotopyEquivalence`, `IsContractible`.
  Read their full source and the node's complete conventions.
- `def-coef-coherent-nerve-infrastructure`: public import
  `Sheaf.CategoryTheory.CoherentNerveInfrastructure`; declarations
  `CategoryTheory.CoherentNerve.SCat`, `sCatCategory`, `hom`, `IsLocallyKan`.
  Read the complete module and its enriched functor Hom definition.
- Proof imports are the recorded modules
  `Sheaf.AlgebraicTopology.ContractibleHomotopyFiberEquivalence`,
  `Sheaf.AlgebraicTopology.PathFibrationReplacement`, and
  `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak`. Read their node
  statements and theorem signatures/docstrings. The two theorem docstrings
  spell out all four proof steps of the item, including the separate Kan-fibre
  argument and the two simplicial homotopies for precomposition by f.
- Mathlib supplies `eComp`, `eId`, the Cartesian `lift`, `SSet.const`, and the
  internal-hom representation. Read `CategoryTheory/Enriched/Basic.lean`,
  `AlgebraicTopology/SimplicialCategory/Basic.lean`,
  `CategoryTheory/Functor/FunctorHom.lean`, and the functor-to-types closed structure.

Edge cases checked before writing:

- For V the identity, the normalized fibre is the contractible space of paths
  ending at b, not all vertices of the mapping space.
- For discrete mapping complexes, a local weak equivalence is a bijection;
  the normalized fibre has its unique inverse-image vertex and constant path.
- Empty object sets are allowed. If a source mapping complex is empty and a
  local weak equivalence exists, the target mapping complex is empty as well;
  thus no b exists and the quantified assertion is vacuous as intended.
- For a one-object category coming from a discrete nontrivial group, the
  unnormalized set of equivalences need not be contractible, whereas each
  normalized comparison and normalized inverse fibre is a singleton. The
  statement correctly distinguishes these cases.
- Identity f, equal objects x=y, constant comparison paths and degenerate
  simplices obey the same formulas. There is no nonemptiness assumption on
  object types, mapping complexes or index types.
- Enriched composition is ordered `(f,g) ↦ g ∘ f`. The helper therefore uses
  `(f,h)`, whereas the second inverse edge uses `(h,f)` in `eComp y x y`.
- Universes and variables are explicit; the module sets `autoImplicit false`.

Searches made:

- `msearch.py leanfinder`: “A locally weak equivalence of Kan enriched categories
  has contractible normalized homotopy fibres and reflects homotopy equivalences”.
  Eight hits on bifibrant weak equivalences, homotopy relations and localization;
  none states the normalized enriched comparison or its inverse-data clause.
- `msearch.py leansearch`: “normalized homotopy fibre of a weak equivalence of
  Kan complexes”. Eight model-category hits, including `mem_trivialFibrations`
  and Brown factorizations; none states this lemma.
- `msearch.py loogle`: `CategoryTheory.EnrichedCategory.eComp, SSet.KanComplex`.
  Zero hits; unknown identifier for the first name (the actual operation is
  `CategoryTheory.eComp`, as verified directly in Mathlib source).
- `msearch.py grep`: `homotopy[Ff]iber|normalized.*comparison|homotopy.*[Ee]quivalence`
  in Mathlib/AlgebraicTopology. Twenty-five displayed hits on model homotopies,
  quasicategory truncations and homotopy groups; no normalized-fibre statement.
- Direct `rg` of Mathlib, upstream `WeilConjectures/`, and `lean/Sheaf/` found no
  declaration named `normalizedInversePrecomposition`,
  `normalized_presentation_comparisons`, or `normalized_inverse_comparisons`.
  Searching upstream for the item id found no match.
- Direct searches for the enriched inverse notion found the existing
  `CategoryTheory.IsPiZeroIso` in `Sheaf.CategoryTheory.CoherentNerveComparison`.
  This is a condition on an underlying ordinary arrow, using equality of
  components. Importing its owning DAG node as a new statement dependency would
  close the path coherent-nerve-comparison → model-colimit-localization-comparison
  → small-diagram-model-rectification → coherent-diagram-coyoneda
  → right-fibration-section-limit → THIS ITEM. No such dependency was added.
  Instead the theorem spells out the source's two inverse edges directly,
  without introducing a competing named predicate or an instance choice.
- The existing strict `SimplicialGroupoid` inverse data were also read; strict
  degreewise inverses are a different, stronger notion and are not used.

Source check: opened the cited HTT PDF at
https://www.math.ias.edu/~lurie/papers/HTT.pdf and located Proposition the project server.
It concerns the unstraightening equivalence of simplicial categories. As the node
already explicitly records, the normalized homotopy-fibre assertion is the
agent-formulated argument extracted from returned Step 4, not a verbatim HTT
proposition. No source or node correction is needed.

No new nodes or dependency repairs are introduced. No `STATEMENT-DISPUTED` fault.

Validation: `scompile.py NJ lem-coef-dk-normalized-presentation-comparisons`
compiled the delivered module successfully with exit code 0 and no diagnostics,
using the standard per-file limit. Both the sandbox and library-path checks passed.
`deliver2.py NJ lem-coef-dk-normalized-presentation-comparisons --no-push`
reported OK: the delivery passes preflight and compiles. The earlier dispatch
reported a split/review preflight rejection; this reconstructed lean-only delivery
passes without altering those stage-1 fields.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
