## Worker report

Module: `lean/Sheaf/AlgebraicTopology/ExInfinityFiniteProducts.lean`.
Main statement: `SSet.ex_infinity_finite_products`, with its whole proof `sorry`.
All ten helper definitions have actual data and verified structure fields. No other
DAG node is stated. No statement correction or dependency repair is needed.

Source read: https://kerodon.net/tag/00ZA, Construction the project server and Propositions
the project server, the project server, the project server; https://kerodon.net/tag/00YU, Construction the project server.
The source explicitly iterates Ex with the last-vertex comparison as transition.
The nine steps of the node's proof are carried in the theorem docstring, with
all named inputs. The three non-Mathlib proof inputs (face-poset calculus,
one-step comparison, filtered-colimit weak equivalences) have no recorded Lean
statement yet and therefore have no proof import. The already stated
Kan–Quillen input and the filtered-colimit/finite-limit Mathlib leaf are imported
privately for the future proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A simplicial set is exactly Mathlib `SSet.{u}`. There are no Kan, nonempty,
  connectivity or finiteness assumptions on `K`; `u` is arbitrary.
- The subdivided standard simplex is Mathlib `SimplexCategory.sd.{u}.obj n`:
  the nerve of `PartialOrder.NonemptyFiniteChains` of the lifted finite ordinal.
  Since that ordinal is linearly ordered, every nonempty finite subset is a chain.
  Mathlib maps a subset by direct image under the monotone map, as required.
- The Ex functor is the existing `SSet.ex.{u}`, whose degree-n simplices are
  `ULift` of maps from that subdivided simplex. This outer `ULift.{0}` is a
  harmless encoding of exactly the node's Hom set, without a size restriction.
- `sdLastVertexOrderHom` takes `S.finset.max' S.nonempty`.
  `sdLastVertex` sends a flag to the monotone sequence of these maxima.
  `sdLastVertexCosimplicial` records its naturality for all monotone ordinal maps.
  `exLastVertexUnit.app K` sends `x` to last-vertex precomposition with the simplex
  map `yonedaEquiv.symm x`. Thus this is the specified `j_K : K → Ex K`.
- `exIter 0` is the identity and `exIter (n+1)` is `exIter n ⋙ SSet.ex`.
  `exIterTransition n` is `Functor.whiskerLeft (exIter n) exLastVertexUnit`:
  its component is `j` at the n-th stage, precisely the prescribed transition.
- `exTowerFunctor` uses `Functor.ofSequence` on those transitions in the
  endofunctor category. `exInfinityFunctor` is its chosen `colimit`.
  Functor-category colimits are computed pointwise; evaluating this colimit is
  canonically the sequential colimit in the node. `exInfinity K` is that value.
  `exInfinityUnit` is the actual stage-zero `colimit.ι`, a natural transformation.
- `∀ K, KanComplex (exInfinity K)` is the Kan assertion for every simplicial set.
- `Enhanced.IsWeakHomotopyEquivalence (exInfinityUnit.app K)` is the assertion
  about the natural stage-zero map, using the recorded realization-based notion.
- `PreservesFiniteLimits exInfinityFunctor.{u}` includes every finite diagram,
  hence empty diagrams and finite products, equalizers and pullbacks.
- For every `I : Type v` with `[Finite I]`, and every `K : I → SSet.{u}`,
  `IsIso (piComparison exInfinityFunctor K)` asserts that the actual canonical
  comparison to the product of the images is an isomorphism. The universe `v`
  is independent of `u`; no finite index set is excluded.
- The next clause says that composing this comparison with `Pi.π` gives
  `exInfinityFunctor.map (Pi.π K i)`. The following clause says that first
  applying `exInfinityUnit` to the product, then the comparison and projection,
  equals the original projection followed by the unit of the corresponding
  factor. These are exactly the two requested projection compatibilities.
- `IsIso (terminalComparison exInfinityFunctor.{u})` names the actual terminal
  comparison, hence includes the empty product explicitly.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set`: Mathlib
  `AlgebraicTopology.SimplicialSet.Basic`, `SSet` (functors from the opposite
  simplex category to types). The additionally recorded `degenerate`,
  `nonDegenerate`, `Subcomplex`, and `Finite` signatures/docstrings were read
  in their Mathlib files; no replacements are defined.
- `lem-coef-kan-quillen-right-proper`: read
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`, including the full signature
  and proof docstring of `SSet.KanQuillen.right_proper_kan_quillen`.
  Its standard Kan notion is Mathlib `SSet.KanComplex` (all positive-dimensional
  horns, including outer horns); this is publicly imported directly. The model
  theorem is imported privately as a proof input.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit` and `colimit.ι`, publicly imported.
- `def-cbc-enhanced-diagrams-cones`: read
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`; use
  `SSet.Enhanced.IsWeakHomotopyEquivalence`. Its definition requires bijectivity
  on realization path components and every positive based homotopy group, with
  all source basepoints. This is not an arbitrary weak-equivalence predicate.
- Additional existing constructions read: Mathlib
  `AlgebraicTopology.SimplicialSet.Subdivision` (all definitions),
  `Order.NonemptyFiniteChains`, the standard-simplex Yoneda equivalence,
  `CategoryTheory.Functor.OfSequence`, product comparisons, terminal comparison,
  and `Limits.FilteredColimitCommutesFiniteLimit`.

Edge cases checked:

- The empty simplicial set is included: no nonempty positive-dimensional horn
  maps into it, and neither KanComplex nor the statement requires a vertex.
- In degree zero the nonempty subset poset is a singleton, so maximum and its
  last-vertex simplex are defined with no choice of a nonexistent element.
- Noninjective simplex operators are allowed: their images may collapse subsets,
  and the naturality construction uses maximum of their actual nonempty image.
- Stage zero is the identity. The natural-number indexing category is nonempty
  and filtered, and the unit is its stage-zero coprojection.
- The arbitrary finite family includes empty and singleton index types in every
  universe. For an empty index the projection clauses are vacuous, while the
  isomorphism clause and the explicit terminal comparison remain substantive.
- One-dimensional horns and both outer horns are included through Mathlib's
  KanComplex, with no dimension-zero nonemptiness requirement.

Searches actually run (all `msearch.py` calls use group Q24 and this item):

- LeanFinder: `iterated Ex infinity Kan replacement preserves finite limits simplicial sets`.
  Eight hits: truncated simplicial-set limits, skeleton/coskeleton, generic
  simplicial limits, finite presentability and the homotopy-category functor's
  terminal preservation; none states Ex-infinity replacement.
- Loogle: `SSet.ex, KanComplex, PreservesFiniteLimits`.
  Invalid query: the service reported unknown identifier `KanComplex`.
  This is not evidence of absence; it was rerun with the valid query `SSet.ex`.
- Loogle: `SSet.ex`. Three hits: `SSet.ex`, its right-adjoint instance, and
  `SSet.sdExAdjunction`. These supply a single Ex, not its iterated replacement.
- LeanSearch: `Ex infinity functor simplicial sets Kan complex weak equivalence finite limits`.
  Eight hits: KanComplex, generic finite-limit preservation, homotopy-category
  finite products, simplicial finite colimits/presentability/limits, realization,
  and Dold–Kan; no exact theorem.
- Mathlib grep through msearch: `ExInfinity|exInfinity|lastVertex|sdExAdjunction`
  in `AlgebraicTopology`. Only the adjunction and its two adjoint instances.
- Read-only `rg` searches of `WeilConjectures/`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for Ex-infinity and the introduced declaration
  names found no existing definition or statement of this replacement.
  The plain node-id search in the source project also found none.

No new node, duplicate notion, extra hypothesis, or STATEMENT-DISPUTED flag.
The module was checked with the prescribed `scompile.py`, one file at a time,
under the normal 60-second limit; the final file compiled with no warnings or
errors. Definitions prove only their elementary structural laws, with no
postponed proof or chosen arbitrary map. The one mathematical theorem is left
with exactly `sorry` as required for stage 2.

## Second reading by Q24

Independent reading on 2026-10-17. I opened the repository node, the sandbox
module and node record, all four statement-dependency records, the relevant
Mathlib declarations, and the two project dependency modules. No repair note
exists for this item. The source is Kerodon, not Stacks: I read the actual
Section 3.3.6 (https://kerodon.net/tag/00ZA) and Construction the project server
(https://kerodon.net/tag/00YU). Their ambient assumption is an arbitrary
simplicial set, with no Kan, nonemptiness, connectivity or finiteness condition.
The chosen transitions are the comparison at each iterate, as in the node.

Object/hypothesis/conclusion checklist, prepared from the node before checking
the Lean rendering (every verdict below is exact):

1. Objects are arbitrary simplicial sets and simplicial maps. Lean uses
   Mathlib `SSet.{u}` and its natural transformations. I read Basic.lean's
   `SSet := SimplicialObject (Type u)` and the dependency's recorded Mathlib
   match. No additional instance is assumed on a simplicial set.
2. The subdivided standard n-simplex is the nerve of the nonempty subsets of
   `[n]`, ordered by inclusion. Lean uses `SimplexCategory.sd.{u}.obj n`.
   I read Subdivision.lean and NonemptyFiniteChains.lean: on the linearly
   ordered lifted `Fin (n.len + 1)`, the comparability field imposes no extra
   restriction on a subset; the order is finset inclusion. This is the same
   poset, including singleton subsets and the full subset.
3. `Ex K` in degree n is maps from that nerve into K, with operators from
   direct images under monotone maps. Lean uses existing `SSet.ex`, defined
   as `Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd`. Its simplex
   elements are precisely the indicated maps with an outer `ULift.{0}`.
   The latter changes no elements or universe. The subdivision functor on
   ordinals takes actual finset images, including noninjective operators.
4. The last-vertex map sends a subset to its maximum, and induces natural
   `j_K`. `sdLastVertexOrderHom` is `S.finset.max' S.nonempty`;
   `sdLastVertex` applies it along every flag;
   `sdLastVertexCosimplicial` verifies naturality in the ordinal;
   `exLastVertexUnit.app K` sends x to
   `ULift.up (sdLastVertex n.unop ≫ yonedaEquiv.symm x)`.
   This is the source's maximum-precomposition map, with both naturalities
   supplied as actual structure fields, rather than an arbitrary comparison.
5. The sequence starts at K and has transitions `j` at the current iterate.
   `exIter 0` is the identity, and `exIter (n + 1)` is `exIter n ⋙ SSet.ex`.
   `exIterTransition n` is `Functor.whiskerLeft (exIter n) exLastVertexUnit`:
   this is `j_(Ex^n K)`, rather than a differently whiskered unit.
   `exTowerFunctor` is `Functor.ofSequence` on those maps. I read
   OfSequence.lean: its adjacent arrow is the given transition.
6. The replacement is the sequential colimit and its unit is the stage-zero
   map, natural in K. `exInfinityFunctor` is `colimit exTowerFunctor` in the
   endofunctor category, `exInfinity K` is its value, and `exInfinityUnit`
   is `colimit.ι exTowerFunctor 0`. Pointwise functor-category colimits give
   exactly the node's colimit at each K. This uses the recorded category
   colimit notion; there is no choice from an unproved existence assertion.
7. Every replacement is Kan. The first conjunct is
   `∀ K : SSet.{u}, KanComplex (exInfinity K) ∧ ...`.
   I read Mathlib KanComplex.lean: the horn conditions include all positive
   dimensions and both outer horns, without imposing a vertex in dimension
   zero. This is the Kan notion in the recorded Kan--Quillen dependency.
8. The natural map is a weak homotopy equivalence. The same universal
   conjunct states `Enhanced.IsWeakHomotopyEquivalence (exInfinityUnit.app K)`.
   I opened its exact definition in EnhancedDiagramsCones.lean: realization
   induces a bijection on path components and bijections on positive based
   homotopy groups for every source-realization basepoint. The node's notion
   and KanQuillenRightProper.lean use this same definition.
9. The functor preserves finite limits. The second conjunct is
   `PreservesFiniteLimits exInfinityFunctor.{u}`. I read the Mathlib class:
   this is preservation of every finite diagram, with no hypothesis that
   the diagram is nonempty or that its values are finite simplicial sets.
10. For every finite product the canonical comparison is an isomorphism.
    The third conjunct quantifies over `(I : Type v) [Finite I]`
    and `(K : I → SSet.{u})` and states
    `IsIso (piComparison exInfinityFunctor.{u} K)`.
    The comparison is Mathlib's canonical map induced by the original
    projections, not an unspecified isomorphism.
11. The comparisons commute with projections. For each `i : I`, the first
    equation is `piComparison ... K ≫ Pi.π ... i =
    exInfinityFunctor.map (Pi.π K i)`, exactly its required i-th component.
12. The natural unit commutes with product projections and the comparison.
    The next equation is `exInfinityUnit.app (∏ᶜ K) ≫ piComparison ... K ≫
    Pi.π ... i = Pi.π K i ≫ exInfinityUnit.app (K i)`.
    Domain, codomain and composition order agree with the source's
    naturality of the stage-zero inclusion.
13. The empty product is included explicitly: the final conjunct is
    `IsIso (terminalComparison exInfinityFunctor.{u})`.
    This uses the canonical map to the chosen terminal object.

Edge cases: empty and singleton index sets are covered by `[Finite I]`,
with `v` independent of `u`; there is no `Nonempty I` assumption. For an
empty index set the projection equations are vacuous, but the product
comparison and terminal comparison remain asserted. The empty simplicial set
is covered by the universal K binder; its Kan condition does not require a
vertex. At n = 0 the underlying ordinal is `Fin 1`, so the nonempty-subset
maximum is defined and the last-vertex map is the unique zero-simplex map.
Stage zero is the identity, not one application of Ex. Noninjective ordinal
maps correctly collapse subsets by direct image. Both u and v are explicitly
bound; no additional category, smallness, characteristic, ring, scheme or
field assumption occurs. Zero modules, empty schemes and characteristic
restrictions are inapplicable to this simplicial-set statement.

Independent searches (different wording from the worker's first query):

- `msearch.py ... leanfinder 'iterated Ex infinity Kan replacement finite products'`
  returned eight hits: homotopy-category finite products, coskeleton, finite
  simplicial products, Cech nerve and a generic transfinite iteration.
  None is this functor or theorem.
- `msearch.py ... loogle 'SSet.ex'` returned exactly `SSet.ex`, its
  right-adjoint instance and `SSet.sdExAdjunction`. I opened Subdivision.lean:
  it supplies one Ex and its adjunction, with no last-vertex unit or iteration.
- `msearch.py ... leansearch 'Sequential iteration of subdivision right adjoint
  preserves finite limits and gives a Kan weak homotopy equivalence replacement'`
  returned eight generic limit-preservation/adjunction results, no replacement.
- `msearch.py ... grep 'ExInfinity|exInfinity|ex_infinity'` returned no hit.
  Additional `rg` searches in pinned Mathlib AlgebraicTopology, upstream
  WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json for
  lastVertex, sdLastVertex, exInfinity, ex_infinity_finite_products and the
  Ex tower found no existing definition or exact theorem. Broad spelling
  searches also returned unrelated last-vertex and complex-tower text;
  those concern other constructions, not this replacement.

All ten helper definitions belong to the replacement explicitly constructed
by this node; they introduce no independent missing notion and duplicate no
recorded dependency. There are no new nodes or dependency modules to audit.
The project Kan--Quillen theorem and the Mathlib filtered-colimit/finite-limit
input are appropriately private proof imports; the three remaining proof
inputs have no recorded Lean module yet. I checked the nine docstring steps
against all nine node proof steps, including the distinction between
`Sd(lambda_A)` and `lambda_(Sd A)` in the double-adjunction argument.
The module and each declaration have the source/blueprint docstring. The
only mathematical theorem has proof exactly `sorry`; all helper data and
structural naturality fields are implemented. There is no hollow definition,
private notion, local notation or extra theorem. All lines are at most 100
characters, and all variables/universes are bound. The node's lean.statement
is verbatim the theorem signature preceding `:= by`.

Mismatches found: none. I left the correct Lean module and node record intact
and added this independent reading and its search evidence to the report.
No source correction, citer audit, or STATEMENT-DISPUTED flag is needed.
The prescribed scompile.py checked the sole delivered module in sandbox and
library modes under the normal 60-second limit, with no errors or warnings.
