## Worker report

The module `Sheaf.AlgebraicTopology.EndpointFixedInnerHornRefinement` states
`SSet.endpoint_fixed_inner_horn_refinement`, with its proof `sorry` and all seven
DAG proof steps in its docstring. The two concrete helper declarations
`SSet.MixedInnerHorn` and `SSet.mixedInnerHornCell` encode the allowed cells of this
same statement, and are listed in `lean.declarations`. Their data are fully defined;
no definition chooses data from an unproved existence assertion.

Hypothesis and conclusion correspondence:

- Small simplicial sets are `{X Y : SSet.{u}}`, with no size restriction beyond the
  input universe. `[Quasicategory Y]` is exactly the quasicategory hypothesis on Y.
  Neither X nor a fibre is assumed inhabited or fibrant.
- `r : Y ⟶ Δ[1]` is the specified map, and `[InnerFibration r]` retains its stated
  inner-fibration hypothesis. It is not replaced by a Kan or Joyal fibration.
- `a : X ⟶ Y` is unrestricted as a simplicial map. `ha` is the categorical-equivalence
  condition verbatim from the weak-equivalence identification in
  `SSet.exists_joyal_model_structure`: restriction on ordinary homotopy categories
  of functor simplicial sets is an equivalence for every quasicategory C in the
  testing universe `max u v`. The input/output maps retain the same testing universe.
- `hend` says that the induced endpoint map is an isomorphism for each `e : Fin 2`.
  The canonical functor `Over.pullback (SSet.const (stdSimplex.obj₀Equiv.symm e))`
  takes a map over Δ[1] to its strict endpoint pullback. Its arrow is the actual
  arrow induced by a, not an arbitrary comparison. These pullbacks are canonically
  the degreewise fibres of the recorded `SSet.Enhanced.fiber`; Mathlib orders the
  two factors oppositely here. The map to Δ[0] retains the point coordinate.
- The existential `(M : SSet.{u}) (j : X ⟶ M) (k : M ⟶ Y) (h : j ≫ k = a)`
  is the factorization. The structure map on M is k ≫ r, so this is also strictly
  a factorization over Δ[1], without needing an additional map or compatibility
  assumption. The equality h is used to type the actual maps in the slices.
- `∀ n : SimplexCategoryᵒᵖ, Function.Injective (j.app n)` gives degreewise
  injectivity of j. The following universal hFun condition is its categorical
  equivalence, using exactly the same condition as ha.
- `(MorphismProperty.monomorphisms SSet.{u}).rlp k` is precisely trivial Joyal
  fibration. In the model structure dependency, cofibrations are degreewise
  injections (the monomorphisms of this presheaf category), and the first weak
  factorization system identifies their right lifting class with the trivial
  fibrations. This avoids choosing a model structure or adding model parameters.
  It imposes neither a stronger nor a weaker condition on k.
- `Nonempty (HomotopicalAlgebra.RelativeCellComplex.{u} ... (Over.homMk j h))`
  retains a countable continuous cell presentation of this very j **over Y**.
  Its shape is ℕ. Mathlib's parent `TransfiniteCompositionOfShape` supplies the
  well-order-continuous sequence, its initial isomorphism with X, and its colimit
  with point M, with the initial-to-colimit map equal to j. `AttachCells.{u}` at
  each successor supplies a pushout of coproducts with index type in Type u.
  Thus neither the cell sequence nor the smallness of each coproduct is omitted.
- Every permitted cell has dimension `c.n + 2`, index `c.i`, and proofs
  `0 < c.i` and `c.i < Fin.last (c.n + 2)`: exactly the inner horns. Its simplex
  `c.simplex : Δ[c.n + 2] ⟶ Y` is retained in the **slice** arrow, so the attaching
  squares and their fillers are over that specified simplex of Y.
  `c.mixed` excludes both constant interval maps, which is exactly nonconstancy
  of its Δ[1] coordinate. It excludes no mixed simplex and includes no pure cell.
- Finally, for each e an isomorphism `t` identifies the strict M endpoint with the
  X endpoint. The first equation sets the actual induced j endpoint map to
  `t.inv`. The second sets the actual induced k endpoint map to
  `t.hom ≫ a_e`. Consequently, identifying M_e with X_e by t and identifying
  X_e with Y_e by the given a_e, both maps are the identity. This is how the
  node's identified endpoint fibres are represented with Mathlib's chosen pullback
  objects: literal equality of arbitrary chosen pullback types is not required.
  In addition, mixed inner cells cannot add endpoint simplices: a constant simplex
  misses the opposite extreme vertex (0 or n), which differs from the missing
  interior index, so it is already in the horn.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: its Mathlib `SSet`, `stdSimplex`,
  `horn`, `Quasicategory` and internal functor simplicial sets. Its declaration
  docstrings specify the quasicategory and degreewise pullback conventions.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`, `SSet.hoFunctor`, `SSet.uliftFunctor`,
  and `CategoryTheory.MonoidalClosed.pre`, especially the full signature's hFun
  test and its first weak factorization system.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` publicly exports
  the original fibration interface. The used `SSet.InnerFibration` is Mathlib's
  inner-horn RLP predicate; `SSet.Enhanced.fiber` was read in the reexported
  `Sheaf.CategoryTheory.InfinityFibrations` to check the endpoint convention.
- Proof imports: `Sheaf.AlgebraicTopology.JoyalQuasicategoryCharacterizations`
  (`SSet.joyal_quasicategory_characterizations`, including its full model-class
  identifications), and `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
  (`CategoryTheory.Limits.combinedIsColimit`), the Mathlib match of the sectionwise
  colimit node. All stated proof dependencies are imported.
- The canonical cell API is Mathlib's `HomotopicalAlgebra.RelativeCellComplex`
  and `HomotopicalAlgebra.AttachCells`; canonical endpoint transport is Mathlib's
  `CategoryTheory.Over.pullback`. No replacement of these notions is defined.

Edge cases checked before writing: dimensions zero and one produce no inner cell,
and dimension two permits precisely index one. Constant and nonconstant interval
coordinates exhaust the cases because a simplex of Δ[1] is a monotone map into
{0,1}. An empty endpoint has its unique empty pullback and identity isomorphism;
no chosen vertex, nonemptiness or surjectivity from an empty source is assumed.
Both endpoints may be empty, giving the empty simplicial set case. Identity a
allows empty coproducts at every cell stage. Noninjective a is permitted: only
j is required injective, and pushouts preserve old simplices even with noninjective
attaching maps. No extra universe equality is imposed. The supplied hypothesis on
r is kept although the natural-language proof does not need it separately.

Searches performed:

- `msearch.py ... leansearch`: “A categorical equivalence of simplicial sets over
  the interval can be refined by a countable sequence of mixed inner horn
  attachments with unchanged endpoint fibers and a trivial Joyal fibration”.
  Eight hits on quasicategory horn filling and ordinary Kan-model fibrations,
  with no refinement statement.

- `msearch.py ... leanfinder`: “A categorical equivalence of simplicial sets over
  the interval factors into mixed inner horn cell attachments fixing both endpoint
  fibers and a trivial Joyal fibration”. Eight hits, ordinary Kan-model generators
  and unrelated standard simplicial constructions; no endpoint-fixed refinement.
- `msearch.py ... loogle`: `SSet.innerHornInclusions,
  CategoryTheory.SmallObject.RelativeCellComplex`. No hits; the latter anticipated
  name was unknown. Reading the source located the actual API in namespace
  `HomotopicalAlgebra`, used directly instead of a new cell-complex notion.
- `msearch.py ... grep`: `MixedInnerHorn|endpoint.fixed.*horn|mixed.inner.horn`
  in `AlgebraicTopology`: no Mathlib hits.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for endpoint-fixed /
  mixed-inner-horn names: no matching declaration, only unrelated endpoint-fixed
  homotopies and exact-sequence equivalences. Searching the exact item id upstream
  returned no match. Proposed declaration names also have no match in
  `dag/lean_names_upstream.json`, upstream sources, or the existing project sources.
- The current blueprint's
  `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`
  was read at the “For K” derived mapping-complex comparison. The explicit seven
  refinement steps are the item's agent expansion of that ancestor, as its source
  and proof_origin say. The node reviewer already notes that the source field's
  Corollary the project server reference should be the project server for the fibration characterization;
  the module docstring uses the corrected bibliographic locator. No mathematical
  node correction is needed, and no node field other than lean is changed.

There are no new nodes or dependency repairs, and no disputed statement. Compilation
and delivery preflight are run through the prescribed wrappers; the final verification
result is recorded below.

Verification: `scompile.py Q06 lem-coef-endpoint-fixed-inner-horn-refinement
.../EndpointFixedInnerHornRefinement.lean` exited 0, with no errors or warnings,
for both the sandbox check (24.4 s) and the module-path check (14.6 s). The first
attempt's endpoint universe inference and slice equality elaboration were repaired
by making `SSet.const.{u}` explicit and exposing the underlying composition before
rewriting by h. All universes and variables are bound explicitly.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
