## Worker report

Current return: immutable head `3f25b6b7e237`. The returned diagnostic is an
`--apply-fixes` pathname refusal for
`coord/reports/NF/lem-coef-resolution-interval-tensor.md`: that reviewer-fix
interface accepts `<item>.report.md` at the fix-directory root, rather than
the repository report pathname. No mathematical defect is identified in this
return. Following the repair brief, the retained packet was inspected and
dry-run first; `deliver2.py --no-push` accepted commit `c0b87530b2`, including
the per-file compile. This is a normal worker delivery, not an `--apply-fixes`
directory: its `report.md` is supplied to `deliver2.py`, which stages the report
at the repository pathname itself. The retained Lean module is unchanged.

The current self-check compared the saved node with the shared read-only
snapshot: only `lean` and the added coend-owner `stmt_deps` entry differ.
The tool rebuilds the packet against current `origin/newtargets-dag` on every
dry run. The recorded main signature was checked verbatim against the module,
all 13 declarations are recorded, all five postponed named theorems have
source/proof docstrings, and every Lean line is at most 100 characters.
The clause mapping and edge-case checks below were reread against the saved
node and module; no further mathematical change is needed for this return.

Repair of returned immutable head `9081064679d4`. The saved packet was inspected
first and its prescribed dry run passed at `b768b28a50`; the subsequent self-check
confirmed that the returned mathematical defects were still present. The work
was retained and repaired in the existing module, rather than replaced by an
unchanged push. The module is `Sheaf.CategoryTheory.ResolutionIntervalTensor`.

Hypotheses and clauses, against the unchanged natural-language node:

* The complete and cocomplete model category is `{M : Type u} [Category.{v} M]
  [HasLimits M] [HasColimits M] [ModelCategory M]`. The two
  `HasFunctorialFactorization` instances express the convention stated explicitly
  in `lem-coef-reedy-model-structure`: unlike Mathlib's `ModelCategory` alone,
  that dependency's model-category convention includes functorial factorizations.
  The object and Hom universes remain independent. Small sets, colimits and
  the regular cardinal use the Hom universe `v`; no equality of universes is imposed.
* A cosimplicial object is `A : CosimplicialObject M`. The hypothesis
  `hA : IsCosimplicialResolution A` is the conjunction of the recorded
  `Reedy.leftClass (monomorphisms SimplexCategory) (cofibrations M) (initial.to A)`
  and `∀ f, WeakEquivalence (A.map f)`. The positive simplex arrows are
  **monomorphisms**, as in the recorded `Reedy.simplex_reedy_structure`.
  The erroneous epimorphism latching class and redundant `IsReedyCofibrant`
  definition were removed.
* The canonical augmentation is the actual `resolutionAugmentation A`, whose
  component in degree `n` is `A.map (SimplexCategory.const n ⦋0⦌ 0)`.
  It targets the constant object on that same object's degree zero. There is
  no existential arbitrary augmentation or additional augmentation conclusion.
* The ordinary coend is the existing `CategoryTheory.framedHornCoend A K`.
  Its defining diagram `framedHornCoendDiagram A K` is indexed by `K.Elementsᵒᵖ`:
  objects label coproduct summands, and arrows impose exactly the simplex-operator
  relations. Its maps are the existing `framedHornCoendMap` and
  `framedHornCoendMapObj`. No replacement `resolutionCoendDiagram` or
  `resolutionCoend` is defined. `resolutionCoendι` merely names its actual
  colimit injection for a specified simplex.
* The functoriality clause is implemented by `resolutionCoendFunctor` and
  `resolutionTensorFunctor`. The latter is a real bifunctor
  `CosimplicialObject M ⥤ SSet.{v} ⥤ CosimplicialObject M`, constructed by
  composing the coend bifunctor, Mathlib's product bifunctor, `SSet.stdSimplex`,
  and whiskering functors. Its term is definitionally
  `framedHornCoend A (K ⨯ SSet.stdSimplex.obj n)`. Its simplex-operator map is
  `framedHornCoendMap A (prod.map (𝟙 K) (SSet.stdSimplex.map f))`;
  argument maps use the existing coend maps. Thus its objects, structure maps,
  and both argument actions are specified, rather than inferred from an
  existential degreewise object equality. The named postponed theorem
  `resolution_coend_functoriality` supplies only identity, composition and
  interchange proofs for these already constructed maps.
* `resolutionVertexComponent A k i n` is the coend injection indexed by the
  simplex corresponding under `SSet.yonedaEquiv` to
  `prod.lift (SSet.stdSimplex.map (SimplexCategory.const n ⦋k⦌ i)) (𝟙 _)`.
  `resolutionVertex A k i` bundles these into the actual natural transformation.
  `resolution_vertex_naturality` supplies its degree naturality, and
  `resolution_vertex_natural_in_object` states naturality in `A` as well.
  These are the vertex maps of the node, not unspecified weak equivalences.
* `resolution_tensor_point` states that `resolutionVertex A 0 0` is an
  isomorphism and that every vertex map equals this point inclusion followed
  by the tensor functor applied to `Δ[0] → Δ[k]`. The actual
  `resolutionTensorUnitIso A` is the inverse of that specified isomorphism.
  Its data is the uniquely determined inverse, not a choice from an
  unconstrained existence theorem. The two endpoints are exactly
  `resolutionVertex A 1 0` and `resolutionVertex A 1 1`.
* The first conclusion of `interval_tensor_resolution` is
  `IsCosimplicialResolution (((resolutionTensorFunctor M).obj A).obj Δ[1])`.
  The second gives `WeakEquivalence` for both specified endpoint components
  in every `n : SimplexCategory`. Neither requires a cardinal or presentability
  hypothesis. The last conclusion quantifies over `lambda : Cardinal.{v}`,
  `[Fact lambda.IsRegular]`, and then assumes termwise
  `IsCardinalPresentable (A.obj ⦋n⦌) lambda` to conclude the same for the tensor
  terms. `Cardinal.IsRegular.aleph0_le` supplies infinitude. Mathlib's
  `IsCardinalPresentable` is accessibility of the Hom functor at that cardinal.
* No simplicial enrichment of `M` is an input. Only the ordinary category,
  colimits, model classes and the stated model-category conventions are used.

All five postponed theorems are listed in `lean.declarations` together with
all definitions: `resolution_coend_functoriality`,
`resolution_vertex_naturality`, `resolution_vertex_natural_in_object`,
`resolution_tensor_point`, and `interval_tensor_resolution`. Each states a
clause of this very node (functoriality, canonical vertices/point identification,
or preservation), carries its source and blueprint id, and has a complete
proof docstring. No independent missing notion or additional definition node
is needed. Definitions have real data; only named theorem proofs use `sorry`.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.leftClass`, `relativeLatching`, and
  `simplex_reedy_structure`; `model_structure` and its full ambient
  functorial-factorization signature were checked for the model convention.
* Added the already-landed `lem-cbc-framed-horn-criterion` to `stmt_deps` and
  imported `Sheaf.CategoryTheory.FramedHornCriterion`, the owning module of
  `CategoryTheory.framedHornCoendDiagram`, `framedHornCoend`,
  `framedHornCoendMap`, and `framedHornCoendMapObj`. The generic coend helpers
  are used; the framed-horn theorem itself is not assumed in this proof.
* `def-weil-pbc-simplicial-set` is a **Mathlib leaf**, with its existing
  `mathlib_match` (`SSet`, degeneracy, subcomplex and finiteness declarations).
  It does not need a `lean` record or a repair. This module uses `SSet` and
  the representable `SSet.stdSimplex`, `SSet.yonedaEquiv`, and simplex operators.
* `def-coef-complete-algebroid` supplies universe conventions only here;
  its recorded `SSet.Enhanced.Algebroid.completeCategory` signature/docstring
  was read. No algebroid object appears in this ordinary categorical lemma,
  and no claim is made that importing its module supplies the coend or Reedy
  structure. The older report's import claim was incorrect.
* The proof imports `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`
  (`CategoryTheory.simplicial_boundary_collapse_test`),
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`, Mathlib's
  `SSet.anodyneExtensions_pushoutObjObjι`, and
  `CategoryTheory.Limits.colimitLimitToLimitColimit_isIso` /
  `filtered_colim_preservesFiniteLimits`, following the recorded proof plan.

Edge cases checked: in degree zero the positive punctured slice is empty,
so the latching condition is precisely cofibrancy of `A⁰`; epimorphisms would
instead include degeneracies and give the wrong test. At tensor degree zero,
`Δ[1] × Δ[0] ≅ Δ[1]`, so the two specified maps reduce to the two vertex
summands `A⁰ → A¹` under co-Yoneda. For the point tensor, the unique vertex
summand is invertible even without the resolution hypothesis. Constant
cosimplicial objects are not assumed Reedy cofibrant: the degree-one latching
map is a fold map, which need not be a cofibration. The empty simplicial set
has the initial coend. Terminal model categories and the zero resolution in a
pointed model category respect all constructions. The finite strict-chain
presentation of `[1] × [m]` gives finite colimits of terms, so the final clause
includes `lambda = aleph_0` and imposes no lower bound beyond regular infinitude.

Sources opened again: Dugger Appendix A.1's coequalizer and product formula,
and Lemma 6.4's interval functor and endpoint transformations; Hovey
Propositions 5.4.1, 5.4.3 and Corollary 5.4.4. The natural-language statement,
source, proof and proof dependencies remain unchanged. No statement correction
or STATEMENT-DISPUTED flag is needed.

Searches actually made during this repair:

* `msearch.py ... leanfinder "cosimplicial resolution interval tensor ordinary
  coend canonical endpoint maps"`: eight hits, including augmented-simplex
  tensor maps and Dold--Kan functors; none states this theorem or defines this
  ordinary frame tensor.
* `msearch.py ... loogle "SSet.stdSimplex, prod.map, framedHornCoend"`:
  invalid `prod.map` name in the remote index, no match claimed.
  Retried with `"SSet.stdSimplex"`: twelve hits giving the expected standard
  simplex, its fully faithful embedding and simplex equivalence.
* `msearch.py ... leansearch "Functoriality of a cosimplicial object tensored
  with a simplicial set via the coend"`: eight hits, including generic
  `coendFunctor`, `coend.map` and cosimplicial whiskering. These are not an
  existing theorem for interval tensors; the already-landed specialized
  category-of-elements coend is reused.
* `msearch.py ... grep "cosimplicial.*(resolution|tensor)|framedHornCoend|
  resolutionCoend" AlgebraicTopology`: no hits.
* `rg` over `lean/Sheaf` found `FramedHornCriterion.lean:39–78`, read in full
  for all four coend declarations. The same search over
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no competing
  declaration. Searches by the item id in upstream sources and
  `dag/lean_names_upstream.json` found no attachment. DAG searches identified
  the existing owner `lem-cbc-framed-horn-criterion`, now cited, so no new node
  was created. Source inspection found `prod.functor` and the whiskering
  functors, which are used directly rather than rebuilt.

Validation: `scompile.py` compiled both the sandbox probe and the final library
module cleanly, without warnings, with each file under the prescribed 60 seconds.
The final dry run and push are recorded by the delivery tool.

## Second reading by NF

Author's required self-check of the repaired node and module, not a claim of
independent review. No other agent was started, as instructed by the dispatcher.
Checked every hypothesis and conclusion against the clause mapping above.
The changes directly repair each returned fault: positive mono latching class;
actual bifunctor and explicit simplex action; canonical vertex summands and
point identification; unconditional resolution/endpoint conclusions;
conditional presentability only; reuse of the existing coend; accurate
Mathlib-leaf and universe-only dependency descriptions; complete helper
`lean.declarations` and exact main signature. The new bifunctor supplies
functoriality in both arguments, and the explicit vertex naturality theorem
covers naturality in `A`, not just in the degree. The two functorial
factorization instances are precisely the existing dependency's convention,
not presentability assumptions. All constructions use public recorded notions.
The independent maintainer review remains separate from this self-check.
