## Worker report

The module `lean/Sheaf/CategoryTheory/ProjectiveFrameWeightedCoend.lean` states the
projective-frame weighted-coend theorem in namespace
`HomotopicalAlgebra.ProjectiveFrame`. It introduces `Compatible`, the predicate that
records the two coend relations, and `IsCoend`, the universal property of the double
coend. These are statement-level predicates with no chosen data or `sorry` definitions.
The theorem has proof `sorry`, as required for stage 2.

The target's fixed small category is rendered by `(J : Type w) [SmallCategory J]`.
The model category is `(M : Type u) [Category.{v} M] [ModelCategory M]`, together with
large limits and colimits and the functorial factorization classes required by the
Reedy construction. The projective model structure on `M^J` is represented by
`P : ModelCategory (J ⥤ M)`, with `hPW` identifying its weak equivalences with
`(weakEquivalences M).functorCategory J` and `hPF` identifying its fibrations with
`(fibrations M).functorCategory J`. Both projective weak factorization systems
also have explicit `HasFunctorialFactorization` binders, retaining the dependency's
functorial-model-category convention for `P` as well as for `M`.

The cosimplicial frame is `V : SimplexCategory ⥤ J ⥤ M`. Its Reedy cofibrancy is
rendered by `hV`, requiring every latching map
`Reedy.latchingTo (monomorphisms SimplexCategory) V n` to be a projective cofibration.
Homotopical constancy is rendered by `hconst`, requiring
`weakEquivalences M ((V.map a).app j)` for every simplex arrow `a` and object `j`.

The conclusion supplies an injective model structure `I` on
`Jᵒᵖ ⥤ SSet`, a left functor `L`, and an adjunction `a : L ⊣ mappingFunctor V`.
The weak-equivalence class of `I` is the Kan weak-equivalence class objectwise, and its
cofibrations are objectwise monomorphisms. The right adjoint is the actual composite
`uliftYoneda ⋙ whiskeringLeft.obj (...) ⋙ curry ⋙ flipFunctor`. Its value at `T, j, n`
is `ULift ((V.obj n).obj j ⟶ T)`; the lift puts Hom sets in the containing weight
universe. Yoneda gives precomposition by both `V.obj n` on arrows of `J` and `V.map`
on simplex arrows, and postcomposition on arrows of `M`. The product-opposite
equivalence, currying, and flip only reorder these indices.

For every weight `K`, `IsCoend V K` is asserted for the coprojections
`fun j n x ↦ (((a.unit.app K).app (op j)).app (op n) x).down` into `L.obj K`.
Thus the coend object, its maps on weights, and its adjunction are tied together
through the unit's naturality, rather than only identifying objects. `Compatible`'s
first equation imposes `K(a)(x)` versus `V(a)` for each arrow of `J`, and its second
equation imposes the corresponding simplex relation. `IsCoend` requires those
relations and the unique factorization of every compatible family into any `T`.
This is exactly the coproduct-modulo-relations double-coend universal property. The final two clauses say that `L` sends objectwise monomorphisms to
cofibrations, and objectwise monomorphisms that are objectwise weak equivalences to
trivial cofibrations. The empty index case is permitted because `J` has no nonempty
assumption.

The statement dependencies used are:

- `Sheaf.CategoryTheory.ReedyModelStructure`, declaration
  `HomotopicalAlgebra.Reedy.model_structure`.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`, declaration
  `SSet.KanQuillen.right_proper_kan_quillen`.
- `Sheaf.CategoryTheory.CombinatorialInjectiveDiagramModel`, declaration
  `HomotopicalAlgebra.combinatorial_injective_diagram_model`.

The proof plan imports the stated proof-dependency modules, including Mathlib’s
Brown factorization and parametrized-adjunction corner-lifting modules, the free-bar,
simplicial boundary-collapse, simplicial presheaf projective, and realization lemmas;
none of their proofs are used in this stage-2 declaration.

Edge cases checked against the node are `J = ∅`, `J` terminal, an empty simplicial
weight, a zero/initial value of `M`, and `n = 0`. The universal property allows the
initial coend when the index or weight is empty. No nonemptiness,
properness, simplicial enrichment, or fibrancy hypothesis was added.

Searches for an existing declaration were made with:

- `msearch.py ... leanfinder "projective frame weighted coend Quillen adjunction"`:
  returned projective presentations and cofibrant-object results, but no weighted-coend
  Quillen theorem.
- `msearch.py ... loogle "ModelCategory, Quillen, Functor"`:
  no match (the queried identifier was not available to Loogle).
- `msearch.py ... grep "weighted|coend|Quillen" Mathlib/CategoryTheory`:
  no match.
- `rg -n "coend|weighted|Reedy|Quillen"` over Mathlib, the source
  `WeilConjectures`, and `lean/Sheaf`: only ordinary coends, simplicial model
  structures, and unrelated Quillen declarations were found.
- `grep -rl "lem-coef-projective-frame-weighted-coend"` over the source repository:
  no existing source declaration.

The file was compiled with the prescribed `scompile.py Q58
lem-coef-projective-frame-weighted-coend <file>` wrapper; both the sandbox and named
library module compiled cleanly. No `STATEMENT-DISPUTED` issue was found.

The resumed self-check read `uliftYoneda` in `Mathlib.CategoryTheory.Yoneda`,
`Functor.whiskeringLeft` in `Mathlib.CategoryTheory.Whiskering`, `prodOpEquiv`
in `Mathlib.CategoryTheory.Products.Basic`, `Functor.curry` in
`Mathlib.CategoryTheory.Functor.Currying`, and `flipFunctor` in
`Mathlib.CategoryTheory.Functor.Category`. These existing constructions supply the
mapping diagram without duplicating their definitions. The Hirschhorn source URL
was opened; as the node specifies, the injective
weight interchange is the DAG's adaptation of that source.

## Second reading by Q58

The resumed worker reread the saved node and module directly; no additional agent
was started, as required by the dispatcher brief. This self-check found that the
saved statement left the right adjoint arbitrary and specified coends only on
objects. The module now defines `mappingFunctor V` as the concrete Yoneda and
precomposition composite and specifies coend coprojections as the transpose of the
adjunction unit. In particular, the mapping formula, both precomposition actions,
the action on morphisms of weights, and compatibility with the adjunction are now
included. No mathematical node correction was required: these were gaps in the
saved Lean rendering of the unchanged node.

The model-category binders include completeness, cocompleteness and both functorial
factorizations required by the Reedy dependency, for both `M` and the projective
model `P`. Mathlib's bare `ModelCategory` only supplies non-functorial factorizations;
the final self-check made the two projective functorial-factorization binders explicit.
The `w`-small limits/colimits and
`max w v t`-small colimits express its containing-universe convention, including
large simplicial weights. `hPW` and `hPF` specify the projective structure, `hV`
specifies all Reedy latching cofibrations, and `hconst` quantifies over every
cosimplicial arrow and every object. The two class equalities specify the injective
model and both final implications use exactly its objectwise monomorphisms and
realization-based weak homotopy equivalences. No properness or simplicial enrichment
is assumed. For empty `J`, the mapping diagram is unique and `IsCoend` says precisely
that `L.obj K` is initial; for an empty weight the same initial-object property
results, and degree zero includes the initial latching map.

The initial dry run also found that the saved `lean.statement` ended in `:=`,
whereas the preflight's signature extraction stops before it. The record now matches
the file verbatim before that delimiter and lists all four declarations. The
updated file compiled cleanly in both sandbox and library modes through
`scompile.py` (2.2 and 2.0 seconds). All data definitions are explicit compositions
or propositions, all variables and universes are bound, and the sole postponed
proof is `weighted_coend_adjunction`, with the ten-step DAG proof in its docstring.
The unchanged node has no `STATEMENT-DISPUTED` issue.
