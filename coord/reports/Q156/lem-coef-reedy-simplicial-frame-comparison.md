## Worker report

The module `Sheaf.CategoryTheory.ReedySimplicialFrameComparison` states
`HomotopicalAlgebra.Reedy.reedy_simplicial_frame_comparison`, with `sorry` as its entire
proof. It adds no definitions, helper nodes, dependency modules, or statement corrections.
The item's node copy changes only `lean`.

Hypothesis and conclusion correspondence:

- The two model categories are `M : Type u`, `N : Type u'`, with independent morphism
  universes `v`, `v'`. Each has `ModelCategory`, `HasLimits`, `HasColimits`, and the two
  `MorphismProperty.HasFunctorialFactorization` instances. These render precisely the
  complete, cocomplete, functorially factored model-category convention of the dependency.
- `T : M ⥤ N`, `U : N ⥤ M`, and `adj : T ⊣ U` give the specified adjunction.
  `hTcof` and `hTtriv` separately assert preservation of cofibrations and trivial
  cofibrations for every ground arrow.
- `Yc : M` has both `IsCofibrant Yc` and `IsFibrant Yc`.
- `B : SimplexCategoryᵒᵖ ⥤ M` is the given simplicial diagram. `hB` says its terminal
  arrow is in `rightClass (monomorphisms SimplexCategory).op (fibrations M)`, hence it
  is Reedy fibrant for the opposite simplex Reedy structure.
- `hBzero : B.obj (op ⦋0⦌) = Yc` gives the stated degree-zero object. `i` has source
  `(Functor.const SimplexCategoryᵒᵖ).obj Yc`; `hi` places it in the relative-latching
  class `leftClass (epimorphisms SimplexCategory).op (trivialCofibrations M)`.
  `hizero` identifies its zero component with `eqToHom hBzero.symm`, which is the
  identity after the stated object identification.
- `r : T.obj Yc ⟶ Z`, `hr : trivialCofibrations N r`, and `IsFibrant Z` render
  exactly the fibrant replacement data specified by the node.
- `B' : SimplexCategoryᵒᵖ ⥤ N`, `hB'`, and `hB'zero` give the Reedy fibrant target
  and its degree-zero equality with `Z`. `i'` is the constant coaugmentation;
  `hi' : (weakEquivalences N).functorCategory SimplexCategoryᵒᵖ i'` means objectwise
  weak equivalence, and `hi'zero` gives its identity zero component.
- The first conjunct places the transported coaugmentation in the same Reedy trivial
  cofibration class over `N`. Its actual arrow is
  `(Functor.constComp SimplexCategoryᵒᵖ Yc T).inv ≫ Functor.whiskerRight i T`.
  Mathlib's canonical constant-composition isomorphism has identity components; its
  inverse changes the source to `const (T.obj Yc)`. No arbitrary comparison is used.
- `∃ b : B ⋙ T ⟶ B'` gives a natural transformation. Its first equation is the
  coaugmentation equation in the functor category, with composition written in Lean's
  left-to-right convention. Its second equation is
  `T.map (eqToHom hBzero.symm) ≫ b.app (op ⦋0⦌) ≫ eqToHom hB'zero = r`, namely
  `b₀ = r` under the two prescribed degree-zero identifications.
- `∀ n : ℕ, weakEquivalences N (b.app (op ⦋n⦌))` asserts every component is a weak
  equivalence, including degree zero. There is no assertion that `T` preserves fibrations
  or that the transported diagram is Reedy fibrant.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.ReedyModelStructure`: `HomotopicalAlgebra.Reedy.model_structure`,
  `simplex_reedy_structure`, `relativeLatching`, `relativeMatching`, `leftClass`, and
  `rightClass`, including their complete signatures, defining data, and source docstrings.
  The opposite simplex positive arrows are opposite surjections and the negative arrows
  are opposite injections, exactly as used in the statement.
- The proof dependency `lem-weil-pbc-left-adjoint-preserves-colimits` is a Mathlib leaf:
  `CategoryTheory.Adjunction.leftAdjoint_preservesColimits` in
  `Mathlib.CategoryTheory.Adjunction.Limits`. Its signature and Stacks 0038 docstring
  were read. That module is a non-public proof import.
- Mathlib's `Functor.constComp` in `Mathlib.CategoryTheory.Functor.Const` supplies the
  canonical diagram identification. The model classes and object predicates are Mathlib's.

Source checks: read the complete DAG statement and all four proof steps; read current
main-20261015 `prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2; opened Hovey's
linked PDF and located Theorem 5.2.5 and Theorem 5.2.8. The theorem docstring carries all
four steps of the supplied proof, including the terminal lifting square and two-out-of-three.

Edge cases checked before drafting: the degree-zero latching index is empty; the constant
diagram transport still uses identity components there. In degree one the positive
opposite-simplex maps are degeneracies from degree zero, so the latching orientation is
correct. With `T = id`, `r = id`, and equal frames the identity comparison has every stated
property. Constant frames are covered whenever they satisfy the displayed hypotheses.
The equality-map form handles non-definitional zero-object equalities without identifying
the independent category universes. All natural degrees, including zero, are quantified.
No node fault or disputed statement was found.

Searches made (all msearch queries were executed, rather than inferred):

- `leanfinder`: "A left Quillen functor transports a Reedy trivial cofibration of simplicial
  objects and lifts into a Reedy fibrant simplicial frame with prescribed degree zero".
  Eight hits on Kan fibrations, bifibrant objects, and cofibrant localization; no match.
- `leansearch`: the same query. Eight hits on Kan fibrations, Joyal lifting tricks,
  simplicial homotopy categories and universe lifts; no frame-comparison statement.
- `loogle`: `HomotopicalAlgebra.ReedyStructure, CategoryTheory.Functor.mapNatTrans`.
  No hits (the latter identifier is unknown). Follow-up `HomotopicalAlgebra.ReedyStructure`
  returned twelve hits for the abstract Reedy indexing structure and its operations.
- `grep` via msearch, AlgebraicTopology: `Reedy.*(trivial|frame)|simplicial.*[Ff]rame|relativeLatching`
  returned no hits. Broader `Reedy|latching|simplicial.*frame` returned five lines in
  `Mathlib/AlgebraicTopology/Reedy/Basic.lean`, including its Reedy-model-structure TODO.
- `grep` via msearch, all Mathlib: `ReedySimplicialFrameComparison|reedy_simplicial_frame_comparison`
  returned no hits.
- Direct `rg` of upstream `WeilConjectures` and project `lean/Sheaf` for the item id,
  proposed name, and simplicial-frame wording found the existing cosimplicial frame
  development and right-resolution constructions, but no theorem with this statement.
  `dag/lean_names_upstream.json` and Mathlib also contain no proposed declaration name.
  DAG searches located the distinct cosimplicial comparison node, which has different
  variance and hypotheses. The parent frame-mapping theorem merely describes this lift
  in its proof docstring; its declared conclusion does not supply this statement.

Validation uses the prescribed `scompile.py` and `deliver2.py --no-push` wrappers.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
