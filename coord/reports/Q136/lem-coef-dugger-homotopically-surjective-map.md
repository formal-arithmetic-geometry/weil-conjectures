## Worker report

The module `Sheaf.AlgebraicTopology.DuggerHomotopicallySurjectiveMap` states
`HomotopicalAlgebra.exists_homotopically_surjective_presheaf_adjunction`.
Its only theorem has proof `sorry`; it introduces no definitions or axioms.
The node statement, proof, and proof dependencies are unchanged. Two already landed
nodes are added to statement dependencies to name the shared combinatorial-model
interface and the projective-presheaf structure, rather than duplicate either.
There are no new nodes, dependency repairs, or statement corrections.

Source checked: Daniel Dugger, *Combinatorial Model Categories Have Presentations*,
[Definition 3.1 and Proposition 3.3](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dugger-comb.pdf),
printed pp. 181–182; the general proof is in Section 6, pp. 189–191.
The source says every fibrant object and every cofibrant replacement, matching
both universal quantifiers in the Lean statement. No simplicial structure on M
or left properness of M is assumed.

Hypotheses and clauses:

- The universe convention is rendered by `universe u v`: U-small sets and D have
  universe u, simplicial sets are `SSet.{u}`, and M has arbitrary object universe v
  with U-small Hom sets `Category.{u} M`. The enclosing universe may be taken to
  contain both u+1 and v. No equality between the object universe v and u is imposed.
  `CompleteAlgebroid` is imported for the node's common universe convention only;
  none of its algebroid data is an extra hypothesis.
- The ordinary category M is `{M : Type v} [Category.{u} M]`.
  `[ModelCategory M]` supplies the three morphism classes, two-out-of-three,
  retract closure, finite limits/colimits, lifting and factorization axioms.
  Mathlib's two `ModelCategory` weak-factorization-system instances give the
  mutually characterized left/right lifting classes stated in the node.
- Completeness is `[HasLimitsOfSize.{u, u} M]`. Cocompleteness is included in
  `hM.locallyPresentable`, through Mathlib `IsLocallyPresentable` and
  `IsCardinalLocallyPresentable`. Both use small diagrams in universe u.
- Combinatoriality is `hM : CombinatorialModelCategory.{v, u, u} M`.
  Its local-presentability field is the existence of a regular cardinal and a
  small family of presentable objects giving filtered presentations, with ordinary
  Hom preserving the relevant filtered colimits. Its two generating-family fields
  use `J : Type u` and arrows of M. They identify each left class with the left
  lifting class against the generators' right class. In a model weak factorization
  system, taking right orthogonals gives exactly the generator right-class
  formulation of trivial fibrations and fibrations in the node. The two functorial
  factorization fields give the stipulated functorial model factorizations.
- The small ordinary category is `∃ (D : Type u) (_ : SmallCategory D)`; no
  nonemptiness condition is imposed. `Dᵒᵖ ⥤ SSet.{u}` is precisely U(D).
- The existential `P : ModelCategory (Dᵒᵖ ⥤ SSet.{u})` and the first three
  equalities specify its weak equivalences objectwise using
  `SSet.KanQuillen.weakEquivalenceStructure`, its fibrations objectwise using
  `SSet.modelCategoryQuillen.J.rlp`, and its cofibrations as the left lifting class
  against the objectwise trivial Kan fibrations `I.rlp`.
  The existing projective-model theorem identifies `I.rlp` as that trivial class.
  The ambient Kan structure uses monomorphism cofibrations, all horns in positive
  dimensions, and realization weak homotopy equivalences, exactly as in the node.
- Presheaves are complete and cocomplete by the pointwise Mathlib instances.
  The two explicit `HasFunctorialFactorization` conjuncts on P enforce the
  node's functorial-factorization convention on this model category as well.
  Intersections with the weak-equivalence class mean 'trivial'.
- The ordinary adjunction is the actual data `L`, `R`, `adj : L ⊣ R`.
  The first map-preservation conjunct preserves all cofibrations. The second
  preserves weak equivalences among cofibrations; together these say preservation
  of trivial cofibrations, hence the stated Quillen-adjunction condition.
- Fibrant X is exactly `fibrations M (terminal.from X)`.
- Every replacement is the quantification over `Q` and `q : Q ⟶ R.obj X`, with
  `P.categoryWithCofibrations.cofibrations (initial.to Q)` for cofibrancy,
  `P.categoryWithFibrations.fibrations q` and the P weak-equivalence property of q
  for a trivial fibration. No replacement is chosen or fixed in advance.
- The conclusion is `weakEquivalences M (L.map q ≫ adj.counit.app X)`, the
  specified composite rather than existence of some unrelated weak equivalence.
  This final quantified clause renders the definition of homotopical surjectivity
  inline; it introduces no second definition of a notion already in the project.
- The node's conventions about fibrant replacements and Quillen equivalences
  explain those terms but impose no such extra condition on this adjunction.
  Neither unused replacement data nor a Quillen-equivalence hypothesis is added.

Dependency declarations read and used:

- `def-coef-complete-algebroid`:
  `Sheaf.CategoryTheory.CompleteAlgebroid`,
  `SSet.Enhanced.Algebroid.completeCategory`; read its signature and source
  convention. Only the universe convention is relevant to this theorem.
- `def-weil-pbc-simplicial-set`: Mathlib `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`. Also read the recorded
  `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, `SSet.Finite`
  definitions in Degenerate, Subcomplex and Finite; those refinements are unused here.
- Added landed `lem-coef-model-colimit-localization-comparison`:
  `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`,
  `HomotopicalAlgebra.CombinatorialModelCategory`. Its full field signature and
  docstring were read. A DAG traversal confirms no path from this dependency to
  the item, so adding it creates no dependency cycle.
- Added landed `lem-coef-simplicial-presheaf-projective-model`:
  `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel`,
  `SSet.ProjectivePresheaf.simplicial_presheaf_projective_model`.
  Its full signature and proof docstring were read. It supplies the source model
  structure with exactly the W/F/C classes used here, including the empty-D case.
  This node was already a proof dependency. Its import is public because the
  statement uses the structures it exports.
- The other six proof dependencies have no recorded Lean module in the available
  DAG and no module is invented for a proof-only dependency. Their seven-step
  proof route is recorded in the theorem docstring for stage 3.

Edge cases checked before writing:

- Terminal model category: the conclusion permits a terminal source presentation
  and imposes no nontriviality condition on M.
- Empty D is allowed by the existential and by all three projective class formulas;
  the assertion does not claim every D presents every M.
- X can be initial or terminal when fibrant; only the stated fibrancy condition is
  required. There is no assumption that arbitrary X is fibrant.
- Q is arbitrary, and the identity replacement is included whenever R(X) is
  cofibrant. Weak equivalences alone are not substituted for trivial fibrations.
- The ambient universe v is independent of u, so large categories with small
  Hom sets are allowed. All small generators and diagrams use the same u as sSet.
- No enrichment, properness, nonempty indexing, or cofibrancy of R(X) is assumed.
- All universes and variables are explicitly bound (`autoImplicit false`).

Searches for an existing statement (all via `msearch.py` where applicable):

- LeanFinder: 'A combinatorial model category admits a homotopically surjective
  Quillen adjunction from simplicial presheaves on a small category'. Eight hits,
  including `CofibrantObject.toHoCat_obj_surjective`, nerve adjunctions and the
  simplicial-set fibration/cofibration structures. None gives the presentation.
- Loogle: 'HomotopicalAlgebra.ModelCategory, CategoryTheory.Adjunction'. One hit,
  `HomotopicalAlgebra.CofibrantObject.HoCat.adj`; it is an internal resolution
  adjunction and not a simplicial-presheaf presentation of arbitrary M.
- LeanSearch: 'Every combinatorial model category admits a homotopically surjective
  Quillen adjunction from simplicial presheaves'. Eight hits: Kan structure
  declarations, `ModelCategory.mk'`, cofibrant-object surjectivity and `sSetTopAdj`;
  none is the requested theorem.
- msearch grep: `homotopically[Ss]urjective|homotopically_surjective|CombinatorialModelCategory`
  in Mathlib AlgebraicTopology: zero hits.
- `rg` over the upstream project, side `lean/Sheaf`, and upstream name index for
  homotopical-surjectivity spellings and the chosen full theorem name: no match.
  The literal blueprint-id search in upstream project sources also had no match.
- Broader `rg` for `CombinatorialModelCategory`, Quillen-adjunction naming and
  projective-model declarations located the shared combinatorial definition and
  projective-model statement used above. The other Quillen clauses found concern
  supplied adjunctions or specialized comparisons, not this existence theorem.

Validation: the initial complete statement compiled cleanly through `scompile.py`.
The final statement additionally spells out both source functorial factorizations;
its compile and the delivery dry run are checked before pushing. No node fault or
STATEMENT-DISPUTED issue was found.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
