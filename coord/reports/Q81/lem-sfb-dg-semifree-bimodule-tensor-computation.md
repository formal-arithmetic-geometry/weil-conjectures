## Worker report

The module `Sheaf.CategoryTheory.DgSemifreeBimoduleTensorComputation` states
`CategoryTheory.DgAlgebra.semifree_bimodule_tensor_computation`, with its sole
proof `sorry`, and supplies the explicit `SemiFreeFiltration` appearing in the
item's own statement. No node statement has been corrected.

The source read is `literature/stacks-project/dga.tex`, section-P-resolutions
(Tag 09KK, lines 2180 onward) and lemma-derived-bc (Tag 09LS, lines 5324 onward).
The latter constructs the total left derived functor using property-(P) objects;
the former gives exactly the semi-free filtration in this item.

Hypotheses and clauses, in statement order:

- The fixed universes are rendered by explicit `universe u`, `Algebra.{u}` and
  cell sets `index : ℕ → Type u`. The existing Gabriel--Zisman localization
  `Derived A` is in its larger universe. No equality with a separate smaller
  universe, size bound on cell cardinalities, or countability is introduced.
- Associative unital integral DG algebras are the dependency's `Algebra`:
  monoids in cochain complexes of `ModuleCat (ULift ℤ)`. Their differential,
  multiplication and unit are actual data. `RightModule A` uses module objects
  in the reversed tensor category, with the stated right-action Leibniz rule.
- `DerivedStructure A` and `DerivedStructure B` are the dependency's structural
  interfaces for the specified localization's standard shifts and mapping-cone
  triangles. They add no flatness, projectivity or boundedness requirement.
- `N : Bimod A B` has the commuting chain-map left and right actions;
  `_t : BalancedTensorModel N F` specifies the balanced DG tensor functor,
  its action, differential and functorial maps. In particular its `right_action`
  is induced by the action on N, and `naturality` pins `F.map f` to tensoring f
  with the identity. These are not arbitrary functor or action parameters.
- `T`, `α : Q A ⋙ T ⟶ F ⋙ Q B`, and `[T.IsRightKanExtension α]` use exactly
  the universal total-left-derived comparison in the recorded
  `bimodule_derived_tensor_hom_adjunction`. The theorem quantifies over any
  presentation of this canonical universal pair, so applies directly to the
  pair that theorem supplies; it does not require choosing its existential
  witnesses as new global definitions.
- `SemiFreeFiltration A P` gives `stage 0 = 0` up to the unique module
  isomorphism, using `initial` in each degree. This is the harmless reindexing
  `stage (p+1) = F_p P`, and `stage 0 = F_{-1} P`.
- `inclusion`, `injective`, `transition`, and `compatibility` realize the
  increasing DG submodules of P. Injectivity into P implies injectivity of
  transitions. `exhaustive` states that every homogeneous element of P lies
  in one of these submodules. Exhaustiveness degree by degree is equivalent
  to the stated graded union, since graded elements have finite support and
  the stages are increasing.
- `retraction`, `retraction_left_inverse`, and `retraction_action` give graded
  right A-linear splittings of successive inclusions. The maps are additive
  degree maps and are not required to commute with differential.
- `layer`, `quotient`, `quotient_surjective`, and `quotient_exact` identify the
  layer with the actual DG quotient of successive stages. Exactness is the
  equality of image and kernel degree by degree, not an arbitrary layer.
- `index`, `shift`, `cell`, and `cell_shift` give every shifted regular module
  in that layer. `ShiftComparison` includes the complex shift differential
  `(-1)^k d` and the unchanged right action. `cellMap` consists of DG module
  maps; `cells_colimit` makes their underlying degree maps coproduct cocones
  in `ModuleCat`, exactly a small direct sum of those shifted DG modules.
  These maps' compatibility with the differentials and actions ensures the
  coproduct is a DG-module coproduct as well. No coproduct merely in D(A)
  is substituted for the required DG-module direct sum.
- `Nonempty (SemiFreeFiltration A P)` is the property of being semi-free; it
  does not select data from a postponed existence theorem.
- The first conclusion `IsIso (α.app P)` says that this very canonical map
  `T.obj ((Q A).obj P) ⟶ (Q B).obj (F.obj P)` is invertible in `Derived B`.
  Thus it is the required isomorphism of DG B-module derived objects, and
  neither an underlying-complex nor only a cohomology comparison.
- The second conclusion states the naturality equation for every DG map
  `f : P ⟶ P'` between semi-free modules. In composition order it is
  `T.map (Q.map f) ≫ α.app P' = α.app P ≫ Q.map (F.map f)`.
  The tensor model identifies the last map with the class of `f ⊗ id_N`.
- There are no flatness over Z, boundedness, countability, compactness or
  self-extension hypotheses on A, B, P or N.

Dependencies read and used:

- `def-weil-size-convention`: its recorded metatheoretic convention is rendered
  by explicit universe levels, with no declaration to import.
- `Sheaf.CategoryTheory.DgBimoduleDerivedAdjunction`,
  `CategoryTheory.DgAlgebra.bimodule_derived_tensor_hom_adjunction`: read its full
  docstring and signature, including the balanced tensor model, universal
  comparison and universal property. This is the public import.
- Its public dependencies `Sheaf.CategoryTheory.DgBimoduleModels` and
  `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`: read their full definitions
  of `BalancedTensorModel`, `Algebra`, `RightModule`, `Derived`, `Q`, `regular`,
  `underlying`, `act`, `ShiftComparison` and `DerivedStructure`.
- Mathlib `CategoryTheory.Functor.IsRightKanExtension` is the exact universal
  property already used by the dependency, not a new derivability predicate.
  `Function.Exact` and `Cofan.mk`/`IsColimit` express the ordinary quotient and
  direct-sum conditions.

The proof dependencies without recorded declarations are described in the
proof docstring, not restated as extra theorems. The old recorded source
`Sheaf.CategoryTheory.SemiFreeDGModule` for
`lem-coef-dg-semi-free-homotopically-projective` is absent locally and
`scompile.py --source Sheaf.CategoryTheory.SemiFreeDGModule` also answered
`Module source unavailable`; importing it is impossible. Its former category
presentation has not been copied. This item only supplies its own filtration
notion on the current dependency's `RightModule A`, as explicitly permitted
for helpers belonging to the owning node. The same filtration notion is
already described in this node and `lem-sfb-dg-property-p-resolution`, so no
second independent definition node is created. The missing proof dependency
import can be added by maintenance once that theorem is restated.

Edge cases checked mathematically before writing:

- P = 0: all stages and layers can be zero, and each index type can be empty.
  The empty degreewise coproduct forces the layer to be zero.
- A[k] for arbitrary positive, zero or negative k: a one-cell first layer,
  followed by zero layers, gives the filtration with exactly the dependency's
  signed differential and unchanged right action.
- Arbitrary uncountable small cell sets: allowed by `index p : Type u` and
  degreewise coproduct cocones; the sequential filtration does not bound the
  cardinality of a layer.
- Unbounded P and N and rings with integral torsion: there is no degree bound
  or integral flatness assumption anywhere in the signature or filtration.
- Zero N and the zero algebra are not excluded. The tensor comparison remains
  an assertion in the actual localization of B-modules.
- Non-semi-free modules are not claimed to compute ordinary tensor. Their
  universal derived functor is still allowed as input to the theorem.

Searches actually run:

- `msearch.py ... leanfinder` query: “A semi-free differential graded module
  computes derived tensor with a differential graded bimodule”. Eight hits
  concerned Mathlib cochain tensor (`HomologicalComplex.ιTensorObj`, `tensorObj`,
  `HasGoodTensor₁₂`, `HasTensor`, etc.); no semi-free computation theorem.
- `msearch.py ... loogle` query:
  `CategoryTheory.Functor.IsRightKanExtension, IsIso, DgAlgebra`.
  Zero hits; service reported unknown identifier `IsIso`. This is a search
  failure, not evidence that the canonical isomorphism predicate is absent.
- `msearch.py ... grep` query:
  `SemiFree|Semifree|BalancedTensor|DgAlgebra`. Zero Mathlib hits.
- `msearch.py ... leansearch` query:
  “semi free differential graded module filtration direct sums shifts”. Eight
  hits on filtered algebras, graded modules and ideal filtrations; no DG
  semi-free filtration or derived-tensor computation.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for semi-free/property-(P)
  names found the existing DG framework and property-P devissage proof plan,
  but no usable current semi-free filtration or this theorem. The upstream
  node-id search found no occurrence. `dag/lean_names_upstream.json` likewise
  contained no matching names.
- `rg` in Mathlib `CategoryTheory` and `Algebra/Homology` for
  `PropertyP|IsSemiFree|Semifree|semi.free`: no match.
- `tools/blueprint_refs.py search 'semi-free'`: zero blueprint nodes.
  DAG name searches found the known resolution/projectivity nodes, rather
  than a usable duplicate declaration of this computation.

No statement dispute or item fault was found. The withdrawn example module
`Sheaf.CategoryTheory.CompactObject` contains no declarations now; its node
points to `WeilConjectures.CategoryTheory.CompactObject`, which was read for
current module/header conventions.

## Second reading by Q81

A second pass by this worker, with the node and completed file open, checked
all hypotheses and clauses listed above. No separate agent was started, as
required by the dispatch brief; the maintainer provides independent review.
The important checks were that the filtration starts at F_{-1}, rather than
omitting the first free layer; splittings preserve the graded action without
requiring differential compatibility; quotient layers are actual DG quotients;
and the free cells are shifts in DG modules, rather than shifts only after
localization. The first degreewise coproduct includes the empty-cell case.

The theorem uses the dependency's own universal comparison α and proves
invertibility of that arrow in D(B), so neither an arbitrary isomorphism nor
a weaker cohomology comparison has been substituted. The tensor model fixes
all right B-actions and the map f tensor id. The naturality equation has the
correct order and quantifies over every DG map between the two semi-free
modules. No assumptions about N's flatness or P's cardinality slipped into
these data. This pass found no mismatch requiring a change.

Validation: the prescribed `scompile.py Q81
lem-sfb-dg-semifree-bimodule-tensor-computation <module>` completed with exit
code 0 for both the sandbox probe and the final library module, with no
compiler errors or warnings. The signature in `lean.statement` is copied
verbatim from the file, and all source lines have at most 100 characters.
