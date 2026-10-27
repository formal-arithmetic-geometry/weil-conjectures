## Worker report

The module `Sheaf.RingTheory.FixedArrowScalarExtensionDiagram` states
`Module.fixedArrow_scalarExtension_diagram`, with its entire proof `sorry`.
The six helper definitions are actual specializations of Mathlib scalar extension:
`Module.fixedArrowStage`, `fixedArrowStageTmul`, `fixedArrowLimit`,
`fixedArrowLimitTmul`, `fixedArrowStageArrow`, and `fixedArrowLimitArrow`.
There are no new independent notions or dependency repairs. The item changes only
in `lean`. No theorem is proved and no definition contains postponed data.

The source was read at `algebra.tex`, lemma-limit-module-essentially-finite-presentation
(Tag 00QX), its presentation-matrix construction and clauses (1), (4), (6), and
lemma-mod-injective-general (Tag 046Y), its first proof paragraph. The node explicitly
isolates the fixed-stage algebraic construction used there; it does not assume the
local-ring hypotheses of the larger approximation result.

Hypotheses and objects:

- The small nonempty directed preorder is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. `B : I ⥤ CommRingCat.{u}` supplies all rings and their
  coherent transition maps `(B.map (homOfLE h)).hom`.
- `A : CommRingCat.{u}`, `κ : B ⟶ (Functor.const I).obj A`, and
  `hκ : Nonempty (IsColimit (Cocone.mk A κ))` are exactly the ring-colimit cocone.
- `c : I`, `P Q : ModuleCat.{u} (B.obj c)`, their two
  `Module.FinitePresentation` instances, and `v : P ⟶ Q` supply exactly the fixed
  stage, finitely presented modules and linear arrow. There are no other algebraic
  assumptions on the rings, modules or arrow.
- The directed tail is literally `Set.Ici c`, with the inherited preorder and its
  inclusion given by `.1`; `.2` is the map from c. It is small in the same universe.
  The final two conjuncts give its nonemptiness and directedness.
- `fixedArrowStage` and `fixedArrowLimit` use `ModuleCat.extendScalars` along
  `(B.map (homOfLE j.2)).hom` and `(κ.app c).hom`. Mathlib writes `A_j ⊗ P` and
  `A ⊗ P`, with the target-ring action on the first tensor factor. These are the
  specified `P ⊗ A_j` and `P ⊗ A` under the canonical tensor flip
  `TensorProduct.comm`. `fixedArrowStageTmul ... x a` and
  `fixedArrowLimitTmul ... x a` write the paper's argument order explicitly while
  returning the actual pure tensors `a ⊗ x`. The same definitions with Q give Q_j,Q_A.
- `fixedArrowStageArrow` and `fixedArrowLimitArrow` are the `.map v` of those
  actual scalar-extension functors, hence exactly `v ⊗ 1`, under that same flip.

Conclusions, in the order of the Lean signature:

- The witnesses `p`, `q`, `μ`, `ν` are semilinear maps over the specified ring maps.
  Semilinear maps contain additive maps and the required scalar compatibility, so
  neither additivity nor semilinearity is an extra hypothesis.
- For P the first five conjuncts give the pure-tensor transition formula, the
  pure-tensor cocone formula, transition identities, composition and cocone
  compatibility. The following conjunct gives finite presentation of every P_j.
  The next six repeat exactly these assertions for Q. The formulas determine the
  maps uniquely since pure tensors additively generate: these are specified
  canonical maps, not arbitrary maps with only abstract compatibility properties.
- The next two conjuncts are `q j k h (fixedArrowStageArrow ... x) =
  fixedArrowStageArrow ... (p j k h x)` and the analogous equation for ν, μ and
  `fixedArrowLimitArrow`. They are precisely both arrow squares in the node.
- For every j ≤ k the paired witnesses eP,eQ are module-category isomorphisms from
  the actual scalar extensions of P_j,Q_j to P_k,Q_k. Their two pure-tensor clauses
  prescribe the canonical maps `b ⊗ z ↦ b • p(z)` and `b ⊗ z ↦ b • q(z)`.
  The final equation in that block says extension of v_j, then eQ, is eP, then v_k.
- The next block repeats those three clauses at A, with the canonical formulas
  `b ⊗ z ↦ b • μ(z)` and `b ⊗ z ↦ b • ν(z)`, and intertwining with v_A.
  Under tensor commutativity these are exactly all four module-first comparisons
  in the node. An isomorphism in ModuleCat is equivalently a linear equivalence.
- For P and Q separately, the `∀ H f, compatibility → ∃! g, ...` block is the
  abelian-group colimit universal property of the specified cocone. The compatible
  additive maps f_j are its arbitrary competing cocone, g its unique factorization.
  Identity/composition and cocone compatibility already proved in the conclusions
  make p,q into functors and μ,ν into natural transformations; the explicit universal
  property is therefore exactly `IsColimit` for those additive diagrams, without
  introducing a separately chosen diagram or arbitrary comparison.
- The following `∀ x, ∃ j z, ...` blocks give representatives at one stage of each
  limit module. The final `↔ ∃ l hjl hkl, ...` blocks give both directions of the
  common-later-stage equality criterion for each module, allowing distinct stages.
- The zero modules, zero map, rank-zero presentations and rings with zero divisors
  are permitted by the types and absence of extra assumptions. No flatness,
  Noetherian, nontrivial-ring, positive-rank or injectivity assumption appears.
  All sets lie in the one common sufficiently large universe explicitly permitted
  by the node; the tail and group category impose no additional size hypothesis.

Dependencies read and reused:

- `def-weil-pbc-category-colimit`: its recorded
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, and canonical factorization interface. The hypothesis uses
  `IsColimit`, and the conclusion writes the same universal property in groups.
- `def-sc-finitely-presented-module`: recorded
  `Mathlib.Algebra.Module.FinitePresentation`, `Module.FinitePresentation`.
  Its finite-generators/finitely-generated-relations signature and docstring were
  read, including its equivalence to finite-free presentations.
- `def-weil-pbc-module-tensor-product`: its Mathlib match `TensorProduct`,
  `TensorProduct.lift`, `TensorProduct.ext'` and `LinearMap.rTensor` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `Basic`, and `Map`. These are reached
  publicly by `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`. The full existing
  scalar-extension definitions `ExtendScalars.obj'`, `map'`, `extendScalars` and
  their pure-tensor formulas were read. No tensor product is redefined.
- Proof dependency `lem-weil-pbc-colimit-initial-full-subcategory` is a Mathlib
  match in `Mathlib.CategoryTheory.Filtered.Final` and `Limits.Final` (available
  through the former). Its cofiltered-full-inclusion signatures were read.
- Proof dependency `lem-weil-pbc-tensor-right-exact` uses the recorded
  `Mathlib.LinearAlgebra.TensorProduct.RightExactness`, `rTensor_exact` and
  `lTensor_exact`; the exactness and surjectivity hypotheses were read.
- Proof dependency `lem-weil-pbc-tensor-finite-product` uses recorded
  `Mathlib.LinearAlgebra.TensorProduct.Pi`, `TensorProduct.piLeft`, including the
  finite, decidable index assumptions; zero ranks are allowed.
- Proof dependency `lem-weil-pbc-base-change-diagram-elementwise` uses the recorded
  `WeilConjectures.RingTheory.BaseChangeDiagramElementwise`,
  `Module.baseChange_diagram_elementwise`; its source signature and full proof
  docstring were read. It accepts the specified semilinear additive systems and
  canonical tensor comparisons and yields representatives and eventual zero.

The main theorem docstring carries all eight DAG proof steps, including the
cofinal-tail argument, finite-free presentation, balanced inverse formula,
intertwining calculation, elementwise criterion and additive universal property.

Edge cases checked before and during drafting: a singleton preorder (tail contains
c and is directed), c not least in I (all stage indices remain in `Set.Ici c`),
P=0 or Q=0, v=0, empty finite presentations, a zero ring, a non-flat scalar map
such as ℤ → ℤ/2, and non-antisymmetric directed preorders. No term requires a
nonzero element, positive rank, flat transition, cancellation or antisymmetry.
Comparison squares use arbitrary elements of the iterated tensor module, by an
equality of linear maps, not merely a selected set of pure tensors.

Searches for an existing complete statement:

- `msearch.py ... leanfinder`: “A fixed finitely presented module arrow gives
  compatible scalar extension diagrams along a directed ring colimit, with canonical
  tensor comparison isomorphisms and underlying abelian group colimits”. Eight hits:
  `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`,
  `ModuleCat.directLimitIsColimit`, filtered-colimit constructions for modules and
  finite-generation results. None states the fixed-arrow changing-ring result.
- `msearch.py ... loogle "TensorProduct, Module.DirectLimit"`: twelve hits including
  `TensorProduct.directLimitLeft`, `directLimitRight`, `toDirectLimit` and
  `fromDirectLimit`. Those identify fixed-base tensor/direct-limit modules; they
  do not give this specified changing-ring arrow diagram and all its clauses.
- `msearch.py ... grep "fixedArrow|fixed_arrow|baseChange_comp|directLimitRight"
  LinearAlgebra/TensorProduct`: nine hits, only directLimitRight and baseChange_comp
  tools; no complete match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for fixedArrow, fixed_arrow,
  FixedArrow, ScalarExtensionDiagram and the node id returned no existing statement.
  Broader scalar-extension searches found ringExtendScalars and geometric sheaf
  scalar extensions. The existing `exists_finitePresentation_module_diagram` in
  `WeilConjectures.RingTheory.FinitePresentationModuleDiagram` was opened: it
  existentially descends a presentation, assumes finite-type stage rings and has
  different objects; it is not this theorem. The concrete commutative-ring
  `ModuleCat.extendScalars` already supplies the exact scalar-extension objects
  needed here, so that existing construction is used directly.

The previous worker's message concerned a stage-1 re-split refusal. This packet
preserves the reviewed Q19 split verbatim and only supplies its absent Lean record;
it does not re-split the item. No statement fault or dispute was found.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
