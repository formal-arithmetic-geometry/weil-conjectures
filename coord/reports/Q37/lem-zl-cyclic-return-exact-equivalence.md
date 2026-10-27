## Worker report

Item: `lem-zl-cyclic-return-exact-equivalence`, group Q37, stage 2.
The module `Sheaf.CategoryTheory.CyclicReturnExactEquivalence` states the entire node as
`CategoryTheory.Endofunctor.cyclicReturnExactEquivalence`. Its constructions have real data;
all seven named theorem proofs are `sorry`. No node statement was corrected, no dependency
record was repaired, and no new node was needed. The cyclic category is a notion explicitly
introduced by the assigned node, so its constructions belong to this node's own module.

### Hypotheses and objects

* The node's arbitrary abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`,
  with independent object and morphism universes.
* Its additive exact autoequivalence is `(P : C ⥤ C) [P.Additive] [P.IsEquivalence]`.
  An equivalence preserves all existing finite limits and colimits, so exactness is implied
  by these hypotheses, rather than replaced by any extra restriction.
* Its integer `m ≥ 1` is encoded as `(n : ℕ)` and `m = n + 1`. This covers every positive
  cycle length, including one, without a separate positivity-proof parameter.
* The carriers are the discrete diagram category `Discrete (Fin (n + 1)) ⥤ C`, which has
  exactly the independent entries of the tuple and componentwise morphisms. It uses the
  existing Mathlib functor-category abelian structure.
* `cyclicShiftComponent P n` selects evaluation at `j.succ` on index `j.castSucc`, and
  evaluation at zero followed by `P.iterate (n+1)` at `Fin.last n`. `cyclicShift` assembles
  these components using `Discrete.functor` and `Discrete.natTrans`.
* `CyclicTuple P n` is an abbreviation for the dependency's `IsoAlgebra (cyclicShift P n)`.
  Its structure isomorphism has exactly `a_i : A_(i+1) ≅ A_i` and the closing
  `P^(n+1) A_0 ≅ A_n`. The inherited algebra morphism square at each index is the node's
  `a_i ≫ u_i = u_(i+1) ≫ a_i'`, or its closing `a_n ≫ u_n = P^m(u_0) ≫ a_n'`.
  These are precisely the displayed equations after translating composition order.
  Identity and composition are inherited componentwise, with no extra morphism data.
* The target is literally the recorded `IsoAlgebra (P.iterate (n + 1))`, not a second
  definition of fixed pairs. `cyclicEval P n i` is its cyclic counterpart's forgetful
  functor followed by evaluation at index `i`.

### Every conclusion clause

* The specified return isomorphism is the real definition `cyclicReturnIso`:
  the closing edge followed by `cyclicPartialProduct ... (Fin.last n)`. The latter recurses
  by `r_0 = Iso.refl _` and `r_(i+1) = a_i ≪≫ r_i`; in conventional composition this is
  exactly `a_0 ∘ ... ∘ a_(i-1)` from `A_i` to `A_0`.
* The existential `E : CyclicTuple P n ≌ IsoAlgebra (P.iterate (n + 1))` supplies an actual
  equivalence, including natural unit/counit and triangles. Its functor object equation
  fixes the carrier to `A_0` and its structure to `cyclicReturnIso`; its map equation
  fixes the carrier map to `f.hom.f.app ⟨0⟩`.
* The real definition `cyclicConstantObj` has every carrier equal to `B.carrier`, all
  intermediate arrows `Iso.refl _`, and closing arrow `B.str`. The equation for
  `E.inverse.obj` specifies this exact tuple. Its map equation specifies the constant
  tuple `f.hom.f` at every index.
* `E.inverse ⋙ E.functor = 𝟭 _` is the node's strict `TS = id`, in Lean's left-to-right
  functor-composition convention. The counit carrier map is explicitly the identity.
* The unit of `E` already has direction `id ⟶ S T`; its component carrier maps are
  explicitly those of `cyclicPartialProduct`. This includes the required identity at zero.
  The heterogeneous equalities only transport morphism types along the already stated
  object equalities; they do not replace equality by existence of an unspecified comparison.
* Both `Nonempty (Abelian ...)` clauses state abelianness. Typeclass elaboration uses the
  actual upstream `IsoAlgebra.abelian` structure throughout, rather than choosing an
  unrelated instance from these existentials.
* Every `cyclicEval` preserves finite limits and colimits. Thus the canonical maps from
  evaluated kernels to carrier kernels and from carrier cokernels to evaluated cokernels
  are isomorphisms, expressing precisely the componentwise computations, including their
  universal inclusions/projections. The two analogous forgetful-functor preservation
  clauses state the corresponding underlying-object computation for the fixed-pair category.
  The upstream fixed-pair construction gives the induced structure on these universal
  objects. The explicit `IsIso` clauses for every cyclic and fixed-pair object cover these
  induced structures as well; kernels and cokernels are objects of the respective category.
* The two universal `ShortComplex` biconditionals state that exactness is detected on
  all cyclic carriers, respectively on the single fixed-pair carrier. Short complexes
  express a sequence at one middle term with zero composite; arbitrary sequences are
  exact exactly when all such triples are exact. Zero-composite detection is also reflected
  by the faithful forgetful/evaluation family, so no sequences are excluded by this encoding.
* `E.functor.Additive`, `E.inverse.Additive`, and all four finite-limit/colimit preservation
  clauses state that both functors are exact additive functors. The further two
  `ShortComplex` biconditionals explicitly give exactness preservation and reflection
  in both directions.
* For each cyclic object, and separately for each fixed pair in the inverse direction,
  the statement gives an order isomorphism `e` of subobject lattices. Its value is pinned
  to `Subobject.mk (E.functor.map U.arrow)` or the corresponding inverse image under `S`.
  Its order-isomorphism inverse supplies the reverse identification.
* For every comparable pair `U ≤ V`, the quotient clause identifies the image of
  `cokernel (Subobject.ofLE U V h)` with the cokernel of the corresponding inclusion.
  Taking `V` to be top gives the object's quotient by `U`; arbitrary comparable pairs
  include every successive filtration quotient.
* For every natural number `k`, the `eF` equivalence of monotone chains
  `Fin k →o Subobject A` is specified pointwise by the same subobject order isomorphism.
  This states transport of arbitrary finite filtrations, including all their inclusions
  and, by the preceding clause, all successive quotients, in each direction.
* For `m=1`, namely `n=0`, `Fin 0` has no intermediate indices. The only shift component
  is `P.iterate 1 = P` at the unique carrier. Thus cyclic objects and maps are exactly
  the single fixed-pair description written as diagrams on a singleton. The same theorem
  gives return equal to the closing arrow followed by identity and the identity unit.

The six preliminary theorem statements register the additive/exact properties needed
for elaborating these standard categories and `ShortComplex.map`: additivity and
invertibility of positive powers, additivity and finite-limit/colimit preservation of
the twisted shift, and additivity of `cyclicEval`. These are clauses of the same node's
explicit constructions and proof steps 3--9, are recorded in `lean.declarations`, have
source/proof docstrings, and do not introduce independent notions or assumptions.

### Dependency declarations and sources read

* `def-sp-abelian`: Mathlib `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; read the class and its complete docstring.
* `def-weil-endofunctor-fixed-pair-category`:
  `CategoryTheory.Endofunctor.IsoAlgebra`, `IsoAlgebra.forget`, `carrier`, `str`, `mk`,
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`. Read their signatures,
  real constructions, morphism square, docstrings, and kernel/colimit lifting interfaces.
* The public import of `WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor`
  supplies that recorded module transitively, together with `IsoAlgebra.abelian`, the
  actual preadditive structure, and exactness of `IsoAlgebra.forget`. All were read.
* `lem-weil-pbc-coimage-mono` and `lem-weil-pbc-abelian-of-coimage-image-iso` are Mathlib
  proof dependencies in `Mathlib.CategoryTheory.Abelian.Basic`, reached by the required
  imports. Read their actual declarations and docstrings. Their arguments are retained
  in the main theorem's proof plan, including the carrier comparison calculation.
* Also used Mathlib `Discrete.functor`, `Discrete.natTrans`, `Discrete.natIso`,
  `evaluation`, `functorCategoryAbelian`, `ShortComplex.Exact`, `Subobject`, `Subobject.mk`
  and `Subobject.ofLE`, and the existing upstream `Functor.iterate`.
* Read the PDF's printed pp.151--152 with `pdftotext -f 16 -l 17 -layout`: the paragraph
  after (1.1.10) is the field-change/cyclic-sheet argument. Read the current blueprint
  `sk-i-dl-general-real/_section.md`, the unit proof, and
  `thm-zl-real-mixed-by-curves.proof.md`. The assigned abstract lemma expands that
  paragraph's categorical calculation; it is not the unit's own statement.

### Edge cases checked

Cycle length one has no intermediate edges and the closing map is the original P-map;
length two has a single intermediate arrow and return `a_1 ≫ a_0` in Lean order.
The partial-product direction and closing square were checked explicitly in those cases.
Zero carriers and the zero abelian category satisfy the definitions with no nonzero
assumption. All powers include the zero-th recursive base internally, and the theorem
covers all positive lengths. Subobjects zero/top, their zero/full quotients, repeated
filtration terms, `k=0` empty chains and `k=1` singleton chains are included. No choice of
finite endpoints, characteristic, coefficients, smallness, lissity or semisimplicity is
imposed. Universes `u` and `v` remain independent. All declaration variables are bound
explicitly and the module sets `autoImplicit false`.

### Searches

* `msearch.py ... leansearch "cyclic isomorphisms of objects equivalent to fixed pairs of
  an endofunctor"`: eight hits, including `Endofunctor.Algebra.isoMk` and unrelated cyclic
  group results; no cyclic-return statement.
* `msearch.py ... leanfinder "A cycle of isomorphisms with closing arrow P^m A0 to A last
  is equivalent to fixed pairs for an exact autoequivalence of an abelian category"`, and
  `"category of cyclic tuples of isomorphisms with a twisted last arrow equivalence with
  fixed pairs"`: generic composable-arrow and exactness results, no requested equivalence.
* `msearch.py ... loogle "CategoryTheory.Endofunctor.IsoAlgebra,
  CategoryTheory.ComposableArrows"`, and `"CategoryTheory.Endofunctor.Algebra,
  CategoryTheory.Functor.iterate"`: no exact match; the remote search index does not know
  upstream `Functor.iterate`, so its actual local source was read and reused.
* `msearch.py ... grep "Cyclic|cyclic|IsoAlgebra" CategoryTheory`: no twisted cyclic tuple
  normalization. `rg` through Mathlib CategoryTheory, `lean/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json` found no declaration named `CyclicTuple`,
  `cyclicReturnExactEquivalence`, `cyclicPartialProduct` or `cyclicConstantObj`.
* Search for `IsoAlgebra` together with `Abelian`/`Preadditive` located the existing upstream
  `Preadditive/EndoFunctor.lean`; its structures and exact forgetful functor were reused.
  `rg` for the assigned node id in `lean/WeilConjectures` found no prior attachment.
* `tools/blueprint_refs.py search 'cyclic normalization'` returned zero blueprint nodes.
  DAG searches for the same notion found the assigned lemma and its consumers, not a
  separate definition node. These constructions therefore remain in the owning module.

Validation: `scompile.py Q37 lem-zl-cyclic-return-exact-equivalence <module>` passed both
its sandbox and library-name passes (10.1 s and 11.2 s) with no errors or warnings. All
seven theorem proofs are intentionally postponed for stage 3. No STATEMENT-DISPUTED issue.

## Second reading by Q37

I reread the node's statement and all eleven proof steps against the finished module.
This is the dispatcher's single-worker reading; the maintainer provides the independent
review, as specified in this assignment. No second agent was started.

The initial elaboration had required an explicit dependent case split for the constant
tuple; this was repaired without changing its data. The positive-power additive and
equivalence facts and additive evaluation were then exposed as named theorem statements
so that the node's natural hypotheses suffice for the exactness statements. No hypothesis
was added to the item. The clean compiler run confirms those interfaces elaborate.

On the clause reading: the Fin indices put the intermediate arrow from `succ` to
`castSucc`, with the P-power only at `last`; the original dependency's algebra square is
exactly the required morphism square; partial products point from `A_i` to `A_0`, giving
the required unit direction. The return and inverse object/map equations pin down the
specified functors; the strict functor equality is TS, and the counit map is identity.
Both abelian clauses, componentwise kernel/cokernel preservation, induced invertibility,
carrier exactness, functor exactness, subobject order isomorphisms, quotients for every
comparable pair and arbitrary finite chains are present in both directions. The singleton
case reduces to one closing edge and no intermediate equation; empty chains and zero
objects remain allowed. No source correction or missing clause was found.
