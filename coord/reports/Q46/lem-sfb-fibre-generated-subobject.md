## Worker report

The module `Sheaf.CategoryTheory.FibreGeneratedSubobject` states
`CategoryTheory.exists_fibre_generated_subobject`, with its entire proof `sorry`.
It introduces no definitions, helper theorems, or new nodes. The node is unchanged
except for its `lean` record. Source read directly: Milne, Algebraic Groups (2017),
Section 9(d), printed p.175 (PDF page 187), the subobject-lattice paragraph,
footnote 6, and the paragraph beginning “Let X be an object of C and S a subset”.
The surrounding Theorem 9.32 supplies precisely the category and fibre-functor
hypotheses used here.

Hypothesis and conclusion correspondence:

- The field k is `{k : Type r} [Field k]`.
- The category is `{C : Type u} [Category.{v} C] [Abelian C]`.
  `Abelian` provides the preadditive structure, zero object, finite biproducts,
  kernels, cokernels and normal monomorphisms/epimorphisms in `def-sp-abelian`.
- The k-vector-space structure on every Hom and bilinearity of composition are
  `[Linear k C]` (Mathlib's class has a module structure on each Hom and the two
  composition/scalar compatibility laws).
- Essentially small is `[EssentiallySmall.{w} C]`, meaning equivalence with a
  small category, with explicitly independent smallness, object and Hom universes.
- The functor is `(F : C ⥤ ModuleCat.{s} k)` together with
  `(h_finite : ∀ X : C, FiniteDimensional k (F.obj X))`. Over a field, these
  bundled modules are vector spaces, and this fibrewise finiteness is precisely
  the assertion that F takes values in finite-dimensional vector spaces. It
  imposes no bound on the cardinality of S.
- k-linearity of F is `[F.Additive] [F.Linear k]`: the former supplies addition
  preservation on Hom sets, the latter scalar preservation. The latter class
  alone does not contain additivity, so both parts of linearity are written.
- Faithfulness is `[F.Faithful]`, whose field is injectivity on each Hom set.
- Preservation of short exact sequences is exactly
  `(h_exact : ∀ T : ShortComplex C, T.ShortExact → (T.map F).ShortExact)`.
  No finite-limit/colimit hypothesis is substituted for or added to this clause.
- The arbitrary object and subset are `(V : C) (S : Set (F.obj V))`.
- The asserted monomorphism is `∃ (G : C) (i : G ⟶ V), Mono i ∧ ...`.
- Fibre containment is `S ⊆ Set.range (F.map i)`. Module-category arrows coerce
  to their underlying functions; this is the actual image of F(i).
- Every competing monomorphism j is quantified by
  `∀ (H : C) (j : H ⟶ V), Mono j → S ⊆ Set.range (F.map j) → ...`.
- The unique factorization is `∃! a : G ⟶ H, a ≫ j = i`.
  Lean composes left to right, so this is exactly j composed with a equals i.
- The “Thus” clause (least subobject, unique up to a unique isomorphism over V)
  is expressed by this same universal property. For any two witnesses, its
  unique factorizations in both directions compose to identities by mono
  cancellation. They are therefore the unique inverse arrows over V. This
  quantification over mono representatives is precisely the node's convention
  of identifying monomorphisms isomorphic over V; no chosen representatives or
  arbitrary intersection is introduced.
- Empty S and zero V are not excluded by any binder or hypothesis.

Dependency declarations read and reused:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (available through
  the public finite-dimensional import).
- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, full class and explanatory docstring.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, an abbreviation for
  `Module.Finite`. Its `fg_top` field and `Module.Finite.exists_fin` in
  `Mathlib.RingTheory.Finiteness.Defs` explicitly give a finite spanning family.
- `lem-sp-exact-functor-preserves-homology`: the recorded Mathlib match
  `CategoryTheory.Functor.preservesHomologyOfExact` in
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`, reached through
  the proof import `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`.
  That file also gives `Functor.exact_tfae`, bridging the exact hypothesis
  above to finite-limit and finite-colimit preservation for stage 3.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank`, imported for the proof plan.
- `lem-trf-finite-dimensional-short-exact-dimension`:
  `ModuleCat.free_shortExact_finrank_add`,
  `Mathlib.Algebra.Category.ModuleCat.Free`, imported for the proof plan.

The auxiliary statement vocabulary also uses existing Mathlib declarations:
`CategoryTheory.Linear` (Linear.Basic), `CategoryTheory.Functor.Linear`
(Linear.LinearFunctor), `CategoryTheory.EssentiallySmall` (EssentiallySmall),
`CategoryTheory.Functor.Faithful` (Functor.FullyFaithful), `ModuleCat`
(Algebra.Category.ModuleCat.Basic), `ShortComplex.ShortExact`
(Algebra.Homology.ShortComplex.ShortExact), and `Set.range`. Their source
signatures and docstrings were read. No dependency repair is needed.

Edge cases checked mathematically before writing:

- S empty: the zero subobject has the stated property; all competitors qualify,
  and there is exactly one map from the zero object to any competitor.
- V zero: its fibres are zero, and both possible subsets (empty and {0}) generate
  the zero subobject. No positive-dimension assumption is needed.
- S = {0}: again the zero subobject; S = the whole fibre: the identity subobject,
  since a mono containing the whole fibre becomes an isomorphism under exact
  faithfulness.
- For the identity functor on finite-dimensional vector spaces, the conclusion
  is the inclusion of the linear span of S with its usual universal property.
- For a forgetful functor from finite-dimensional comodules, it is the smallest
  subcomodule containing S; no assertion that every linear span is a subobject
  of the original category is made.
- k has arbitrary characteristic. All five universes u,v,w,r,s are explicit,
  with no additional universe equalities or implicit variables.

Searches for an existing statement:

1. `msearch.py ... leanfinder "For an exact faithful functor to finite dimensional
   vector spaces there is a least subobject whose fibre contains a given subset"`:
   eight hits, including Grothendieck `generatingMonomorphisms.largerSubobject`,
   `top_mem_range`, and Freyd–Mitchell. Reading the returned sources shows that
   the first requires Grothendieck data and is not least fibre generation, while
   the latter constructs a different embedding functor. No exact match.
2. `msearch.py ... loogle "CategoryTheory.Subobject, CategoryTheory.Functor.Faithful"`:
   only `CategoryTheory.Subobject.instFaithfulPullback`, unrelated.
3. `msearch.py ... grep
   "generatedSubobject|minimalSubobject|smallest.*subobject|least.*subobject"
   CategoryTheory`: two general subobject-classifier documentation hits.
4. `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
   for `generatedSubobject|fibreGenerated|fiberGenerated|least.*subobject|smallest.*subobject`:
   image-subobject, filtration and sheafification statements only. Reading
   `WeilConjectures/Mathlib/CategoryTheory/Subobject/Limits.lean` shows that
   `imageSubobject_le_iff` starts with a morphism in C, which a mere fibre subset
   does not provide. `rg` for this node id in `lean/WeilConjectures` returned no hit.
5. The proposed declaration name was searched in Mathlib, both library roots
   and the upstream name table: no collision. Binary intersections in Mathlib's
   Subobject/Lattice.lean do not supply this minimum-dimension argument by
   themselves.

The three msearch calls succeeded; their exact response summaries are in
`searches.jsonl` in the sandbox. No statement fault or disputed assertion found.

## Second reading by Q46

A separate in-thread reread compared the node, Milne p.175 and the written
signature clause by clause. The dispatcher explicitly forbids starting another
agent, so this is a worker self-check; the maintainer's independent review is
still required. The reread checked that additivity is included alongside scalar
preservation, h_finite quantifies over every source object, h_exact preserves
short exact sequences, the competitor quantifies over all monomorphisms into V,
and `a ≫ j = i` has the correct orientation. The unique-isomorphism sentence is
the consequence of the displayed unique factorization property for two witnesses,
not an extra choice or assumption. No mismatch or source correction was found.
No new nodes or dependency modules are delivered.
