## Worker report

Module `Sheaf.Algebra.Homology.TotalOplaxConjugationSummands` states the full
five-factor conjugation calculation. It defines the ordinary and total
isomorphisms with real data, using the published single-functor comparisons.
Every theorem has only `sorry`; no notion or postponed auxiliary lemma was added.
All companion statements are clauses of this item's own statement, listed in
`lean.declarations`. There was no repair note and no statement correction.

Hypotheses and objects, matched with the node:

- Four abelian categories: `A₀`, `A₁`, `B₀`, `B₁` with explicit, independent
  object universes `u₀,u₁,u₂,u₃` and morphism universes `v₀,v₁,v₂,v₃`, each
  with `Category`, `Abelian`, and `MonoidalCategory` instances. No equality
  between any object and morphism universe is imposed. A containing universe
  may contain all eight universes; there is no restriction on category sizes.
- Additive tensor in both variables is `MonoidalPreadditive` on each category.
  The small-colimit assumptions supply `HasColimitsOfSize.{0,0}` on all four
  categories and `PreservesColimitsOfSize.{0,0}` for each left and right tensor
  functor. As in the recorded termwise-strong-monoidal dependency, these are the
  sufficient small-index consequences of all-small-colimit existence and
  preservation: the only constructions here use integer pair/triple fibres.
  This interface works with independent category universes and needs no
  closedness, braiding, symmetry, or cocontinuity of Fi or Fs beyond coproducts.
- `E₀ : A₀ ⥤ B₀`, `E₁ : A₁ ⥤ B₁` carry `IsEquivalence`, `Additive`,
  and `Monoidal`; `Fi : A₀ ⥤ A₁`, `Fs : B₀ ⥤ B₁` carry `Additive`,
  `Monoidal`, and the two quantified countable-discrete-colimit preservation
  instances `hFi`, `hFs`. Equivalences infer their own colimit preservation.
- The arbitrary square isomorphism is `a : Fi ⋙ E₁ ≅ E₀ ⋙ Fs`. Lean writes
  functor composition in order of application, so this is exactly E1 Fi ≅ Fs E0.
  There is no `NatTrans.IsMonoidal a.hom` hypothesis.
- Unbounded complexes are `CochainComplex A₀ ℤ`; no bounds or exactness binders
  occur. `mapHomologicalComplex (.up ℤ)` is termwise application, and
  `NatIso.mapHomologicalComplex a (.up ℤ)` is termwise a. Tensor is the existing
  signed `HomologicalComplex.tensorObj`, with ordinary complex constraints
  from `HomologicalComplex.monoidalCategory`.

Definitions and conclusions, matched clause by clause:

- gamma G is `(Functor.Monoidal.μIso G M N).symm`, epsilon G is
  `(Functor.Monoidal.εIso G).symm`. The published `G.mapCochainComplexμIso P Q`
  inverted is the node's T_G. `G.mapCochainComplexεIso.symm` is j_G: the
  definition uses `single.mapIso` and `singleMapHomologicalComplex`, hence
  epsilon in degree zero and the unique zero-object comparisons elsewhere.
  These are reused directly, rather than duplicated under new names.
- `conjugatedTensorIso` is exactly gamma tilde, as an isomorphism. Its five
  factors, in Lean order of application, are Fs applied to mu E0, a inverse,
  E1 applied to delta Fi, delta E1, and tensor of the two components of a.
  This reverses the printed right-to-left formula, without changing its maps.
- `conjugatedTotalTensorIso` is A, with factors Fs_Ch applied to T_E0 inverse,
  termwise a inverse at P tensor Q, E1_Ch applied to T_Fi, T_E1, and tensor
  of termwise a_P and a_Q. Its declared result is a complex isomorphism, so
  the chain equation and inverse equations are part of the actual data.
- `total_tensor_degree_countable` states both `Countable` and `Small.{0}` for
  `{pq : ℤ × ℤ // pq.1 + pq.2 = n}`. Smallness at zero implies smallness in
  the fixed containing universe. The proof docstring gives the bijection
  p ↦ (p,n-p), inverse to the first projection.
- `total_oplax_coproduct_E₀`, `_E₁`, `_Fi`, and `_Fs` state that the image
  of the degree-indexed coproduct cocone is colimiting and that its canonical
  inverse comparison carries G of each injection to the corresponding
  injection. `PreservesCoproduct.iso G Z` is kappa_G inverse; its inverse is
  `sigmaComparison G Z`, the canonical map induced by the images of the
  injections. Specialize Z to the tensor summands of the source total.
  The chosen total-degree coproduct and its injections are precisely the
  same `GradedObject.mapObj` coproduct and `Sigma.ι` used here.
- `total_oplax_conjugation_summands` says
  `Fs.map iota ≫ A.hom.f n = gammaTilde.hom ≫ iota'`, for every p,q,n,h.
  This is exactly the node's displayed equation with Lean composition order.
- `conjugatedTensorIso_naturality` states the ordinary two-input equation
  for f and g; the composites are Hf tensor Hg, H = E0 followed by Fs.
- `conjugatedTotalTensorIso_naturality` states naturality in both entire
  complexes, with actual tensor maps on the termwise images.
- `conjugatedTotalTensorIso_differential` states the chain equation after
  the (p,q) injection, expanded as the horizontal naturality term plus
  `p.negOnePow` times the vertical one. The target degree is p+q+1.
  The source maps are precisely Fs(E0(dP) tensor 1) and
  Fs(1 tensor E0(dQ)); the proof docstring explains identification with
  the two target-differential terms by ordinary naturality. Since A is
  constructed as a complex isomorphism, the unexpanded global chain
  equation is already available as A.hom.comm.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, including its full class signature.
- `def-sfb-monoidal-category`: `CategoryTheory.MonoidalCategory`,
  `Mathlib.CategoryTheory.Monoidal.Category`, including tensorIso and coherence.
- `def-weil-pbc-category-colimit`: `colimit`, `colimit.cocone`, `Cocone`,
  `IsColimit`, `Mathlib.CategoryTheory.Limits.HasLimits`; the canonical
  comparison is `PreservesCoproduct.iso` from
  `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`, whose inverse
  is sigmaComparison. Its source/docstrings and injection equations were read.
- `def-sfb-strong-monoidal-functor`: `Functor.CoreMonoidal`, its conversion
  to `Functor.Monoidal`, and `Monoidal.μIso`, `Monoidal.εIso`,
  `Mathlib.CategoryTheory.Monoidal.Functor`. These are equivalent presentations
  of the dependency's specified invertible tensorator and unit.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. This item needs its
  underlying cochain complexes, not localization or quasi-isomorphism hypotheses.
- `def-sfb-preserves-kflat-quasi-iso`: imported its recorded module
  `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`, read both
  `CochainComplex.IsKFlatForTotalTensor` and
  `Functor.PreservesTotalTensorKFlatQuasiIso`. This item uses the same
  Mathlib total tensor specified by that node; it imposes no K-flatness condition.
- `lem-sfb-total-tensor-homotopy`: imported the recorded
  `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal`;
  the needed declaration is `HomologicalComplex.monoidalCategory`. The
  homotopy descent instance is not needed for the complexes-only conclusion.
- Proof dependency `lem-sfb-termwise-strong-monoidal`: the recorded
  `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex` provides
  `Functor.mapCochainComplexμIso`, `mapCochainComplexεIso`, and their exact
  summand equations. Their full definitions/docstrings were read, together
  with `mapBifunctor.isColimitMapCofan`, `hom_ext_of_map` and
  `map_ιMapBifunctor_mapBifunctorComparisonX` in the upstream Bifunctor module.
  This import is public because its canonical isomorphisms appear in A's data.
- Proof dependency `lem-galois-equivalence-preserves-limits`:
  `Adjunction.isEquivalence_preservesColimits` and
  `Adjunction.isEquivalencePreservesLimits`,
  `Mathlib.CategoryTheory.Adjunction.Limits` (proof-only import).

Edge cases: all integer n have countable nonempty fibres, including negative n.
Negative p uses `Int.negOnePow`, not a natural-number exponent. Zero complexes,
zero summands and degree-zero single complexes use the same canonical total
construction. There are no nonzero assumptions or boundedness restrictions.
Identity functors/a give the original total comparison. Arbitrary a need not
respect tensor or unit, so no conclusion of monoidality for a was imposed.
No exactness or quasi-isomorphism preservation is assumed for Fi or Fs.

Source checked: `literature/stacks-project/homology.tex`,
`definition-associated-simple-complex` and `remark-triple-complex` (Tag 012Z),
including the explicit sign, unbounded direct sum and countable existence clause.
As the node states, the square-conjugation theorem is an agent calculation,
not a verbatim theorem of Stacks. The latest blueprint is not changed.

Searches actually run with the prescribed msearch wrapper:

- LeanFinder: “Conjugation of the tensor total comparison by an arbitrary
  natural isomorphism of a square of strong monoidal functors, on each
  bidegree coproduct injection”. Eight hits: generic localization comparison,
  tensor naturality and μNatIso; none states this full conjugation.
- Loogle: `Functor.mapCochainComplexμIso, HomologicalComplex.ιTensorObj`.
  Zero hits, with unknown-identifier note for the shortened upstream name;
  this is not evidence that the known upstream comparison is absent.
- Mathlib grep: `conjugat|mapCochainComplexμIso`, subdirectory Algebra/Homology:
  zero hits.
- LeanSearch: “Conjugation of tensor total complex comparison by a natural
  isomorphism, bidegree coproduct injection formula”. Eight hits, including
  `ιTensorObj`, `ιTotal` and total.mapIso; none is the required square theorem.
- rg in WeilConjectures and Sheaf for `conjugat|totalOplax|total_oplax`, then
  focused searches for `mapCochainComplexμIso`: existing canonical comparison
  and specialized consumers, no identical general square statement. Exact
  item-id grep in WeilConjectures returned no hits. The dependencies already
  carry all notions, so no new definition node or dependency repair is needed.

Validation: scompile.py compiled both the sandbox and the named library module cleanly
with no warnings. Every compiler call used the prescribed server wrapper.

## Second reading by Q09

Self-check with the node and complete module reopened; independent review is
performed by the maintainer as specified by the dispatch brief. The first
reading checked the five factors against their typed sources and targets;
the second checked each clause against the list above. The square's direction
is Fi followed by E1 to E0 followed by Fs, inverse a occurs at the total, and
all three inverse tensorators occur in the required orientation. The degree
index is all integers, and the second differential term keeps the negative
integer sign. Four preservation clauses are included, not merely Fi/Fs.
The unit j is the existing dependency's precise degree-zero-unit isomorphism.
No mathematical correction, missing clause, private copy or disputed statement
was found. Compiler repairs made the Fi preservation-instance argument explicit at uses
of the total helper. The main statements retain Fs preservation and strong
monoidality with explicit includes, since neither is needed in the helper
definition itself. This changes no mathematical assumption.
