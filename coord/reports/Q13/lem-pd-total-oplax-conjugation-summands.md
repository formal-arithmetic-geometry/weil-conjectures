## Worker report

The module `Sheaf.Algebra.Homology.TotalOplaxConjugationSummands` states
`CategoryTheory.Functor.total_oplax_conjugation_summands`. Its only postponed proof
is that theorem. Four concrete definitions package its coproduct clauses, ordinary
five-factor isomorphism, five-factor chain isomorphism, and bidegree component.
These are helpers of this node, not independent mathematical notions. No node
statement, dependency interface, or proof plan was changed; no new nodes are needed.
There was no repair note for this item.

Hypotheses and objects, clause by clause:

- The four categories are `A₀`, `A₁`, `B₀`, `B₁`, with eight independent explicitly
  declared object/morphism universe parameters. Their containing universe can be
  chosen above all eight; no equality of category universes is imposed.
- `[Abelian _]` supplies the abelian structures. `[MonoidalCategory _]` gives the
  specified tensor, unit, associator and unitors. `[MonoidalPreadditive _]` means
  tensor is additive in both variables. No braiding is assumed.
- All small colimits and their two-sided tensor preservation are used through
  `HasColimitsOfSize.{0,0}` and `PreservesColimitsOfSize.{0,0} (tensorLeft X)` /
  `tensorRight X` for each category. This is the established size convention of
  `lem-sfb-termwise-strong-monoidal` (Q66): the node's assumptions supply these
  instances; all integer degree fibres and the binary/triple/quadruple total
  constructions have universe-0 indexing. No category object or morphism universe
  is identified with zero. Larger containing universes therefore exclude no case.
- `E₀ : A₀ ⥤ B₀` and `E₁ : A₁ ⥤ B₁` have `.Additive`, `.Monoidal`, and
  `.IsEquivalence`. `Fi : A₀ ⥤ A₁` and `Fs : B₀ ⥤ B₁` have `.Additive` and
  `.Monoidal`. Countable coproduct preservation is `hFi`, `hFs`, each quantifying
  over `(J : Type) [Countable J]` and `PreservesColimitsOfShape (Discrete J)`.
  `hFsMonoidal` is explicitly included even though the five-factor conjugation
  does not use its tensorator. No exactness hypothesis is present.
- The arbitrary natural isomorphism is `a : Fi ⋙ E₁ ≅ E₀ ⋙ Fs` (Lean functor
  composition is in order of application). There is no monoidality instance for a.
- `CochainComplex _ ℤ` is unbounded. `mapHomologicalComplex (.up ℤ)` extends
  functors termwise, `NatIso.mapHomologicalComplex a (.up ℤ)` extends a termwise,
  and `ιTensorObj` is the actual signed total tensor injection. Tensor products
  use `HomologicalComplex.monoidalCategory` and its ordinary total constraints.

Constructions and conclusions, clause by clause:

- The ordinary inverse tensorator γ is `(Monoidal.μIso G M N).symm`, and ε is
  `(Monoidal.εIso G).symm`. The canonical T is
  `(G.mapCochainComplexμIso P Q).symm`; j is the dependency's
  `G.mapCochainComplexεIso.symm`, with its stated degree-zero / zero-object
  components. These are existing constructions, not newly chosen comparisons.
- `conjugatedOplaxTensorIso` is exactly the five-factor displayed formula for
  tilde-γ. Reading `≪≫` left to right: `Fs.mapIso (μIso E₀ M N)`, inverse a at
  `M ⊗ N`, E₁ of inverse μ for Fi, inverse μ for E₁, then `tensorIso` of a.
  Its type is `Fs(E₀M ⊗ E₀N) ≅ Fs(E₀M) ⊗ Fs(E₀N)`.
- `conjugatedTotalOplaxIso` is the same ordered five factors on complexes, using
  the actual `mapCochainComplexμIso` comparisons. Its type is the node's A, as
  an isomorphism of complexes, so its hom is already a chain map.
- The first theorem conjunct is `∀ n, Countable {pq : ℤ × ℤ // pq.1 + pq.2 = n}`.
  That fibre is a literal `Type 0`, hence small in any containing universe. There
  is no new smallness hypothesis on n or on a complex.
- The next four conjuncts are `totalOplaxCoproductAssertions` for E₀, E₁, Fi, Fs.
  Its first clause says `Nonempty (IsColimit (Cofan.mk ... (fun x ↦ G.map (ι...))))`
  for every complex pair and degree, precisely the image tensor-coproduct cocone.
  Its second clause supplies `IsIso (sigmaComparison G Z)` for every family on
  the fibre and the inverse formula `G.map (Sigma.ι Z x) ≫ inv κ = Sigma.ι _ x`.
  `sigmaComparison` is the canonical map induced by the images of injections;
  the existential proof is passed explicitly to `CategoryTheory.inv` to avoid
  a hidden local instance or a `let` in the statement.
- `conjugatedTotalOplaxComponent` is tilde-γ followed by the target injection.
  The next conjunct is `Fs.map (ιTensorObj ...) ≫ A.hom.f n = component` for
  every p,q,n and h : p+q=n. Lean composition is left to right, exactly reversing
  the typography of the node's right-to-left formula.
- The next conjunct gives ordinary naturality for arbitrary `f : M ⟶ M'` and
  `g : N ⟶ N'`: `Fs(E₀f ⊗ E₀g) ≫ b' = b ≫ (Hf ⊗ Hg)`, H=FsE₀.
- The next conjunct gives naturality of the actual A in arbitrary cochain maps
  f and g, using `⊗ₘ` and the termwise functors.
- The final conjunct is the signed chain equation on every summand. It says
  `component(p,q,n) ≫ d_target = Fs(E₀(dP) ▷ E₀Q) ≫ component(p+1,q,n+1)
  + p.negOnePow • (Fs(E₀P ◁ E₀(dQ)) ≫ component(p,q+1,n+1))`.
  Together with the explicitly stated ordinary naturality, its two terms are
  precisely the equations for `(dP,1)` and `(1,dQ)` with the second weighted by
  (-1)^p. The binders h₁,h₂ only express the forced integer index equalities;
  given p+q=n they always have proofs. They impose no boundedness restriction.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (normal monos/epis, finite products,
  kernels/cokernels, hence zero objects and biproducts).
- `def-sfb-monoidal-category`: `CategoryTheory.MonoidalCategory`,
  `Mathlib.CategoryTheory.Monoidal.Category`, including tensorIso and tensorHom.
- `def-weil-pbc-category-colimit`: `Limits.colimit`, `Cocone`, `IsColimit`,
  `colimit.desc`, `Mathlib.CategoryTheory.Limits.HasLimits`. The specialized
  `Cofan`, `sigmaComparison`, and coproduct injection interface are used directly.
- `def-sfb-strong-monoidal-functor`: `Functor.CoreMonoidal`, its `toMonoidal`,
  and the equivalent `Functor.Monoidal` with `Monoidal.μIso` / `εIso`, in
  `Mathlib.CategoryTheory.Monoidal.Functor`.
- `def-weil-abstract-derived-category`: the recorded `DerivedCategory`, Q and
  `HasDerivedCategory` were read in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  This node only uses the underlying cochain complexes and termwise functors,
  not localization or a derived-category instance; their module is publicly
  imported by the recorded K-flat dependency module.
- `def-sfb-preserves-kflat-quasi-iso`: read
  `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`, including
  `IsKFlatForTotalTensor` and `PreservesTotalTensorKFlatQuasiIso`; its specified
  binary tensor is the Mathlib tensor used here. No K-flatness is assumed.
- `lem-sfb-total-tensor-homotopy`: read its recorded
  `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal`; use
  `HomologicalComplex.monoidalCategory` for the ordinary complex constraints.
  Homotopy descent is not an additional hypothesis on this chain-level result.
- `lem-sfb-termwise-strong-monoidal`: read the entire recorded
  `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex` module and
  use `mapCochainComplexμIso`, its inverse, naturality, summand characterization,
  and `mapCochainComplexMonoidal`. Its unit is `mapCochainComplexεIso`.
- `lem-galois-equivalence-preserves-limits`: read and import
  `Adjunction.isEquivalence_preservesColimits` and `isEquivalencePreservesLimits`
  in `Mathlib.CategoryTheory.Adjunction.Limits`; the former supplies the
  equivalences' coproduct preservation automatically.
- Read the proof helpers `mapBifunctor.isColimitMapCofan`, `hom_ext_of_map`, and
  `map_ιMapBifunctor_mapBifunctorComparisonX` in
  `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor`, and `CochainComplex.ιTensorObj_d`
  in `WeilConjectures.Mathlib.Algebra.Homology.Monoidal`, including the integer sign.

Edge cases checked before writing: every integer n (including negative and zero)
has the countable infinite fibre parametrized by p ↦ (p,n-p); negative p uses
`Int.negOnePow`, not natural-number parity. Zero complexes and zero summands use
the same coproduct injections. Concentrated degree-zero complexes recover the
ordinary five factors. Identity functors and a=id reduce to the canonical tensor
comparisons; a nonmonoidal automorphism remains allowed. Unbounded complexes have
only two outgoing terms per summand, so no infinite sum of morphisms or exactness
assumption is introduced. Categories can have unrelated object/morphism universes.
No STATEMENT-DISPUTED issue or correction was found.

Searches performed:

- `msearch.py ... leanfinder`: “Conjugation of total tensor comparison of cochain
  complexes through an arbitrary natural isomorphism between composites of
  additive strong monoidal functors, evaluated on bidegree coproduct injections”.
  Eight hits, chiefly shift-comparison lemmas; none states this conjugation.
- `msearch.py ... loogle`: `HomologicalComplex.ιTensorObj, CategoryTheory.NatIso`
  yielded zero hits (NatIso is namespace syntax, not a standalone identifier).
  A corrected query `HomologicalComplex.ιTensorObj` yielded the injection and two
  unitor lemmas; none supplies the conjugation formula.
- `msearch.py ... grep`: `conjugat.*[Tt]ensor|[Tt]ensor.*conjugat|mapHomologicalComplex.*[Nn]at[Ii]so`
  yielded seven matches, including `NatIso.mapHomologicalComplex`, unrelated group
  homology, and adjunction conjugation; none is this statement.
- `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name
  index found no declaration named `total_oplax_conjugation_summands`,
  `conjugatedOplaxTensorIso`, or `totalOplaxCoproductAssertions`. The exact node-id
  search in `lean/WeilConjectures` found no module. Broader tensor/conjugation
  searches found other derived and adjunction comparisons, not this square.
- Read the current blueprint's Verdier-exchange unit under
  `literature/blueprint/latest/blueprint/sec-six-functors/` and the cited local
  Stacks homology source, definition-associated-simple-complex and following
  remark-triple-complex. The node identifies its five-step calculation as agent
  extraction, rather than a verbatim Stacks theorem.

Validation: scompile.py successfully compiled both the sandbox and the library module
with no errors or unexpected warnings. Final dry-run and
push results are recorded by the delivery wrapper. Every variable/universe is
explicit. No global build or direct git operation was run.

## Second reading by Q13

Self-audit against the node and source, not an independent agent review (the
assignment forbids starting agents; the maintainer performs independent review).
The first compile exposed that containing-universe colimit instances do not
implicitly shrink in the required tensor API; the module now follows the exact
universe-0 convention validated for its recorded termwise dependency. Checked all
five factors in application order, both endpoints, inverse directions, the arbitrary
a, all four preserved-coproduct clauses, ordinary and chain naturality, and the
negative-degree sign. A missing retained `Fs.Monoidal` section assumption was
repaired by explicitly including it. The canonical inverse uses an explicit
IsIso proof, avoiding a statement-local let. The theorem's proof is entirely sorry;
its docstring contains all five node proof steps and the dependency plan.
