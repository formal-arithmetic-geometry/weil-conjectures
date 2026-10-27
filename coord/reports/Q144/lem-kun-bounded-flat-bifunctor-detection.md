## Worker report

The module Sheaf.Paper.BoundedFlatBifunctorDetection states
AlgebraicGeometry.Etale.isIso_of_bounded_flat_test_pairs, with its sole proof `sorry`.
The natural-language statement, split, and dependency lists are unchanged. The source read
is the current blueprint lem-kun-0f1n.proof.md, paragraphs 2-4: first upper good
truncations, then bounded-above flat replacement in E alone, then stupid truncations.
The theorem docstring carries all seven steps of the node's expanded proof.

Clause-by-clause correspondence:

- Schemes U,V: `(U V : AlgebraicGeometry.Scheme.{u})`; arbitrary coefficient ring:
  `(Λ : Type (u + 1)) [CommRing Λ]`. These are exactly the size conventions of the
  recorded etale derived-category dependency; the target has independent universes uT,vT.
- D_U and D_V: `DerivedCategoryModule Λ U` and `DerivedCategoryModule Λ V`.
  Cochain representatives use `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`
  and the analogous category on V. Localization Q_U,Q_V is `DerivedCategory.Q.obj`.
- Triangulated target: `Category`, `Preadditive`, `HasZeroObject`, `HasShift T ℤ`,
  additivity of all shift functors, `Pretriangulated T`, and `IsTriangulated T`.
  These spell out the recorded Mathlib match of def-weil-triangulated-category.
- Countable coproducts in the target: `HasCountableCoproducts T`.
- Bifunctors A,B: curried functors
  `DerivedCategoryModule Λ U ⥤ DerivedCategoryModule Λ V ⥤ T`.
  Currying retains precisely functoriality on the product category.
- Specified exact-functor shift comparisons: `CommShift ℤ` on each `A.obj E`,
  `B.obj E`, `A.flip.obj F`, `B.flip.obj F`. Each partial functor is exact via its
  corresponding `IsTriangulated` instance. No cross-variable shift law is imposed.
- Separate countable coproduct preservation: four families of
  `PreservesColimitsOfShape (Discrete ℕ)` instances. Preservation of ℕ-indexed
  coproducts expresses countable coproduct preservation; smaller countable indexing
  types can be padded by zero objects, which exact partial functors preserve.
- Natural transformation: `(α : A ⟶ B)`. Shift compatibility for each fixed first
  input is `NatTrans.CommShift (α.app E) ℤ`, and for each fixed second input is
  `NatTrans.CommShift (α.flipApp F) ℤ`. The defining equation is
  chi_A followed by the shifted component equals the shifted-input component followed
  by chi_B, precisely the node's equation with Lean's left-to-right composition.
- Every bounded cochain complex P and R is quantified in hα. Each boundedness
  predicate is `∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)` (respectively R).
  Bounds depend on the complex and refer to terms, rather than cohomology.
- Flatness is required only for P: `∀ i : ℤ, exactFunctor _ _ (tensorRight (P.X i))`.
  The recorded flat-sheaf dependency explicitly exposes this existing predicate for
  the Sheaf(ModuleCat Λ) encoding, rather than the distinct SheafOfModules encoding.
  TensorRight is the canonical sheaf tensor over the constant coefficient ring.
- The test-pair component is
  `IsIso ((α.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj R))`.
- Conclusion: for every E in D_U and F in D_V,
  `IsIso ((α.app E).app F)`. There is no boundedness or flatness hypothesis on E,F.

Dependency declarations read and used:

- WeilConjectures.AlgebraicGeometry.DerivedCategories and its public dependency
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  AlgebraicGeometry.Etale.DerivedCategoryModule; localization is Mathlib's DerivedCategory.Q.
- Mathlib.CategoryTheory.Triangulated.Pretriangulated: CategoryTheory.Pretriangulated;
  Mathlib.CategoryTheory.Triangulated.Triangulated: CategoryTheory.IsTriangulated;
  Mathlib.CategoryTheory.Triangulated.Functor: Functor.IsTriangulated.
- Mathlib.CategoryTheory.Limits.HasLimits: colimit, as supplied by the countable coproduct
  API; Mathlib.CategoryTheory.Limits.Shapes.Countable: HasCountableCoproducts.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: SheafOfModules.IsFlatOnSite and its
  publicly exposed CategoryTheory.exactFunctor. The node's recorded note authorizes
  applying exactFunctor to the canonical tensorRight in the module-valued-sheaf encoding.
- Proof dependencies imported privately: Sheaf.CategoryTheory.TruncationsAndHomotopyColimits,
  Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit,
  Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit, Sheaf.Paper.BoundedFlatReplacement,
  Sheaf.AlgebraicGeometry.TruncationHomotopyColimit. The remaining proof dependencies are
  already in the public imports, including triangle-morphism two-out-of-three and Q.

Edge cases checked: the zero complex satisfies termwise boundedness with any ordered
bounds and has exact zero tensor functor. Empty intervals (a>b) are allowed and force
all terms to vanish. Bounds can be negative or positive. Neither zero coefficient ring
nor empty schemes are excluded. R need not be flat. No nonzero, torsion, Noetherian,
quasi-compactness, finite Tor-dimension or finite cohomological-dimension condition is added.
There are no node faults or disputed statements.

Searches (msearch.py, Q144, this item):

- leansearch: "Detect natural isomorphisms of exact coproduct preserving functors on
  sheaf derived categories by bounded complexes of flat sheaves". Eight hits, including
  PreservesCoproduct.iso and Functor.mapHomologicalComplexUpToQuasiIsoFactorsh. These
  concern coproduct comparisons and induced functors; none is this detection theorem.

- leanfinder: "A natural transformation of exact countable coproduct preserving bifunctors
  on derived categories of module sheaves is invertible if invertible on bounded flat
  complexes in the first variable and bounded complexes in the second". Eight hits,
  including Abelian.Ext.mapExactFunctor_hom and Functor.mapDerivedCategoryFactors;
  these concern Ext and induced functors, not this two-variable detection theorem.
- loogle: `DerivedCategory, "isIso"`. Seven hits, including isIso_Q_map_iff_quasiIso
  and isIso_iff; these test single morphisms or localization, not bounded test pairs.
- grep: `isIso.*bounded|bounded.*isIso|[Dd]evissage|flat.*generat` in Algebra/Homology:
  no hits. Direct rg in WeilConjectures and Sheaf for the node id and
  bounded-flat-bifunctor/detection patterns: no matches. Direct rg of the chosen
  declaration name in Mathlib, WeilConjectures, Sheaf, and the upstream names index:
  no matches. No existing declaration duplicates this statement.

Validation: scompile.py compiled the sandbox and library module modes cleanly under
60 seconds (10.2 s and 7.0 s). No error or unexpected warning was printed.

## Delivery context

The previous attempt reported that preflight treated an unchanged stage-2 item as an
unauthorized stage-1 re-split. The current node has a reviewed stage-1 split and no
Lean record. This packet changes only lean and adds its statement module and report;
it does not re-split the node or modify its reviewed mathematics.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
