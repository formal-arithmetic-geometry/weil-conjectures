## Worker report

Stage 2 only. The live node has N8's reviewed stage-1 split, merged at 05:02 UTC
on 2026-10-22, and no Lean record. This delivery preserves that split and every
non-Lean field. The former worker's superseded-stage-1 diagnosis does not apply
to writing the missing stage-2 statement.

Module: `Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`.
Declarations: `CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_forget_properties`
and `CategoryTheory.Endofunctor.IsoAlgebra.exists_fixedPairDerivedForgetComparison`.
Both proofs are `sorry`. There are no new definitions, additional nodes,
dependency repairs, statement corrections, or statement disputes.

Hypotheses and clauses, checked against the whole node and its twelve proof steps:

- Grothendieck abelian C and D are `Category.{vC} C`, `Abelian C`,
  `IsGrothendieckAbelian.{vC} C` and their D counterparts. Object universes uC,
  uD, morphism universes vC, vD, and four localization universes wC, wD, wF,
  wH are explicit and independent. `HasDerivedCategory` binders choose the
  ordinary localizations specified by def-weil-abstract-derived-category;
  they are always available at the standard sizes and impose no geometric
  condition or identification of universes.
- The additive autoequivalences are `F : C ⥤ C`, `F.Additive`,
  `F.IsEquivalence`, and likewise H. `IsoAlgebra F` is definitionally the full
  subcategory `(Algebra.IsIsoStr F).FullSubcategory` of the recorded
  `Endofunctor.Algebra F`. Its carrier, invertible structure map and commuting
  morphisms are precisely the dependency's pairs. `forget F` is its prescribed
  inclusion followed by `Algebra.forget F`. No new fixed-pair category is made.
- `IsGrothendieckAbelian (IsoAlgebra F)` is the first structural conclusion.
  Its `Abelian` structure is the existing upstream `IsoAlgebra.abelian`
  instance for the exact additive autoequivalence. Apply the same structural
  declaration with `(D,H)` for the second fixed-pair category.
- Exactness of U_F is `PreservesFiniteLimits (forget F)` and
  `PreservesFiniteColimits (forget F)`; conservativity is
  `(forget F).ReflectsIsomorphisms`.
- The free left adjoint is the actual upstream `Free.functor F`; its
  adjunction is `Nonempty (Free.functor F ⊣ forget F)` and exactness is the
  pair of finite-limit/finite-colimit preservation clauses. This does not
  substitute an arbitrary unspecified left adjoint for the construction.
- Its underlying object is explicitly equated with `∐ (Free.obj F M)`.
  Reading `Free.posObj`, `negObj` and `obj` shows these are all integer
  powers, using `F.inv` for negative powers. `Free.objSucc` uses the
  equivalence counit in negative degrees. The next clause specifies its
  structure on every summand:
  `F.map (Sigma.ι ... n) ≫ str.hom = objSucc.hom ≫ Sigma.ι ... (n + 1)`.
- Preservation of injectives and of K-injectives is asserted by the existing
  `Functor.PreservesInjectiveObjects` and `PreservesKInjectiveComplexes`.
  The latter's field maps `CochainComplex.IsKInjective` objects to such
  objects; Mathlib's IsKInjective is exactly null-homotopy of every chain
  map from an acyclic complex, with no boundedness restriction.
- The last structural clause is
  `(forget F).mapDerivedCategory.ReflectsIsomorphisms`: conservativity on
  ordinary unbounded derived categories, rather than the category of
  fixed pairs formed after localization.
- L is `L : C ⥤ D`, `L.Additive`, `PreservesFiniteLimits L`. The datum
  `e : L ⋙ H ≅ F ⋙ L` has component `H(LM) ≅ L(FM)`, as required.
  The already defined `mapOfNatIso e` transports the carrier to LM and
  the structure map to `e.hom.app M ≫ L.map θ.hom`; on morphisms it is
  L.map. Read Algebra.mapOfNatTrans and IsoAlgebra.mapOfNatIso in full.
  Its additive and left-exact instances are existing upstream instances.
- The comparison is an isomorphism of functors on the entire ordinary
  derived category:
  `R(mapOfNatIso e) ⋙ D(forget H) ≅ D(forget F) ⋙ R(L)`.
  Lean's composition order is left to right, so this is the node's displayed
  `D(U_H) R(L̃) ≅ R(L) D(U_F)`.
- R and its units are specifically the dependency's recorded
  `rightDerivedFunctorOfQuasiIsoResolutions` and
  `rightDerivedFunctorOfQuasiIsoResolutionsUnit`. The hF and hC variables
  are universally quantified proofs of enough K-injectives, in the
  theorem's conclusion. They do not add a hypothesis about the categories
  or an arbitrary candidate derived functor. Their existence follows from
  the Grothendieck conclusions, `kInjectiveResolutionFunctor`,
  `toKInjectiveResolution`, and `monoQuasiIso_toKInjectiveResolution_app`:
  take I to be that functor's value and s the component of that natural
  transformation. The supplied upstream instance establishes K-injectivity.
  Monicity of this particular available witness is not required by hF/hC.
- The comparison is canonical: `∃! α` whose hom identifies the two units.
  On the left, apply D(U_H) to η_L̃, then α, then apply RL to the canonical
  factorization `Qh D(U_F) ≅ U_F,K Qh`. On the right, use
  `mapDerivedCategoryFactorsh` for U_H, the homotopy comparison induced by
  `mapOfNatIsoCompForgetIso e`, the inverse composition comparison for
  U_F and L, and η_L at U_F,K(K). Both are maps with the same source and
  target. Thus the equality controls actual maps. This is the canonical
  unit-compatible comparison described by the source and def-sfb's
  universal property, written for arbitrary homotopy objects to specify
  canonicity. Evaluate at
  `(HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor _ 0).obj M)`
  to obtain exactly the node's M[0] clause; the ordinary single-degree
  identifications are `mapDerivedCategorySingleFunctor 0` and
  `DerivedCategory.singleFunctorIsoCompQ`. The source's common-resolution
  computation proves this normalization on every K (node step 12).

Dependency declarations read and reused:

- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`:
  `CategoryTheory.IsGrothendieckAbelian`, `hasLimits`, `hasColimits`,
  and `ab4OfSize`; the class was read at lines 60-109.
- `Mathlib.CategoryTheory.Endofunctor.Algebra`: `Endofunctor.Algebra`,
  `Algebra.Hom` (its full commuting equation), and `Algebra.forget`.
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`:
  `Algebra.IsIsoStr`, `IsoAlgebra`, `carrier`, `str`, `forget`,
  `Algebra.mapOfNatTrans`, `IsoAlgebra.mapOfNatIso`.
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor`:
  `IsoAlgebra.abelian`, the additive and exact forgetful instances and
  additive transport instance. This uses the recorded fixed-pair
  dependency's exact full subcategory, not an alternative representation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `Q`, `Qh`, and single-degree identifications.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the recorded functor, unit, universal property, unit-compatible unique
  isomorphism, and K-injective computation declarations, read in full.
- Source construction `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra`:
  Free's complete construction through `adjunction` and
  `isGrothendieckAbelian`, and `mapOfNatIsoCompForgetIso`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra`:
  `Free.preservesHomology_functor`, `preservesKInjectiveComplexes_forget`,
  `rightDerivedFunctorMapOfNatIsoCompForgetIso`, read in full. This supplies
  the existing comparison for the upstream chosen right-derived models;
  our statement also supplies the unit equation for the recorded models.
- Proof interfaces: `Adjunction.preservesKInjectiveComplexes` in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`;
  `Adjunction.map_injective` and `Functor.PreservesInjectiveObjects` in
  Mathlib's Preadditive.Injective.Basic/Preserves;
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactorsh`, and
  `mapDerivedCategorySingleFunctor` in Mathlib's DerivedCategory.ExactFunctor;
  `DerivedCategory.isIso_iff` in DerivedCategory.HomologySequence;
  `CochainComplex.IsKInjective.Qh_map_bijective` in DerivedCategory.KInjective;
  the four recorded functorial replacement declarations in
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`;
  `exists_rightDerived_of_enough_isKInjective` in
  `Sheaf.CategoryTheory.KInjectiveTotalDerived`. Also read the two
  `Adjunction.isEquivalencePreservesLimits`/`isEquivalence_preservesColimits`
  signatures named by the equivalence-preservation node.

Edge cases checked mathematically: the zero category and zero complexes cause
no exceptions; F = identity on Ab gives the free direct sum indexed by all
integers and the usual invertible-operator forgetful functor. The n = 0
summand is M itself; n = -1 uses the equivalence counit and shifts to n = 0.
No boundedness or injectivity of individual terms is substituted for
K-injectivity. No assumption that forgetting detects K-injectivity appears.
Identity L and identity e retain the unit normalization. The M[0] equation
holds also for M = 0. Independent object, morphism and localization universes
are retained, including small categories and large categories with small Homs.

Searches actually run:

- msearch LeanFinder: “For an additive autoequivalence of a Grothendieck
  abelian category the forgetful functor from fixed pairs is exact,
  preserves K-injective complexes, and commutes with right derived functors”.
  Eight hits about exact derived functors and Ext; no full fixed-pair theorem.
- msearch Loogle: `CategoryTheory.Endofunctor.IsoAlgebra, CategoryTheory.Functor.rightDerivedFunctor`.
  Zero hits; the service reports IsoAlgebra as an unknown identifier (it
  searches Mathlib, whereas this declaration is upstream).
- msearch grep: `IsoAlgebra|PreservesInjectiveObjects` in
  `CategoryTheory/Endofunctor`: zero hits in Mathlib.
- msearch LeanSearch: “The forgetful functor from fixed pairs for an
  autoequivalence preserves injectives and commutes with total right
  derivation”. Eight hits including Functor.injective_obj,
  preservesInjectiveObjects_of_isEquivalence and injective-object facts;
  no full theorem.
- rg on `lean/WeilConjectures` and `lean/Sheaf`, by this node ID and
  `rightDerivedFunctorMapOfNatIsoCompForgetIso`, `mapOfNatIsoCompForget`,
  `fixed.pair`, `IsoAlgebra`, and the proposed new declaration names.
  This locates the upstream constructions and object comparison above;
  no declaration states the whole node together with its unit equation.
  In particular FixedPairTruncationCohomology concerns pairs formed in
  the derived category and cannot replace this statement.

Validation: prescribed scompile.py compiled the module both in its private
sandbox and at its declared library module path (8.3 and 8.6 seconds), exit 0,
with no errors or unexpected warnings. autoImplicit is false; no diagnostics,
local notation, private constructions or local instances are left in the file.
The exact main signature is copied into lean.statement, and both declarations
are listed in lean.declarations. The maintainer supplies the independent review.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
