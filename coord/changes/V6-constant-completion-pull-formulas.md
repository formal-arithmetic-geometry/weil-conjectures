# Derived scalar and finite-pullback representative formulas

## Reason

Profiling the assigned module found repeated normalization of composite complex functors
in two existing computation equations. In an isolated tail check, kernel checking of the
`derivedPullComparison` and `finitePull` witness definitions took 7.1 and 4.84 seconds.
Their long predicate arguments repeated the concrete conversions while selecting the
unique witnesses. Record the same equations with abstract ordinary and derived functors,
so the conversions are checked once with abstract objects and maps.

The new predicates introduce no assumption or proof hole. Unfolding them gives exactly
the original equations, including every map, representative, flatness hypothesis and
K-flatness hypothesis. The two theorems retain their existing holes. Their witness
definitions and all target statements are unchanged.

## Old

```lean
theorem derivedPullComparison_existsUnique (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃! δ : dres (coefficientMap J A I) ⋙ (derivedPull F V adj (constantMap F A)).functor ⟶
        (derivedPull F V adj (completedMap F A I)).functor ⋙ dres (coefficientMap J' A I),
      ∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        (derivedPull F V adj (constantMap F A)).functor.map
            ((resFactors (coefficientMap J A I)).inv.app P) ≫
          (derivedPull F V adj (constantMap F A)).comparison.app
            (((res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (Q (constant J' A)).map
            ((NatTrans.mapHomologicalComplex (ordinaryPullComparison F A I)
              (ComplexShape.up ℤ)).app P) =
        δ.app ((Q (completed J A I)).obj P) ≫
          (dres (coefficientMap J' A I)).map
            ((derivedPull F V adj (completedMap F A I)).comparison.app P) ≫
          (resFactors (coefficientMap J' A I)).inv.app
            (((pull F (completedMap F A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        := by
  sorry

theorem finitePull_existsUnique (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : (derivedPull F V adj (constantMap F A)).functor ⋙ extend (quotient J' A I n) ≅
        extend (quotient J A I n) ⋙
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor,
      ∀ P : Cx (constant J A), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        (extend (quotient J' A I n)).map
            ((derivedPull F V adj (constantMap F A)).comparison.app P) ≫
          (extendComparison (quotient J' A I n)).app
            (((pull F (constantMap F A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (Q (finite J' A I n)).map
            ((NatIso.mapHomologicalComplex (ordinaryFinitePull F V adj A I n)
              (ComplexShape.up ℤ)).hom.app P) =
        e.hom.app ((Q (constant J A)).obj P) ≫
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor.map
            ((extendComparison (quotient J A I n)).app P) ≫
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).comparison.app
            (((change (quotient J A I n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        := by
  sorry
```

## New

```lean
def DerivedPullComparisonFormula
    {M₀ M₁ M₂ M₃ D₀ D₁ D₂ D₃ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃]
    [Preadditive M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (q₀ : CochainComplex M₀ ℤ ⥤ D₀) (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    {dr : D₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃} {db : D₀ ⥤ D₂}
    (α : r.mapHomologicalComplex (.up ℤ) ⋙ q₁ ≅ q₀ ⋙ dr)
    (βp : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ⟶ b ⋙ s)
    (βb : q₀ ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (δ : s.mapHomologicalComplex (.up ℤ) ⋙ q₃ ≅ q₂ ⋙ ds)
    (e : dr ⋙ dp ⟶ db ⋙ ds) (P : CochainComplex M₀ ℤ) : Prop :=
  dp.map (α.inv.app P) ≫ βp.app ((r.mapHomologicalComplex (.up ℤ)).obj P) ≫
      q₃.map ((NatTrans.mapHomologicalComplex γ (.up ℤ)).app P) =
    e.app (q₀.obj P) ≫ ds.map (βb.app P) ≫
      δ.inv.app ((b.mapHomologicalComplex (.up ℤ)).obj P)

def FinitePullComparisonFormula
    {M₀ M₁ M₂ M₃ D₀ D₁ D₂ D₃ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃]
    [Preadditive M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (q₀ : CochainComplex M₀ ℤ ⥤ D₀) (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    {dr : D₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃} {db : D₀ ⥤ D₂}
    (α : q₀ ⋙ dr ⟶ r.mapHomologicalComplex (.up ℤ) ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s)
    (δ : q₀ ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (ε : q₂ ⋙ ds ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (e : dr ⋙ dp ≅ db ⋙ ds) (P : CochainComplex M₀ ℤ) : Prop :=
  dp.map (α.app P) ≫ β.app ((r.mapHomologicalComplex (.up ℤ)).obj P) ≫
      q₃.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app P) =
    e.hom.app (q₀.obj P) ≫ ds.map (δ.app P) ≫
      ε.app ((b.mapHomologicalComplex (.up ℤ)).obj P)

theorem derivedPullComparison_existsUnique (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃! δ : dres (coefficientMap J A I) ⋙ (derivedPull F V adj (constantMap F A)).functor ⟶
        (derivedPull F V adj (completedMap F A I)).functor ⋙ dres (coefficientMap J' A I),
      ∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        DerivedPullComparisonFormula (Q (completed J A I)) (Q (constant J A))
          (Q (completed J' A I)) (Q (constant J' A))
          (res (coefficientMap J A I)) (res (coefficientMap J' A I))
          (pull F (constantMap F A)) (pull F (completedMap F A I))
          (resFactors (coefficientMap J A I))
          (derivedPull F V adj (constantMap F A)).comparison
          (ordinaryPullComparison F A I)
          (derivedPull F V adj (completedMap F A I)).comparison
          (resFactors (coefficientMap J' A I)) δ P
        := by
  sorry

theorem finitePull_existsUnique (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : (derivedPull F V adj (constantMap F A)).functor ⋙ extend (quotient J' A I n) ≅
        extend (quotient J A I n) ⋙
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor,
      ∀ P : Cx (constant J A), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        FinitePullComparisonFormula (Q (constant J A)) (Q (constant J' A))
          (Q (finite J A I n)) (Q (finite J' A I n))
          (pull F (constantMap F A)) (pull F (constantMap F (A ⧸ I ^ (n + 1))))
          (change (quotient J' A I n)) (change (quotient J A I n))
          (derivedPull F V adj (constantMap F A)).comparison
          (extendComparison (quotient J' A I n)) (ordinaryFinitePull F V adj A I n)
          (extendComparison (quotient J A I n))
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).comparison e P
        := by
  sorry
```

## Users

A full Lean-source search finds each theorem used only by its corresponding witness
getter in this module. The getters' signatures and bodies remain identical. Every
later use of those getters therefore has the same interface and the same normalized
representative requirement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantCompletionEquivalence | V6 | The two witness getters select the same uniquely normalized comparisons. |

A standalone Lean conversion check applied each old theorem directly to the complete
new theorem type, with no rewriting. Both conversions compiled together in 9.4 seconds.
The new predicates are constructed definitions attached to the existing node
`lem-weil-pbc-constant-completion-equivalence`; they are no new mathematical obligations.
No external consumer needs adaptation and no adopted-source declaration is changed.

## Status

landed 20261020T230839-L-620015 2026-10-20 (merge of deliver/V6/Sheaf.Paper.ConstantCompletionEquivalence)
