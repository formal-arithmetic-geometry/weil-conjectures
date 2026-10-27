# AlgebraicGeometry.ProEtale.CondensedRing.ModuleObjectDerivedTensorFormula

## Reason

The identical total-complex normalization was elaborated once for arbitrary additive
monoidal functors and again for concrete pro-etale modules. Factor that expression into
`tensorRepresentativeFormula` and specialize it. The quantified complexes, summand
normalization, and derived counit equation are unchanged. The former explicit tensor
existence instances and the synthesized ones are proofs of the same propositions, so
proof irrelevance identifies them. This makes the definition usable without repeatedly
elaborating its expanded derived tensor term.

## Old

```lean
def ModuleObjectDerivedTensorFormula
    (μ : Functor.leftDerivedDerivedTensor (upperStar Λ f) ⟶
      Functor.derivedTensorLeftDerived (upperStar Λ f)) : Prop :=
  letI : HasColimitsOfSize.{0, 0}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    Mod.hasColimitsOfSize
  letI : HasColimitsOfSize.{0, 0}
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
    Mod.hasColimitsOfSize
  letI : ∀ K P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ,
      HomologicalComplex.HasTensor K P :=
    fun _K _P _n ↦ @HasColimitsOfShape.has_colimit _ _ _ _
      (HasColimitsOfSize.has_colimits_of_shape _) _
  letI : ∀ K P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ,
      HomologicalComplex.HasTensor K P :=
    fun _K _P _n ↦ @HasColimitsOfShape.has_colimit _ _ _ _
      (HasColimitsOfSize.has_colimits_of_shape _) _
  ∀ K P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ,
    ∃ q : ((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj K P) ⟶
        HomologicalComplex.tensorObj
          (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj K)
          (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (i j n : ℤ) (h : i + j = n),
        ∃ b : (upperStar Λ f).obj (K.X i ⊗ P.X j) ⟶
            (upperStar Λ f).obj (K.X i) ⊗ (upperStar Λ f).obj (P.X j),
          ModuleObjectTensorGeneratorFormula Λ f (K.X i) (P.X j) b ∧
          (upperStar Λ f).map (HomologicalComplex.ιTensorObj K P i j n h) ≫ q.f n =
            b ≫ HomologicalComplex.ιTensorObj
              (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj K)
              (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) i j n h) ∧
      (μ.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj P) ≫
          ((Functor.derivedTensorLeftDerivedCounit (upperStar Λ f)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        ((Functor.leftDerivedDerivedTensorCounit (upperStar Λ f)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫ DerivedCategory.Q.map q
```

## New

```lean
def ModuleObjectDerivedTensorFormula
    (μ : Functor.leftDerivedDerivedTensor (upperStar Λ f) ⟶
      Functor.derivedTensorLeftDerived (upperStar Λ f)) : Prop :=
  tensorRepresentativeFormula (upperStar Λ f) (ModuleObjectTensorGeneratorFormula Λ f) μ
```

`tensorRepresentativeFormula` is the former private `abstractTensorFormula`, with the
same body and generic category hypotheses. It is now public because a public definition
uses it. It is recorded with the existing helper node. No quantified condition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalLocalizingProjectionFormula | P5 | Identical predicate factored through the generic formula; proofs use it by reduction. |

`tools/downstream.py Sheaf.Paper.RationalLocalizingProjectionFormula --uses
ModuleObjectDerivedTensorFormula` lists this module alone. Indirect target uses retain
the same predicate and canonical comparison; this definition change is submitted for
independent statement review.

## Status

landed 20261025T143725-L-1079163 2026-10-25 (merge of deliver/P5/Sheaf.Paper.RationalLocalizingProjectionFormula)
