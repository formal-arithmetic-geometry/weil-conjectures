# AlgebraicGeometry.ProEtaleWeilSheaf.NativeAdjunctionNormalization

## Reason

The former extra scalar (-1)^(p*q) is incompatible with the native row-sign Hom
complex. Its differential is (-1)^p(d_I f - f d_P), while the tensor total is
ordered (P,Q), with differential d_P + (-1)^p d_Q and value Q^q tensor P^p.
Direct uncurrying is therefore unsigned. The previous E1 delivery recorded a
counterexample using two contractible disks; this repair follows that diagnosis.

In characteristic zero take P to be the coefficient unit in degree 1, Q the
contractible unit disk in degrees 0 and 1, and I the contractible tensor-unit disk
in degrees 1 and 2. The native Hom differential is minus the identity. If c is the
transpose of the identity, the map phi has components c and -c. The old formula
forces both components of psi to be the identity, contradicting the chain-map
square (tensor differential -id, target differential id). The corrected formula
has components id and -id, which satisfy that square. Both disks are contractible,
so K-flatness and K-injectivity do not avoid the counterexample.

The proved source lemma
`CochainComplex.ιTensorObj_internalHomEquiv_symm_f` in
`WeilConjectures/Algebra/Homology/InternalHom.lean` independently gives unsigned
uncurrying for degree-zero maps with this row-sign convention. Its cochain formula
has the factor (-1)^(p*n), where n is the degree of the cochain, not the input
complex degree q. Here n=0. Edge checks: degree-zero or even parity inputs agree
with the old formula; odd/odd inputs remove the erroneous second sign; zero
objects and empty summands still give zero maps.
The correction changes no target text and requires renewed statement review for
targets whose definitions reach this normalization. The Koszul factor in the
separate signed-swap assertion is retained.

## Old

```lean
def NativeAdjunctionNormalization
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasCountableCoproducts A] [HasDerivedCategory.{b} A]
    (H₀ : Aᵒᵖ ⥤ A ⥤ A) [H₀.Additive] [∀ P, (H₀.obj P).Additive]
    (T : A ⥤ A ⥤ A) [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : ∀ P, T.obj P ⊣ H₀.obj (op P))
    (H : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (R : NativeHomRepresentatives H₀ H) (S : CoefficientClosedStructure H)
    (flat : CochainComplex A ℤ → Prop)
    (model : ∀ P Q : CochainComplex A ℤ, flat P →
      (S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor P Q T))) : Prop :=
  ∀ (P Q I : CochainComplex A ℤ) (hP : flat P) (_hQ : flat Q)
    (hI : I.IsKInjective) (φ : Q ⟶ CochainComplex.bifunctorHomObj H₀ P I),
    ∃ ψ : CochainComplex.mapBifunctor P Q T ⟶ I,
      (∀ (p q n : ℤ) (hpq : p + q = n),
        HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq ≫ ψ.f n =
          (p * q).negOnePow •
            ((T.obj (P.X p)).map (φ.f q ≫
                CochainComplex.bifunctorHomπ H₀ P I q p n hpq) ≫
              (adj (P.X p)).counit.app (I.X n))) ∧
      (model P Q hP).hom ≫ DerivedCategory.Q.map ψ =
        (S.transpose (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj I)).symm
            (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv)
```

## New

```lean
def NativeAdjunctionNormalization
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasCountableCoproducts A] [HasDerivedCategory.{b} A]
    (H₀ : Aᵒᵖ ⥤ A ⥤ A) [H₀.Additive] [∀ P, (H₀.obj P).Additive]
    (T : A ⥤ A ⥤ A) [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : ∀ P, T.obj P ⊣ H₀.obj (op P))
    (H : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (R : NativeHomRepresentatives H₀ H) (S : CoefficientClosedStructure H)
    (flat : CochainComplex A ℤ → Prop)
    (model : ∀ P Q : CochainComplex A ℤ, flat P →
      (S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor P Q T))) : Prop :=
  ∀ (P Q I : CochainComplex A ℤ) (hP : flat P) (_hQ : flat Q)
    (hI : I.IsKInjective) (φ : Q ⟶ CochainComplex.bifunctorHomObj H₀ P I),
    ∃ ψ : CochainComplex.mapBifunctor P Q T ⟶ I,
      (∀ (p q n : ℤ) (hpq : p + q = n),
        HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq ≫ ψ.f n =
          (T.obj (P.X p)).map (φ.f q ≫
              CochainComplex.bifunctorHomπ H₀ P I q p n hpq) ≫
            (adj (P.X p)).counit.app (I.X n)) ∧
      (model P Q hP).hom ≫ DerivedCategory.Q.map ψ =
        (S.transpose (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj I)).symm
            (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeWeilClosedForgetful | R4 | Corrects the normalization used by NativeOrdinaryTensorModels and thus the existential comparison assertion. |
| Sheaf.Paper.DerivedWeilOperations | U4 | Inherits corrected normalization through NativeClosedComparison; no use of the removed scalar and no source edit required. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed | Inherits corrected normalization through NativeClosedComparison; no use of the removed scalar and no source edit required. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed | Inherits corrected normalization through NativeClosedComparison; no use of the removed scalar and no source edit required. |
| Sheaf.Paper.NativeOpenDerivedTensor | unclaimed | Inherits corrected normalization through NativeClosedComparison; no use of the removed scalar and no source edit required. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed at audit | Uses canonical uncurrying from the closed structure; no use of the removed scalar and no source edit required. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed at audit | Uses the native compact tensor comparison; no use of the removed scalar and no source edit required. |
| Sheaf.Paper.WeilGeometricHomConstructibility | T8 | Inherits corrected normalization through NativeClosedComparison; no use of the removed scalar and no source edit required. |

## Status

landed 20261025T005410-L-3479801 2026-10-25 (merge of deliver/R4/Sheaf.Paper.NativeWeilClosedForgetful)
