# PointFiniteSourceConstraints and PointIntegralTensorScalarSquare

## Reason

The finite and integral stage lemmas must mention these predicates without importing
the assembly theorem, which imports those lemmas. Move the two existing declarations
verbatim into PointFibreDerivedTensorCompatibility and publicly re-export that module
from PointFibreDerivedTensor. Names, universes, signatures, data and visibility are
unchanged. Only the owning blueprint docstring tags change. No target meaning changes.

## Old

In `lean/Sheaf/Paper/PointFibreDerivedTensor.lean`:

```lean
def PointFiniteSourceConstraints
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (S : PointFiniteTensorData D l E n) : Prop :=
  letI := (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal
  ∃ J : @Functor.Monoidal _ _ S.monoidal _ _
      (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        (Spec (.of D.k))).ι,
    (∀ X Y, HEq
      (@Functor.LaxMonoidal.μ _ _ S.monoidal _ _ _ _ J.toLaxMonoidal X Y)
      (eqToHom (congrArg (fun G ↦ G.obj (X, Y)) S.tensor_eq).symm)) ∧
    HEq (@Functor.LaxMonoidal.ε _ _ S.monoidal _ _ _ _ J.toLaxMonoidal)
      (eqToHom S.unit_eq.symm)

def PointIntegralTensorScalarSquare
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (C₁ : PointIntegralTensorCanonical D l hl E I₁)
    (C₂ : PointIntegralTensorCanonical D l hl L I₂) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (p q : ℤ)
    (a b : (completedIntegralCommRingSheafUnrestricted l L
      (Spec (.of D.k))).obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (x : (P.obj.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (y : (Q.obj.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))),
    ((C₂.completion
      ⟨_, scalarGood l E L ι (Spec (.of D.k)) P⟩
      ⟨_, scalarGood l E L ι (Spec (.of D.k)) Q⟩).f (p + q))
      ((HomologicalComplex.ιTensorObj
        ((pointIntegralComplexSections D l L).obj
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P.obj))
        ((pointIntegralComplexSections D l L).obj
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q.obj)) p q (p + q) rfl).hom
        (integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (P.obj.X p)
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) a x ⊗ₜ[
            ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l L)]
          integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (Q.obj.X q)
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) b y)) =
    ((scalarTensorChain l E L ι (Spec (.of D.k)) P.obj Q.obj).f (p + q)).val.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))
      (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
        (((integralOperationsTensorComplexFunctor l E (Spec (.of D.k))).obj
          (P.obj, Q.obj)).X (p + q))
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) (a * b)
        (((C₁.completion P Q).f (p + q))
          ((HomologicalComplex.ιTensorObj
            ((pointIntegralComplexSections D l E).obj P.obj)
            ((pointIntegralComplexSections D l E).obj Q.obj) p q (p + q) rfl).hom
            (x ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)] y))))
```

## New

The exact same declarations, now in
`lean/Sheaf/Paper/PointFibreDerivedTensorCompatibility.lean`:

```lean
def PointFiniteSourceConstraints
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (S : PointFiniteTensorData D l E n) : Prop :=
  letI := (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal
  ∃ J : @Functor.Monoidal _ _ S.monoidal _ _
      (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        (Spec (.of D.k))).ι,
    (∀ X Y, HEq
      (@Functor.LaxMonoidal.μ _ _ S.monoidal _ _ _ _ J.toLaxMonoidal X Y)
      (eqToHom (congrArg (fun G ↦ G.obj (X, Y)) S.tensor_eq).symm)) ∧
    HEq (@Functor.LaxMonoidal.ε _ _ S.monoidal _ _ _ _ J.toLaxMonoidal)
      (eqToHom S.unit_eq.symm)

def PointIntegralTensorScalarSquare
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (C₁ : PointIntegralTensorCanonical D l hl E I₁)
    (C₂ : PointIntegralTensorCanonical D l hl L I₂) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (p q : ℤ)
    (a b : (completedIntegralCommRingSheafUnrestricted l L
      (Spec (.of D.k))).obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (x : (P.obj.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (y : (Q.obj.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))),
    ((C₂.completion
      ⟨_, scalarGood l E L ι (Spec (.of D.k)) P⟩
      ⟨_, scalarGood l E L ι (Spec (.of D.k)) Q⟩).f (p + q))
      ((HomologicalComplex.ιTensorObj
        ((pointIntegralComplexSections D l L).obj
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P.obj))
        ((pointIntegralComplexSections D l L).obj
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q.obj)) p q (p + q) rfl).hom
        (integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (P.obj.X p)
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) a x ⊗ₜ[
            ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l L)]
          integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (Q.obj.X q)
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) b y)) =
    ((scalarTensorChain l E L ι (Spec (.of D.k)) P.obj Q.obj).f (p + q)).val.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))
      (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
        (((integralOperationsTensorComplexFunctor l E (Spec (.of D.k))).obj
          (P.obj, Q.obj)).X (p + q))
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) (a * b)
        (((C₁.completion P Q).f (p + q))
          ((HomologicalComplex.ιTensorObj
            ((pointIntegralComplexSections D l E).obj P.obj)
            ((pointIntegralComplexSections D l E).obj Q.obj) p q (p + q) rfl).hom
            (x ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)] y))))
```

The old module adds `public import Sheaf.Paper.PointFibreDerivedTensorCompatibility`.
The original node retains the canonical-system structure and theorem; the two
relocated predicates have definition nodes recording their unchanged meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointFibreDerivedTensor | S7 | Publicly re-exports both unchanged definitions; assembly uses the stage lemmas. |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | Only downstream importer reported by downstream.py; declarations remain available under the same names; no edit required. |

No forced adaptations and no source-library edits. The new modules use the public
compatibility import to avoid an import cycle.

## Status

landed 20261021T182521-L-1212342 2026-10-21 (merge of deliver/S7/Sheaf.Paper.PointFibreDerivedTensor)
