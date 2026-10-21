# CochainComplex.boundedProjectiveComplexDualPairing

## Reason

Preflight conservatively classifies the new section `variable` command and
`attribute [local instance] termRightDual` command as changes visible to importers.
Both serve private, proved helpers. The instance attribute is local to
`section Coordinates`, which ends before the public theorem. All new declarations
are private. No existing public signature, public import, instance, attribute,
notation, definition, or elaboration option changes. The additional source-library
import is private. This record documents that the consumer effect is empty.

## Old

```lean
theorem boundedProjectiveComplexDualPairing (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    [∀ n : ℤ, Module.Finite A (P.X n)] [∀ n : ℤ, Module.Projective A (P.X n)] :
    ∃ (D : CochainComplex (ModuleCat.{u} A) ℤ)
      (e : ∀ n : ℤ, D.X (-n) ≅ ModuleCat.of A (Module.Dual A (P.X n))),
      (∀ n m : ℤ, D.d (-n) (-m) =
        (e n).hom ≫ ModuleCat.ofHom ((-m).negOnePow • (P.d m n).hom.dualMap) ≫
          (e m).inv) ∧
      (∀ n : ℤ, n < -b ∨ -a < n → IsZero (D.X n)) ∧
      (∀ n : ℤ, Module.Finite A (D.X n) ∧ Module.Projective A (D.X n)) ∧
      ∃ (ε : D ⊗ P ⟶ 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ))
        (η : 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) ⟶ P ⊗ D),
        (∀ n : ℤ,
          HomologicalComplex.ιTensorObj D P (-n) n 0 (neg_add_cancel n) ≫ ε.f 0 ≫
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom =
            (e n).hom ▷ P.X n ≫
              ModuleCat.ofHom (LinearMap.finiteProjectiveEvaluation A (P.X n))) ∧
        (η.f 0 =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom ≫
            ∑ n ∈ Finset.Icc a b,
              ModuleCat.ofHom (LinearMap.finiteProjectiveCoevaluation A (P.X n)) ≫
                P.X n ◁ (e n).inv ≫
                  HomologicalComplex.ιTensorObj P D n (-n) 0 (add_neg_cancel n)) ∧
        (∀ n : ℤ, n ≠ 0 → ε.f n = 0 ∧ η.f n = 0) ∧
        ((λ_ P).inv ≫ η ▷ P ≫ (α_ P D P).hom ≫ P ◁ ε ≫ (ρ_ P).hom = 𝟙 P) ∧
        ((ρ_ D).inv ≫ D ◁ η ≫ (α_ D P D).inv ≫ ε ▷ D ≫ (λ_ D).hom = 𝟙 D)
```

The body was `by sorry`; no coordinate helpers or section-local instance existed.

## New

```lean
theorem boundedProjectiveComplexDualPairing (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    [∀ n : ℤ, Module.Finite A (P.X n)] [∀ n : ℤ, Module.Projective A (P.X n)] :
    ∃ (D : CochainComplex (ModuleCat.{u} A) ℤ)
      (e : ∀ n : ℤ, D.X (-n) ≅ ModuleCat.of A (Module.Dual A (P.X n))),
      (∀ n m : ℤ, D.d (-n) (-m) =
        (e n).hom ≫ ModuleCat.ofHom ((-m).negOnePow • (P.d m n).hom.dualMap) ≫
          (e m).inv) ∧
      (∀ n : ℤ, n < -b ∨ -a < n → IsZero (D.X n)) ∧
      (∀ n : ℤ, Module.Finite A (D.X n) ∧ Module.Projective A (D.X n)) ∧
      ∃ (ε : D ⊗ P ⟶ 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ))
        (η : 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) ⟶ P ⊗ D),
        (∀ n : ℤ,
          HomologicalComplex.ιTensorObj D P (-n) n 0 (neg_add_cancel n) ≫ ε.f 0 ≫
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom =
            (e n).hom ▷ P.X n ≫
              ModuleCat.ofHom (LinearMap.finiteProjectiveEvaluation A (P.X n))) ∧
        (η.f 0 =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom ≫
            ∑ n ∈ Finset.Icc a b,
              ModuleCat.ofHom (LinearMap.finiteProjectiveCoevaluation A (P.X n)) ≫
                P.X n ◁ (e n).inv ≫
                  HomologicalComplex.ιTensorObj P D n (-n) 0 (add_neg_cancel n)) ∧
        (∀ n : ℤ, n ≠ 0 → ε.f n = 0 ∧ η.f n = 0) ∧
        ((λ_ P).inv ≫ η ▷ P ≫ (α_ P D P).hom ≫ P ◁ ε ≫ (ρ_ P).hom = 𝟙 P) ∧
        ((ρ_ D).inv ≫ D ◁ η ≫ (α_ D P D).inv ≫ ε ▷ D ≫ (λ_ D).hom = 𝟙 D)
```

The body is proved from the finite projective module pairing and the existing
source complex-dual API. Private helpers install the canonical termwise right dual,
identify mates with ordinary dual maps, and identify degree coordinates. The data
fields of the pairing are explicit evaluation and coevaluation linear maps;
the imported module theorem supplies only their proof fields.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Transitive importer; public API unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Transitive importer; public API unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Transitive importer; public API unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | Transitive importer; public API unchanged; no adaptation needed. |
| Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect | K7 | Sole direct importer; public API unchanged; no adaptation needed. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Transitive importer; public API unchanged; no adaptation needed. |

No downstream module uses a new declaration because they are all private.
No target statement or definition used by a target changes meaning.

## Status

landed 20261021T111301-L-69781 2026-10-21 (merge of deliver/K9/Sheaf.Algebra.Homology.BoundedProjectiveComplexDualPairing)
