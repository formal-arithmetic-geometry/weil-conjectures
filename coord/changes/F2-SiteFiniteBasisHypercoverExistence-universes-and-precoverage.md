# CategoryTheory.exists_site_finite_basis_hypercover

## Reason

The finite qcqs site has objects in `Type (u+1)` and morphisms in `Type u`.
The old `SmallCategory` binder equated these universes, preventing its intended application.
Allow independent object and morphism universes and take formal-family indices in their maximum.
The existing proof uses neither `HasIsos`, `IsStableUnderComposition`, nor
`IsStableUnderBaseChange`; remove those unused precoverage assumptions. A pretopology on
finite families does not imply the stronger arbitrary-cartesian-presieve base-change class:
isomorphic repetitions can make the indexing presieve infinite. The proof needs exactly
pullbacks, finite basis covers, and closure under adjoining a basis arrow.

Both changed modules were unclaimed when work began and remain unclaimed at this check.
They are changed under the launcher's 2026-10-12/14 unclaimed-module authorization.
This generalization specializes to the old API when the two universes agree. The conclusions
and the split-truncation invariant are identical under that specialization. No target
statement or definition appearing in a target statement changes. No other-group module is adapted.

## Old

```lean
theorem exists_site_finite_basis_hypercover
    {C : Type u} [SmallCategory C] [HasPullbacks C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange]
    (B : Set C)
    (hcover : ∀ T : C, ∃ (I : Type u) (U : I → C) (f : ∀ i : I, U i ⟶ T),
      Finite I ∧ (∀ i : I, U i ∈ B) ∧ Presieve.ofArrows U f ∈ J T)
    (hadjoin : ∀ (T : C) (I : Type u) [Finite I] (U : I → C)
      (f : ∀ i : I, U i ⟶ T), (∀ i : I, U i ∈ B) →
      Presieve.ofArrows U f ∈ J T → ∀ (V : C), V ∈ B → ∀ (g : V ⟶ T),
        Presieve.ofArrows U f ⊔ Presieve.singleton g ∈ J T)
    (T : C) :
    ∃ (K : SimplicialObject (FormalCoproduct.{u} (Over T)))
      (M : ∀ n : ℕ, Cone (K.properFaceDiagram n))
      (μ : ∀ n : ℕ, K _⦋n⦌ ⟶ (M n).pt),
      (∀ n : ℕ, Finite (K _⦋n⦌).I) ∧
      (∀ (n : ℕ) (i : (K _⦋n⦌).I), ((K _⦋n⦌).obj i).left ∈ B) ∧
      (M 0).pt = (FormalCoproduct.incl (Over T)).obj (Over.mk (𝟙 T)) ∧
      (∀ n : ℕ, Nonempty (IsLimit (M n))) ∧
      (∀ (n : ℕ) (a : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (M n).π.app (op a) = K.map a.obj.hom.op) ∧
      (∀ (n : ℕ) (j : (M n).pt.I),
        Presieve.ofArrows
          (fun i : {i : (K _⦋n⦌).I // (μ n).f i = j} ↦ ((K _⦋n⦌).obj i.val).left)
          (fun i : {i : (K _⦋n⦌).I // (μ n).f i = j} ↦
            ((μ n).φ i.val).left ≫
              eqToHom (congrArg (fun k ↦ ((M n).pt.obj k).left) i.property)) ∈
          J ((M n).pt.obj j).left)
```

## New

```lean
theorem exists_site_finite_basis_hypercover
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : Precoverage C)
    (B : Set C)
    (hcover : ∀ T : C, ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ T),
      Finite I ∧ (∀ i : I, U i ∈ B) ∧ Presieve.ofArrows U f ∈ J T)
    (hadjoin : ∀ (T : C) (I : Type (max u v)) [Finite I] (U : I → C)
      (f : ∀ i : I, U i ⟶ T), (∀ i : I, U i ∈ B) →
      Presieve.ofArrows U f ∈ J T → ∀ (V : C), V ∈ B → ∀ (g : V ⟶ T),
        Presieve.ofArrows U f ⊔ Presieve.singleton g ∈ J T)
    (T : C) :
    ∃ (K : SimplicialObject (FormalCoproduct.{max u v} (Over T)))
      (M : ∀ n : ℕ, Cone (K.properFaceDiagram n))
      (μ : ∀ n : ℕ, K _⦋n⦌ ⟶ (M n).pt),
      (∀ n : ℕ, Finite (K _⦋n⦌).I) ∧
      (∀ (n : ℕ) (i : (K _⦋n⦌).I), ((K _⦋n⦌).obj i).left ∈ B) ∧
      (M 0).pt = (FormalCoproduct.incl (Over T)).obj (Over.mk (𝟙 T)) ∧
      (∀ n : ℕ, Nonempty (IsLimit (M n))) ∧
      (∀ (n : ℕ) (a : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (M n).π.app (op a) = K.map a.obj.hom.op) ∧
      (∀ (n : ℕ) (j : (M n).pt.I),
        Presieve.ofArrows
          (fun i : {i : (K _⦋n⦌).I // (μ n).f i = j} ↦ ((K _⦋n⦌).obj i.val).left)
          (fun i : {i : (K _⦋n⦌).I // (μ n).f i = j} ↦
            ((μ n).φ i.val).left ≫
              eqToHom (congrArg (fun k ↦ ((M n).pt.obj k).left) i.property)) ∈
          J ((M n).pt.obj j).left)
```

The old proofs are retained, with the same mathematical construction and only the universe
annotations generalized. The existential choices in the compatible tower remain local to
the proof; no new data definitions are selected from an unproved existence assertion.

## Users

`tools/downstream.py Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence --uses exists_site_finite_basis_hypercover`
finds only the declaration itself and no pre-existing caller (the F2 item was sorry).
For the step module, `--uses IsFiniteBasisTruncation` likewise finds only that module and
the existence module. The full transitive importers are included below for completeness.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry | F2 | F2 item: new proof instantiates object universe u+1 and morphism universe u. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence | unclaimed | Generalized in this delivery; proof unchanged except universe annotations. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | B3 | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | F4 | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| TargetsCheck | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | No declaration mentions the changed invariant or theorem; proof-only transitive dependency. Signatures and definitions unchanged. |

## Status

landed 20261015T184347-L-858854 2026-10-15 (merge of deliver/F2/Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry)
