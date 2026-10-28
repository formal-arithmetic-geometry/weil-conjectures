# completed_tensor_common_lift_constraints_associative

## Reason

The existing STATEMENT-DISPUTED warning identifies a real normalization gap:
CompletedTensorCommonLiftTensorUnit stores an arbitrary natural tensor isomorphism
and an unrelated unit comparison. Neither field is related to the finite models.
Naturality and invertibility do not imply an associativity equation. For example,
on rational graded lines let the binary comparison have scalar -1 at the degree
pair (1,0) and scalar 1 elsewhere. It is natural and invertible. At degrees (1,0,0)
the left associativity path has scalar 1 and the right path has scalar -1.
The private example in the item formalizes this generic obstruction. It does not
instantiate the entire scheme/realization context of the old theorem.

BS Remark 6.8.15 concerns the actual tensor functors; HRS Lemma 7.9 concerns the
natural finite-field colimit equivalences. Neither source asserts coherence of
arbitrary tensorators. Require the component equality to the existing explicit
completedTensorCommonComponent construction. Prove existence of tensor/unit data
with exactly that equality by rebuilding the existing component construction and
retaining its definitional equation. This adds no new existence assumption.

The constraint wrapper now returns data and its constraints existentially. Its
sole consumer needs precisely this existence statement and keeps its original
signature and fields. This is a statement repair with the associativity hole
retained, not a claimed proof of the old universally quantified assertion.

## Old

```lean
theorem completed_tensor_common_lift_constraints_associative
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry) :
    ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      closed.tensor.map (Prod.mkHom (data.tensor.hom.app (A, B)) (𝟙 _)) ≫
          data.tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
          (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
        (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
          ((ordinary l X R).obj C)).hom ≫
          closed.tensor.map (Prod.mkHom (𝟙 _) (data.tensor.hom.app (B, C))) ≫
          data.tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C))
```

```lean
theorem completed_tensor_common_lift_constraints
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry) :
    Nonempty (CompletedTensorCommonLiftConstraints l X R closed models symmetry
      data.tensor data.unit)
```

## New

```lean
theorem completed_tensor_common_lift_constraints_associative
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry)
    (normalized : ∀ A B, data.tensor.hom.app (A, B) =
      (completedTensorCommonComponent l X R closed models N A B).hom) :
    ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      closed.tensor.map (Prod.mkHom (data.tensor.hom.app (A, B)) (𝟙 _)) ≫
          data.tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
          (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
        (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
          ((ordinary l X R).obj C)).hom ≫
          closed.tensor.map (Prod.mkHom (𝟙 _) (data.tensor.hom.app (B, C))) ≫
          data.tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C))
```

```lean
theorem completed_tensor_common_lift_constraints
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry) :
    ∃ data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry,
      Nonempty (CompletedTensorCommonLiftConstraints l X R closed models symmetry
        data.tensor data.unit)
```

New proved declaration:
completed_tensor_common_lift_normalized_tensor_unit constructs data together with
its component equations using NatIso.ofComponents and the existing naturality
and ordinary-unit declarations. No definition chooses arbitrary data from a new
unproved existence theorem. Existing structures, target statements, source-library
files and other component theorem signatures are unchanged.

## Users

The current server claim records were read: the item is F1's; both adapted modules
are unclaimed. downstream.py --uses finds exactly the first two callers below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints | unclaimed | Construct normalized data, supply the new component equality, return the data and four constraints together. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftCoherence | unclaimed | Destructure the existential data/constraints in one step; its public theorem and structure signatures are unchanged. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftNormalizedTensorUnit | new, F1 | Concrete construction of normalized tensor/unit data; no sorry. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftAgreement | unclaimed at shared snapshot | Existing coherence interface unchanged; compile as an unchanged consumer. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftAgreementComponent | held independently | Existing coherence interface unchanged; compile as an unchanged consumer. |

All further downstream consumers see the same CompletedTensorCommonLiftCoherence
structure and the same completed_tensor_common_lift_coherence theorem type.
The repair does not change any definition used by a Challenge target statement;
target semantics and the unit route are preserved.

## Status

landed 20261028T072409-L-1942828 2026-10-28 (merge of deliver/F1/Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsAssociative)
