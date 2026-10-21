# Completed coefficient proof interfaces

## Reason

The completed local criterion uses normalized coefficient comparisons and the concrete
quotient and K-flat models of `Sheaf.Paper.AdicCoefficientDatumCompleted`. This dependency
is unclaimed when checked. Fill four existing proof holes without changing its interface.

## Old

```lean
theorem adicDatumFiniteCoefficientIso_exists :
    ∃! e : adicLisseRing T P ≅ AlgebraicGeometry.ProEtale.finiteCoefficientRingSheaf T P,
      adicLisseConstantUnit T P ≫ e.hom.hom =
        AlgebraicGeometry.ProEtale.finiteCoefficientScalarMap T P

theorem adicDatumFiniteCoefficientIso_natural
    (B : Type (t + 1)) [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B] (φ : P →+* B)
    (q : AlgebraicGeometry.ProEtale.finiteCoefficientPresheaf T P ⟶
      AlgebraicGeometry.ProEtale.finiteCoefficientPresheaf T B)
    (hq : ∀ (U : T.ProEtᵒᵖ)
      (s : C(ConnectedComponents U.unop.left, P))
      (c : ConnectedComponents U.unop.left),
      ContinuousMap.toFun (q.app U s) c = φ (s c)) :
    (adicDatumFiniteCoefficientIso T P).hom ≫
        (presheafToSheaf (ProEt.topology T) RingCat.{t + 1}).map q =
      (adicLisseForget T).map
        ((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom φ)) ≫ (adicDatumFiniteCoefficientIso T B).hom

theorem adicDatumQuotients_exists :
    Nonempty (CompletedConstantQuotientTower T d.ideal (adicDatumRing T d) (𝟙 _))

theorem adicDatumExtension_kflat (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    CochainComplex.IsAcyclicTensorKFlat (R := S)
      (((completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
```

## New

The signatures above, all definitions, public imports and visibility are unchanged.
The finite coefficient comparison is the unique map extending the scalar presentation
across the locally bijective constant-ring unit. Local bijectivity gives its inverse;
unit naturality proves compatibility with scalar homomorphisms. Reuse the existing
explicit quotient functor `completedConstant_quotients` through a private proof import.
K-flatness follows by tensor cancellation after exact, faithful restriction of scalars.
Reuse the K-flat part of the existing independent-coefficient change-of-rings proof; its
additional flat-term hypothesis is needed only for its separate flat-term conclusion.
Restriction preserves the total-complex sums, and the resulting bicomplex isomorphism
identifies the restricted tensor complex with tensoring the restricted acyclic input.

## Users

Only theorem proof bodies and a private proof import change. Every module sees the same
signatures and definition bodies, so no consumer adaptation or target re-review is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicCoefficientDatumCompleted | unclaimed | Four existing named proof holes filled. |
| Sheaf.Paper.IntegralStratifiedPerfectModels | K2, new supporting module | Unchanged completed realization interface. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | K2 | Same coefficient types and models. |

| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | The existing K-flat preservation statement has the same signature and a completed proof; no consumer change. |

## Status

landed 20261021T061432-L-1774768 2026-10-21 (merge of deliver/K2/Sheaf.Paper.IntegralStratifiedPerfectCharacterization)
