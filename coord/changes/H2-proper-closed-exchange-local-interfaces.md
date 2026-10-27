# proper_constructible_lifted_test_restriction, condensed_closed_exchange_affine_descent

## Reason

Expose the two missing local interfaces in the assigned proper constructible closed exchange argument. These are new theorem declarations in new Sheaf modules. The assigned theorem and every existing signature and public import remain identical.

## Old

Neither declaration existed. The assigned theorem had one whole-proof sorry.

## New

```lean
theorem proper_constructible_lifted_test_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))))
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (ClosedTestDerivedExchangeModel.closedMap A I))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)] :
    IsIso ((ClosedTestDerivedExchangeModel.sectionsOver Λ V.hom).map
      ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
        ((DerivedCategory.singleFunctor _ 0).obj M)))
```

```lean
theorem condensed_closed_exchange_affine_descent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y C : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (c : C ⟶ Y) [IsClosedImmersion c]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hloc : ∀ (A : Type u) [CommRing A] (I : Ideal A)
      (XU XZ : Scheme.{u}) (v : Spec (.of A) ⟶ Y) [IsOpenImmersion v]
      (a : XU ⟶ X) (fU : XU ⟶ Spec (.of A))
      (b : Spec (.of (A ⧸ I)) ⟶ C)
      (h : XZ ⟶ XU) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
      (_wf : IsPullback a fU f v)
      (_wc : IsPullback b (ClosedTestDerivedExchangeModel.closedMap A I) c v)
      (w : IsPullback h fZ fU (ClosedTestDerivedExchangeModel.closedMap A I)),
      IsIso ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
          ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ a).obj M)))) :
    IsIso ((condensedAmbientExchange Λ
      (g' := pullback.fst f c) (f' := pullback.snd f c) (f := f) (g := c)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app ((DerivedCategory.singleFunctor _ 0).obj M))
```

## Users

These new modules have no pre-existing consumers. Their only consumer introduced in this delivery is the assigned module. No adaptation of another group's module is made.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperConstructibleClosedExchangeHeart | H2 | Proof-only imports; uses evaluated single-test exchange, conservative evaluation and affine descent with the unchanged original theorem signature. |

## Status

landed 20261025T205453-L-3257682 2026-10-25 (merge of deliver/H2/Sheaf.Paper.ProperConstructibleClosedExchangeHeart)
