# AlgebraicGeometry.Etale.etaleGenericPerfectHom

## Reason

The old signature spells out the canonical symmetry/counit evaluation composite twice.
Specializing the generic duality proof to module coefficients made the kernel repeatedly
compare its monoidal instance arguments: the main declaration alone took about 32 seconds
of kernel checking and the whole file reached the 60-second limit. Naming that exact
composite as the transparent, explicitly constructed `derivedHomRightEvaluation` reduces
the complete file to 21.6 seconds. No data is chosen from an existence theorem.

The theorem's binders, universe, hypotheses, conclusion, comparison direction, and actual
evaluation maps are preserved. The two evaluation let values now use a transparent
abbreviation of the same composite. A scratch compatibility theorem with the entire
original signature, including its original `simpa` evaluation terms, was proved by
`exact etaleGenericPerfectHom A g a b c d hab hcd P N hP hN` and compiled in 47.0 seconds.
No definition used by a Challenge target changes its mathematical value.

## Old

```lean
theorem etaleGenericPerfectHom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (P N : DerivedCategoryModule A S)
    (hP : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S,
      ∀ i : U.I₀,
        ∃ E : CochainComplex
            (Sheaf (U.X i).smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
          Nonempty
            (DerivedCategory.Q.obj E ≅
              (Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)).mapDerivedCategory.obj P) ∧
          (∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
          (∀ n : ℤ, ∃ r : ℕ,
            ∃ ι : E.X n ⟶
                (constantSheaf (U.X i).smallEtaleTopology
                  (ModuleCat.{u + 1} A)).obj
                  (ModuleCat.of A (Fin r → A)),
            ∃ π :
                (constantSheaf (U.X i).smallEtaleTopology
                  (ModuleCat.{u + 1} A)).obj
                  (ModuleCat.of A (Fin r → A)) ⟶ E.X n,
              ι ≫ π = 𝟙 (E.X n)))
    (hN : ∀ n : ℤ, n < c ∨ d < n →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj N)) :
    let H : DerivedCategoryModule A S :=
      ((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N
    let P' : DerivedCategoryModule A S' :=
      (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P
    let N' : DerivedCategoryModule A S' :=
      (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj N
    let H' : DerivedCategoryModule A S' :=
      ((RHom(S')[ModuleCat.{u + 1} A]).obj (op P')).obj N'
    let ev :
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj H).obj P ⟶ N := by
      simpa [H] using
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app H).app P ≫
          (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) P).counit.app N
    let ev' :
        ((derivedTensor (ModuleCat.{u + 1} A) S').obj H').obj P' ⟶ N' := by
      simpa [H', P', N'] using
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S').hom.app H').app P' ≫
          (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
            ((Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P)).counit.app
            ((Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj N)
    ((∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj H)) ∧
      (∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S'.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj H')) ∧
      ∃ β : (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj
          (((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N) ≅
          ((RHom(S')[ModuleCat.{u + 1} A]).obj (op P')).obj N',
        ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g
            (((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N) P).inv ≫
            (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).map ev) =
          ((derivedTensor (ModuleCat.{u + 1} A) S').map β.hom).app
            ((Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P) ≫ ev')
```

## New

```lean
theorem etaleGenericPerfectHom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (P N : DerivedCategoryModule A S)
    (hP : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S,
      ∀ i : U.I₀,
        ∃ E : CochainComplex
            (Sheaf (U.X i).smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
          Nonempty
            (DerivedCategory.Q.obj E ≅
              (Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)).mapDerivedCategory.obj P) ∧
          (∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
          (∀ n : ℤ, ∃ r : ℕ,
            ∃ ι : E.X n ⟶
                (constantSheaf (U.X i).smallEtaleTopology
                  (ModuleCat.{u + 1} A)).obj
                  (ModuleCat.of A (Fin r → A)),
            ∃ π :
                (constantSheaf (U.X i).smallEtaleTopology
                  (ModuleCat.{u + 1} A)).obj
                  (ModuleCat.of A (Fin r → A)) ⟶ E.X n,
              ι ≫ π = 𝟙 (E.X n)))
    (hN : ∀ n : ℤ, n < c ∨ d < n →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj N)) :
    let H : DerivedCategoryModule A S :=
      ((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N
    let P' : DerivedCategoryModule A S' :=
      (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P
    let N' : DerivedCategoryModule A S' :=
      (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj N
    let H' : DerivedCategoryModule A S' :=
      ((RHom(S')[ModuleCat.{u + 1} A]).obj (op P')).obj N'
    let ev := derivedHomRightEvaluation (ModuleCat.{u + 1} A) S P N
    let ev' := derivedHomRightEvaluation (ModuleCat.{u + 1} A) S' P' N'
    ((∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj H)) ∧
      (∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S'.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj H')) ∧
      ∃ β : (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj
          (((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N) ≅
          ((RHom(S')[ModuleCat.{u + 1} A]).obj (op P')).obj N',
        ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g
            (((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N) P).inv ≫
            (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).map ev) =
          ((derivedTensor (ModuleCat.{u + 1} A) S').map β.hom).app
            ((Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P) ≫ ev')
```

The new definition is:

```lean
noncomputable def derivedHomRightEvaluation
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (S : Scheme.{u}) (P N : _root_.DerivedCategory (Sheaf S.smallEtaleTopology C)) :
    ((derivedTensor C S).obj (((RHom(S)[C]).obj (op P)).obj N)).obj P ⟶ N :=
  ((derivedTensorSymmetry C S).hom.app (((RHom(S)[C]).obj (op P)).obj N)).app P ≫
    (derivedTensorHomAdjunction C P).counit.app N
```

## Users

`tools/downstream.py Sheaf.SixFunctors.EtaleGenericPerfectHom --uses etaleGenericPerfectHom`
found exactly one downstream module. It imports the item but does not yet mention the
theorem in its proofs. All its signatures and definitions are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.EtaleGenericPerfectHom | H8 | The proof is completed; evaluations share the canonical composite. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | B8 | Unchanged importer; no adaptation is needed. |

No consumer is edited, and no forced adaptation is claimed.

## Status

landed 20261020T051403-L-1662081 2026-10-20 (merge of deliver/H8/Sheaf.SixFunctors.EtaleGenericPerfectHom)
