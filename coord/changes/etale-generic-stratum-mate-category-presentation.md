# EtaleGenericStratumMate category presentation

## Reason

Expanding `DerivedCategoryModule A T` in this module gives exactly
`DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat A))`.
This is a definitional expansion only: universes, assumptions, functors, arrows,
adjunction units and counits are unchanged. It avoids repeated conversion through
abbreviation-generated sheafification proofs while elaborating the tensor mate.
The proof also passes projection invertibility explicitly and carries the concrete
adjoint tensor map through a proved private interface, avoiding repeated expansion
of derived pullback and monoidal localization instances. Original abbreviation-based
proof attempts exceed 60 seconds. After one successful dry run and a timed-out push
recompile (nothing pushed), the final proof infers the pullback functor from its canonical adjunction and
passes projection invertibility explicitly. The item compiles cleanly in 8.1 seconds.
No target declaration in Challenge.lean changes.

## Old

```lean
noncomputable def immersionUpperShriek
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A S :=
  D((j)^*[ModuleCat.{u + 1} A]) ⋙ (R((i)_*[ModuleCat.{u + 1} A])).rightAdjoint
```

```lean
noncomputable def immersionLowerUpperShriekAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    immersionLowerShriek A i j ⊣ immersionUpperShriek A i j :=
  (Adjunction.ofIsLeftAdjoint (R((i)_*[ModuleCat.{u + 1} A]))).comp
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
```

```lean
noncomputable def immersionHomEvaluation
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P M : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj M)).obj P ⟶ M :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj M)).app P ≫
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) P).counit.app M
```

```lean
theorem immersionInternalHomIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    ∃ θ : (immersionLowerShriek A i j).op.prod (𝟭 (DerivedCategoryModule A X)) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) X) ≅
      (𝟭 (DerivedCategoryModule A S)ᵒᵖ).prod (immersionUpperShriek A i j) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) S) ⋙
          R((i ≫ j)_*[ModuleCat.{u + 1} A]),
      ∀ (P : DerivedCategoryModule A S) (M C : DerivedCategoryModule A X)
        (f : C ⟶ (R((i ≫ j)_*[ModuleCat.{u + 1} A])).obj
          (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
            ((immersionUpperShriek A i j).obj M))),
        derivedTensorHom (ModuleCat.{u + 1} A) (f ≫ θ.inv.app (op P, M))
            (𝟙 ((immersionLowerShriek A i j).obj P)) ≫
          immersionHomEvaluation A X ((immersionLowerShriek A i j).obj P) M =
        immersionProjectionMap A i j C P ≫
          (immersionLowerShriek A i j).map
            (derivedTensorHom (ModuleCat.{u + 1} A)
              (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
                (i ≫ j)).homEquiv C
                  (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
                    ((immersionUpperShriek A i j).obj M))).symm f) (𝟙 P)) ≫
          (immersionLowerShriek A i j).map
            (immersionHomEvaluation A S P ((immersionUpperShriek A i j).obj M)) ≫
          (immersionLowerUpperShriekAdjunction A i j).counit.app M
```

## New

```lean
noncomputable def immersionUpperShriek
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  D((j)^*[ModuleCat.{u + 1} A]) ⋙ (R((i)_*[ModuleCat.{u + 1} A])).rightAdjoint
```

```lean
noncomputable def immersionLowerUpperShriekAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    immersionLowerShriek A i j ⊣ immersionUpperShriek A i j :=
  (Adjunction.ofIsLeftAdjoint (R((i)_*[ModuleCat.{u + 1} A]))).comp
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
```

```lean
noncomputable def immersionHomEvaluation
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj M)).obj P ⟶ M :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj M)).app P ≫
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) P).counit.app M
```

```lean
theorem immersionInternalHomIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    ∃ θ : (immersionLowerShriek A i j).op.prod
        (𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) X) ≅
      (𝟭 (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))ᵒᵖ).prod
        (immersionUpperShriek A i j) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) S) ⋙
          R((i ≫ j)_*[ModuleCat.{u + 1} A]),
      ∀ (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (M C : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (f : C ⟶ (R((i ≫ j)_*[ModuleCat.{u + 1} A])).obj
          (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
            ((immersionUpperShriek A i j).obj M))),
        derivedTensorHom (ModuleCat.{u + 1} A) (f ≫ θ.inv.app (op P, M))
            (𝟙 ((immersionLowerShriek A i j).obj P)) ≫
          immersionHomEvaluation A X ((immersionLowerShriek A i j).obj P) M =
        immersionProjectionMap A i j C P ≫
          (immersionLowerShriek A i j).map
            (derivedTensorHom (ModuleCat.{u + 1} A)
              (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
                (i ≫ j)).homEquiv C
                  (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
                    ((immersionUpperShriek A i j).obj M))).symm f) (𝟙 P)) ≫
          (immersionLowerShriek A i j).map
            (immersionHomEvaluation A S P ((immersionUpperShriek A i j).obj M)) ≫
          (immersionLowerUpperShriekAdjunction A i j).counit.app M
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleGenericStratumMate | C1 | Definitional category expansion; original hole proved. |
| Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence | Q3 | Uses the same functors, evaluation and counit; no semantic change or adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Transitive importer; no direct uses of changed declarations and no adaptation. |

The textual-use scan reports no use of `immersionInternalHomIso` outside its own
module. Both downstream originals exceed 60 seconds against the shared baseline and also
against the changed module overlay. No new type error is reported; no consumer file
is changed in this delivery. The existing consumer compilation problem remains
outside this definitionally equal presentation change.

## Status

landed 20261020T131128-L-1244431 2026-10-20 (merge of deliver/C1/Sheaf.AlgebraicGeometry.EtaleGenericStratumMate)
