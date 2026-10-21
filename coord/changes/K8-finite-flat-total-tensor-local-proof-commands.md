# AlgebraicGeometry.Etale.finiteFlatConstructible_totalTensor local proof commands

## Reason

The preflight classifies added top-level variable and attribute commands as an interface
change requiring a record. The new coefficient-category variables are confined to a
closed section containing only proved private helpers. The local finite-biproduct
attribute supplies the canonical Abelian instance for the proof. The added universe
names are used only by those private helpers. No public signature, public import,
definition, global instance or attribute changes. The source library is untouched.
The complete proof compiled in 47.0 seconds; its sole formatting warning was repaired.
Generic K-flat and derived comparison wrappers avoid expensive normalization of the
concrete sheaf total tensor and localization structures, within the existing 60-second limit.

## Old

The public theorem signature is:

```lean
theorem finiteFlatConstructible_totalTensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hPflat : ∀ i : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (P.X i)))
    (_hQflat : ∀ j : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (Q.X j)))
    (_hPc : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X i))
    (_hQc : ∀ j : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (Q.X j))
    (_hPbound : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i))
    (_hQbound : ∀ j : ℤ, (j < c ∨ d < j) → IsZero (Q.X j))
    (T : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hT : T = CochainComplex.mapBifunctor P Q
      (@curriedTensor _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)))) :
    (∀ n : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (T.X n))) ∧
    (∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (T.X n)) ∧
    (∀ n : ℤ, (n < a + c ∨ b + d < n) → IsZero (T.X n)) ∧
    (∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (_root_.DerivedCategory.Q.obj T))) ∧
    (@CochainComplex.IsKFlatForTotalTensor _ _ _
      (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} A)) _ _ T) ∧
    Nonempty (_root_.DerivedCategory.Q.obj T ≅
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        (_root_.DerivedCategory.Q.obj P)).obj (_root_.DerivedCategory.Q.obj Q)) ∧
    ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℤ),
      (n < a + c ∨ b + d < n) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          (_root_.DerivedCategory.Q.obj T)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj N)))
```

Its body was `by sorry`. The file had only `universe u`, the existing `open` command,
and no new local finite-biproduct attribute or coefficient-category helper section.

## New

The public theorem signature is identical:

```lean
theorem finiteFlatConstructible_totalTensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hPflat : ∀ i : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (P.X i)))
    (_hQflat : ∀ j : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (Q.X j)))
    (_hPc : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X i))
    (_hQc : ∀ j : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (Q.X j))
    (_hPbound : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i))
    (_hQbound : ∀ j : ℤ, (j < c ∨ d < j) → IsZero (Q.X j))
    (T : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hT : T = CochainComplex.mapBifunctor P Q
      (@curriedTensor _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)))) :
    (∀ n : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (T.X n))) ∧
    (∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (T.X n)) ∧
    (∀ n : ℤ, (n < a + c ∨ b + d < n) → IsZero (T.X n)) ∧
    (∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (_root_.DerivedCategory.Q.obj T))) ∧
    (@CochainComplex.IsKFlatForTotalTensor _ _ _
      (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} A)) _ _ T) ∧
    Nonempty (_root_.DerivedCategory.Q.obj T ≅
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        (_root_.DerivedCategory.Q.obj P)).obj (_root_.DerivedCategory.Q.obj Q)) ∧
    ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℤ),
      (n < a + c ∨ b + d < n) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          (_root_.DerivedCategory.Q.obj T)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj N)))
```

Its body is now completely proved. The local commands are:

```lean
universe u vC uC wC
attribute [local instance] Abelian.hasFiniteBiproducts
section
variable (E : Type uC) [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
-- Two proved private helpers using derivedTensor E.
end
```

All added declarations are private and proved, and no imported module observes their
section variables or the local attribute. Original public imports remain verbatim.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteFlatConstructibleTotalTensor
--uses AlgebraicGeometry.Etale.finiteFlatConstructible_totalTensor` reports zero
current downstream Lean modules. The item itself is the only textual declaration use.
The unfinished DAG parents and the unit route remain intact; this is a proof delivery,
not a withdrawal. No consumer adaptation is required.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteFlatConstructibleTotalTensor | K8 | Proof and private helpers only; identical public statement. |

## Status

landed 20261021T203703-L-3852797 2026-10-21 (merge of deliver/K8/Sheaf.AlgebraicGeometry.FiniteFlatConstructibleTotalTensor)
