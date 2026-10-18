# SheafOfModules.locallyConstantFiniteType_derivedTensor

## Reason

The assigned theorem is reduced to local constant models and a tensor comparison,
with direct Lean proofs of finite tensor terms, finite homology, and exact realization.
The preflight conservatively records the new `open`, `open scoped`, helper section,
variables, local notation and scoped instance-search settings as an interface command
change. This record covers those commands. They support private proved helpers; no
existing statement, definition, universe, visibility, public import or target is changed.
The proof dependencies are private imports. No consumer requires an adaptation.

The new commands open `CategoryTheory.MonoidalCategory` and scoped `TensorProduct`,
introduce `section ConstantRealization` with `{C : Type u} [Category.{u} C]`, and use
local notations for the same constant ring sheaf and module realization already in the
original statement. The local quotation options keep the existing universe `u`; the
scoped instance-search size is 2048. They add no instances or public definitions.

## Old

The original public signature, verbatim:

```lean
theorem locallyConstantFiniteType_derivedTensor
    {C : Type u} [Category.{u} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B))))]
    (K L : DerivedCategory (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))))
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj K))
    (hL : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj L))
    (hKlc : ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj K))
    (hLlc : ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj L))
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat P) (hQ : CochainComplex.IsAcyclicTensorKFlat Q)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L) :
    ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((CochainComplex.mapBifunctor P Q
        (@CategoryTheory.MonoidalCategory.curriedTensor _ _
          (SheafOfModules.monoidalCategory
            ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj
              (CommRingCat.of B))))).homology i)
```

## New

The public signature, verbatim and unchanged:

```lean
theorem locallyConstantFiniteType_derivedTensor
    {C : Type u} [Category.{u} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B))))]
    (K L : DerivedCategory (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))))
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj K))
    (hL : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj L))
    (hKlc : ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj K))
    (hLlc : ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj L))
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat P) (hQ : CochainComplex.IsAcyclicTensorKFlat Q)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L) :
    ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((CochainComplex.mapBifunctor P Q
        (@CategoryTheory.MonoidalCategory.curriedTensor _ _
          (SheafOfModules.monoidalCategory
            ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj
              (CommRingCat.of B))))).homology i)
```

Its former `:= by sorry` is replaced by the complete proof in the delivered module.
The helper commands and all private helper proofs are included in that same module.

## Users

`tools/downstream.py Sheaf.Paper.LocallyConstantTensor --uses
SheafOfModules.locallyConstantFiniteType_derivedTensor` lists the two downstream modules
below. Its textual declaration scan finds the declaration only in the assigned module;
the downstream proof bodies are still unfinished. Both import the same public statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocallyConstantTensor | N1 | Original signature unchanged; proof and private helpers added. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | G2 | Same public statement and definitions; no edit. |
| Sheaf.Paper.NilpotentReductionLissity | N2 | Same public statement and definitions; no edit. |

No existing definition changes, so no target statement review is reopened. The new
intermediate statements have their own new modules and DAG nodes and receive the
maintainer's independent review with this delivery.

## Status

landed 20261018T091407-L-3256965 2026-10-18 (merge of deliver/N1/Sheaf.Paper.LocallyConstantTensor)
