# SmoothGenericDirectImage local elaboration and compact-dual record API

## Reason

The proof uses local transparency options and irreducibility attributes to avoid expanding
chosen derived-functor constructions. The static interface detector conservatively flags
these commands. They export no new attribute or notation and change no existing definition
or signature. The new compact-dual record packages repeated comparison data behind named
projections; it contains no construction by choice from an admitted existence theorem.
The complete item and model compile without warnings in 26.3 and 29.5 seconds, respectively.

## Old

The original theorem signature, verbatim:

```lean
theorem exists_nonempty_open_smooth_directImage_lisse_baseChange
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (X : Scheme.{u}) (f : X ⟶ S) [IsSeparated f] [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    ∃ U : S.Opens, Nonempty U ∧
      ∀ (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
        IsPullback p fU f U.ι →
        (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))) ∧
        (∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
          ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))) ∧
        ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
          (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T)
          (sq : IsPullback vX fT fU v),
          IsIso ((derivedBaseChangeMap
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sq.toCommSq).app
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L)))
```

There were no local transparency settings or irreducibility commands in this module.

## New

The theorem has exactly the same signature as above. Its proof now uses the model data
and generic constancy; its original public imports are preserved verbatim. The new local
elaboration controls are:

```lean
-- Keep the derived-functor implementation behind its API during elaboration.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] derivedHom constantComplex finiteLisseDualPullbackComparison
  derivedBaseChangeMap upperStar lowerStar
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  _root_.DerivedCategory.homologyFunctor
```

The new module `Sheaf.AlgebraicGeometry.SmoothCompactDualModel` defines
`AlgebraicGeometry.Etale.SmoothCompactDualModel` and states
`AlgebraicGeometry.Etale.exists_smooth_compact_dual_model`. The record fields are a
bounded constructible complex, the ordinary-direct-image duality isomorphisms for open
restrictions and Noetherian test schemes, and the canonical exchange identity.
The attached definition and statement nodes spell out these signatures.
No existing public declaration, public import or target meaning changes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SmoothGenericDirectImage --uses
AlgebraicGeometry.Etale.exists_nonempty_open_smooth_directImage_lisse_baseChange`
reports zero downstream modules and the item itself as the only textual use.
Pending DAG parents remain entitled to use the unchanged theorem. No consumer requires
adaptation. New declarations have only the delivered item as a consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | B7 | Same signature; proof uses new record API. |
| Sheaf.AlgebraicGeometry.SmoothCompactDualModel | new, B7 | New data record and genuine separate existence obligation. |

## Status

landed 20261023T165904-L-2041893 2026-10-23 (merge of deliver/B7/Sheaf.AlgebraicGeometry.SmoothGenericDirectImage)
