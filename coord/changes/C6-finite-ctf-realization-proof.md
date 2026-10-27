# AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization

## Reason

The proof imports the source fixed-scalar Tor comparison. This also brings the pro-etale specialization `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn` into local name resolution. Explicitly qualify the generic Tor predicate with `_root_` to retain exactly the original elaborated proposition. No binder, universe, coefficient, interval, functor or conclusion changes. The two added elaborator options are scoped to this module; they support the existing encoding constructions and do not install downstream instances or alter public imports.

## Old

```lean
theorem finiteCtfInternalEtaleRealization (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hne : p ≠ ℓ) (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] (E : ∀ T : Scheme.{u}, Encoding A T) : (∀ (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] (a b : ℤ), a ≤ b → ∃ e : ObjectProperty.FullSubcategory (fun K ↦ Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T.left K ∧ Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ≌ ObjectProperty.FullSubcategory (fun K ↦ constantModelBoundedConstructible (coefficient A) T.left K ∧ DerivedCategory.torAmplitudeIn (Internal A T.left) a b K), Nonempty (e.functor ⋙ ObjectProperty.ι (fun K ↦ constantModelBoundedConstructible (coefficient A) T.left K ∧ DerivedCategory.torAmplitudeIn (Internal A T.left) a b K) ≅ ObjectProperty.ι (fun K ↦ Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T.left K ∧ Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ⋙ internalEtaleRealization A T.left (E T.left))) ∧ (∀ (V T : Over (Spec (.of k))) [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] (f : V ⟶ T) [QuasiCompact f.left] [QuasiSeparated f.left], Nonempty (DerivedCategory.Plus.ι ⋙ (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.left).rightDerivedFunctor ⋙ internalEtaleRealization A T.left (E T.left) ≅ DerivedCategory.Plus.ι ⋙ internalEtaleRealization A V.left (E V.left) ⋙ CondensedRing.moduleObjectDerivedPushforward (coefficient A) f.left))
```

## New

```lean
theorem finiteCtfInternalEtaleRealization (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hne : p ≠ ℓ) (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] (E : ∀ T : Scheme.{u}, Encoding A T) : (∀ (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] (a b : ℤ), a ≤ b → ∃ e : ObjectProperty.FullSubcategory (fun K ↦ Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T.left K ∧ Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ≌ ObjectProperty.FullSubcategory (fun K ↦ constantModelBoundedConstructible (coefficient A) T.left K ∧ _root_.DerivedCategory.torAmplitudeIn (Internal A T.left) a b K), Nonempty (e.functor ⋙ ObjectProperty.ι (fun K ↦ constantModelBoundedConstructible (coefficient A) T.left K ∧ _root_.DerivedCategory.torAmplitudeIn (Internal A T.left) a b K) ≅ ObjectProperty.ι (fun K ↦ Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T.left K ∧ Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ⋙ internalEtaleRealization A T.left (E T.left))) ∧ (∀ (V T : Over (Spec (.of k))) [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] (f : V ⟶ T) [QuasiCompact f.left] [QuasiSeparated f.left], Nonempty (DerivedCategory.Plus.ι ⋙ (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.left).rightDerivedFunctor ⋙ internalEtaleRealization A T.left (E T.left) ≅ DerivedCategory.Plus.ι ⋙ internalEtaleRealization A V.left (E V.left) ⋙ CondensedRing.moduleObjectDerivedPushforward (coefficient A) f.left))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Identical elaborated proposition; its two existing applications need no adaptation. |
| Sheaf.SixFunctors.FiniteCtfInternalEtaleRealization | C6 | Proof completed; generic Tor predicate explicitly qualified. |

## Status

landed 20261025T100834-L-3629174 2026-10-25 (merge of deliver/C6/Sheaf.SixFunctors.FiniteCtfInternalEtaleRealization)
