# AlgebraicGeometry.Etale.normalized_generic_data_lifts

## Reason

The former intermediate theorem was false: the sheaf clauses do not tie g followed
by nu to the given point x or make K algebraic over its residue field. On a disjoint
union of two field spectra, an inclusion of the first component with identity g and
zero sheaves satisfies the sheaf clauses but cannot lift a point on the second.
The source construction in Stacks Tag 09Z6 uses a finite extension of kappa(x) and
normalizes precisely its residue-field morphism. The corrected intermediate theorem
retains those hypotheses. Its conclusion is unchanged.

The original core theorem discards the required algebra and square. Its signature
and module are untouched. The new, fully proved WithFactorization module repeats
the existing construction while retaining hAlg, hfin and hcomp. Its unit-transport step reuses the existing private helper through a proof-only
`import all Sheaf.AlgebraicGeometry.NormalizedGenericDataCore`; the duplicate
helper has been removed. No new assumptions or sorries enter that construction. The source route (field trivialization,
normalization, generic unit, geometric lifting) is unchanged.

## Old

```lean
theorem normalized_generic_data_lifts
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (x : X)
    (Y : Scheme.{u}) (ν : Y ⟶ X) (hν : IsIntegralHom ν)
    (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ Y)
    (M : ModuleCat.{u + 1} Λ) (hM : Finite M)
    (hu : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))
    (he : Nonempty
      ((upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((upperStar (ModuleCat.{u + 1} Λ) ν).obj F) ≅
       (upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ((Scheme.SpecToEquivOfField Ω X) s).1 = x →
        ∃ w : Spec (.of Ω) ⟶ Spec (.of K), w ≫ g ≫ ν = s
```

## New

```lean
theorem normalized_generic_data_lifts
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (_hF : Scheme.IsConstructibleEtaleModuleSheaf F) (x : X)
    (Y : Scheme.{u}) (ν : Y ⟶ X) (_hν : IsIntegralHom ν)
    (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ Y)
    (a : Algebra (X.residueField x) K)
    (ha : @Module.Finite (X.residueField x) K _ _ a.toModule)
    (hcomp : Spec.map (CommRingCat.ofHom (@algebraMap (X.residueField x) K _ _ a)) ≫
      X.fromSpecResidueField x = g ≫ ν)
    (M : ModuleCat.{u + 1} Λ) (_hM : Finite M)
    (_hu : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))
    (_he : Nonempty
      ((upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((upperStar (ModuleCat.{u + 1} Λ) ν).obj F) ≅
       (upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ((Scheme.SpecToEquivOfField Ω X) s).1 = x →
        ∃ w : Spec (.of Ω) ⟶ Spec (.of K), w ≫ g ≫ ν = s
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | Forced proof adaptation; existing signature and visibility identical. Obtain a, ha and hcomp from the new constructor and pass them to the corrected lifting theorem. Replace the Core proof import with WithFactorization. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataLifts | P2 | Correct the intermediate theorem and prove it using IsAlgClosed.lift. Replace the broad Core public import with its four statement imports. |

Repository-wide rg finds just one external use of normalized_generic_data_lifts:
the adapted module above. tools/downstream.py reports 149 downstream modules,
all behind that unchanged caller signature. No definition or target statement
changes, and no downstream statement acquires an additional hypothesis.

The changed caller lines are its proof-only constructor import, existential
pattern, constructor invocation and final lifting invocation. Each is necessary
to supply the added finite residue-field data. No other caller lines are changed.
The original caller fails against the corrected lifting signature; deliver3.py
records the counterfactual compiler error in the report's Forced adaptations.

## Status

landed 20261012T150955-L-2231638 2026-10-12 (merge of deliver/P2/Sheaf.AlgebraicGeometry.NormalizedGenericDataLifts)
