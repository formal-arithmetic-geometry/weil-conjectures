# AlgebraicGeometry.Scheme.isConstructibleSheaf_of_finite_coefficient_underlying_sets

## Reason

Retire the duplicate local module listed in `coord/retire-items.tsv` and in
`coord/changes/retire-sheaf-twins-kept-20261020.tsv`. The adopted source module already
contains a complete proof of the same public theorem with a verbatim identical signature.
Both modules compile independently; the adopted theorem uses only propext,
Classical.choice, and Quot.sound. No source-library declaration or import is edited.

The listed DIFFERENT classification concerns the private chart helper's hypothesis
(IsLisseEtaleSheafOfSets locally versus IsFiniteLocallyConstantSheafOfTypes upstream)
and its corresponding private proof changes. It does not concern the public theorem.
The upstream proof constructs finite-label submodules and then module charts, preserves
the original stratification, and handles empty charts by discarding them. Its public
statement has neither added hypotheses nor weakened conclusions.

## Old

Module: `Sheaf.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets`.

```lean
theorem isConstructibleSheaf_of_finite_coefficient_underlying_sets
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)))
    (I : Ideal Λ) (hI : Finite (Λ ⧸ I))
    (hkill : ∀ (U : X.Etaleᵒᵖ) (r : Λ), r ∈ I →
      ∀ m : F.obj.obj U, r • m = 0) : IsConstructibleSheaf F
```

## New

Module: `WeilConjectures.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets`.
The same existing public theorem replaces the duplicate; the old module is withdrawn.

```lean
theorem isConstructibleSheaf_of_finite_coefficient_underlying_sets
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)))
    (I : Ideal Λ) (hI : Finite (Λ ⧸ I))
    (hkill : ∀ (U : X.Etaleᵒᵖ) (r : Λ), r ∈ I →
      ∀ m : F.obj.obj U, r • m = 0) : IsConstructibleSheaf F
```

The retired module's sole attached node retains its declaration and statement, and changes only its
Lean attachment to the existing source module. Every parent dependency on this node
therefore still names the same theorem. The node proof, proof dependencies and unit
route remain valid. No DAG node is deleted or replaced by a hollow attachment.

## Users

`tools/downstream.py --uses` found only the two direct consumers below and the item's
own declaration. The remaining six rows are all other transitive importers. None of
these modules has a current claim in coord/claims. There are no quarantined importers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets | E5 (this item) | Withdraw duplicate; move its node attachment to the existing source theorem. |
| Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage | unclaimed | Replace only the proof import with the source module; theorem and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | Reuse the adopted projective-line theorem, remove the duplicate private argument, and retain the public signature. |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | Transitive importer; no change needed. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation | unclaimed | Transitive importer; no change needed. |
| Sheaf.AlgebraicGeometry.FiniteConstructiblePushforwardVanishing | unclaimed | Transitive importer; no change needed. |
| Sheaf.AlgebraicGeometry.FiniteMorphismsConstructible | unclaimed | Transitive importer; no change needed. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | Transitive importer; no change needed. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | Transitive importer; no change needed. |

The inventory's former Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule
consumer has already been retired; its adopted WeilConjectures counterpart already
imports the adopted source theorem, so neither is edited here. The projective-line node drops its now-unused finite-coefficient-reconstruction edge,
while all other parent references remain supported by the same theorem at its new attachment.

The unchanged original ProjectiveLineConstructible consumer also times out at 60 seconds.
Profiling with reduced diagnostic heartbeat limits exposed expensive typeclass inference
in its repeated local argument. The source library already supplies a complete proof,
so the consumer now invokes hasConstructibleDirectImages_projectiveLine. Its proof follows
the same affine-local finite-pushforward/projective-curve route. The local code only
extracts the coefficient instances, converts the constructibility convention, and transports
along rightDerivedFunctorPlusCompatibility. This full file compiles in 12.4 seconds.
The wrapper uses backward.isDefEq.respectTransparency true locally to its proof,
preventing unnecessary unfolding in elaboration. The artifact-producing compile also
succeeds. No file or proof was split, and no time limit was raised.

Removed the now-unused private helpers abelianSetPullbackIso,
constructibleAbelian_underlyingSets, module_constructible_of_abelian,
constantModule_curve_constructible, and curve_constructible_affine. Their public
replacement is already proved in the adopted library. Public imports are unchanged.
The existing public theorem's signature and docstring are preserved verbatim:

```lean
theorem isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine
    (k : Type u) [Field k] (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    (F : Sheaf (ProjectiveSpace (ULift.{u} (Fin 2)) S).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hF : @Scheme.IsConstructibleEtaleModuleSheaf
      (ProjectiveSpace (ULift.{u} (Fin 2)) S) Λ _ hcoeff.2.1 F) (q : ℤ) :
    @Scheme.IsConstructibleEtaleModuleSheaf S Λ _ hcoeff.2.1
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace (ULift.{u} (Fin 2)) S ↘ S)).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (ProjectiveSpace (ULift.{u} (Fin 2)) S).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F)))
```

Updated this consumer node's proof description and proof dependencies to the source proof
plus the coefficient/derived-category wrapper. Removed its obsolete tool approval for
lem-sbc-higher-direct-image-forget-comparison; the remaining approvals stay in order.

## Status

landed 20261020T221133-L-4148159 2026-10-20 (merge of deliver/E5/Sheaf.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets)
