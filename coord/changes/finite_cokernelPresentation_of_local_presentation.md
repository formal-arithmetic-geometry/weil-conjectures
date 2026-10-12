# AlgebraicGeometry.Scheme.finite_cokernelPresentation_of_local_presentation

## Reason

Repair E2 of the returned delivery. An arbitrary local cokernel presentation need not have a finite-source replacement. Adding short exactness alone does not help: any middle sheaf F appears in 0 -> F -> F. The source argument instead first constructs a finite free presentation of the finite quotient and lifts its generators locally; its kernel is finite over the finite ring. This delivery isolates that local step in the new presentation-lift module and proves the categorical cokernel step from its explicit data.

## Old

```lean
theorem finite_cokernelPresentation_of_local_presentation {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ] {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {𝒰 : Cover.{u} etalePrecoverage X} {i : 𝒰.I₀} (h : ∃ K L : ModuleCat.{u + 1} Λ, ∃ φ : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶ (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L, Nonempty (cokernel φ ≅ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂)) : ∃ K L : ModuleCat.{u + 1} Λ, Module.Finite Λ K ∧ ∃ φ : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶ (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L, Nonempty (cokernel φ ≅ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂)
```

## New

```lean
theorem finite_cokernelPresentation_of_local_presentation {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ] {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {𝒰 : Cover.{u} etalePrecoverage X} {i : 𝒰.I₀} (hS : S.ShortExact) [S.X₁.IsConstant X.smallEtaleTopology] (h : ∃ T : ShortComplex (ModuleCat.{u + 1} Λ), T.ShortExact ∧ Module.Finite Λ T.X₁ ∧ ∃ e : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₃ ≅ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₃, ∃ r : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₂ ⟶ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂, r ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).map S.g = (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map T.g ≫ e.hom) : ∃ K L : ModuleCat.{u + 1} Λ, Module.Finite Λ K ∧ ∃ φ : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶ (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L, Nonempty (cokernel φ ≅ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂)
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ConstantExtensionCokernelAux --uses finite_cokernelPresentation_of_local_presentation` lists 430 transitive importers, but only the defining module and the single external caller below mention the declaration. All transitive importers retain identical statements and definitions because the caller retains its exact original signature. No definition changes; no target statement changes or target semantic re-review is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstantExtensionCokernelAux | G2 | Intermediate finite-source theorem corrected and proved; cover theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.ConstantExtensionCokernelPresentation | unclaimed | Forced proof adaptation: obtain finite-kernel local lift data rather than arbitrary cokernel data, then pass hS and that data to the corrected theorem. Its signature and visibility stay byte for byte identical. Proof import of ConstantExtensionPresentationLift is needed for this data. |

The new module Sheaf.AlgebraicGeometry.ConstantExtensionPresentationLift is part of this delivery, not an existing interface changed in the repository. Its only hole is the documented finite free generator-lifting step, strictly below the categorical cokernel conclusion.

## Status

landed 20261012T150952-L-2230408 2026-10-12 (merge of deliver/G2/Sheaf.AlgebraicGeometry.ConstantExtensionCokernelAux)
