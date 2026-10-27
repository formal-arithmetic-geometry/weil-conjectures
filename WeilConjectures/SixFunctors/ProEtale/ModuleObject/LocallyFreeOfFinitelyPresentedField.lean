/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
public import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Locally finitely presented module objects over the field coefficients are locally free

On a scheme `Z` with noetherian underlying space, a pro-étale locally finitely presented module
object over `ℚ̲̄_ℓ,Z` (resp. over `E̲_Z` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`) is locally
free (`ProEtale.CondensedRing.isLocallyFree_of_isLocallyFinitelyPresented_of_noetherianSpace`,
`ProEtale.CondensedRing.ContinuousMapRingObj.isLocallyFree_of_isLocallyFinitelyPresented`): these
are the lisse sheaves of Bhatt–Scholze, *The pro-étale topology for schemes*, Definition 6.8.6.
They are restatements of `condensedQbar_lfp_locally_free` and
`exists_finiteFree_cover_of_condensedField_lfp` for the coefficient rings
`Profinite.padicAlgClRingObj ℓ` and `Profinite.continuousMapRingObj E`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- On a scheme with noetherian underlying space, a pro-étale locally finitely presented module
object over `ℚ̲̄_ℓ` is locally free. -/
theorem isLocallyFree_of_isLocallyFinitelyPresented_of_noetherianSpace (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z) M) :
    IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z) M :=
  sorry

/-- On a scheme with noetherian underlying space, a pro-étale locally finitely presented module
object over `E̲`, for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, is locally free. -/
theorem ContinuousMapRingObj.isLocallyFree_of_isLocallyFinitelyPresented
    (E : FiniteIntermediateField ℓ) (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Z)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) Z) M) :
    IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) Z) M :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
