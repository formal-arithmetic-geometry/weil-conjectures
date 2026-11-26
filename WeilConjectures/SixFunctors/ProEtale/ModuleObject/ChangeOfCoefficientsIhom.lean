/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.ReductionIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IhomCompatibility

/-!
# Change of coefficients for internal Hom

Let `ℓ` be a prime, `k` a field of characteristic `p ≠ ℓ` and `X` a separated `k`-scheme of finite
type. For a map of coefficient rings `Λ ⟶ Λ'` with (monoidal) extension of scalars `T`, the
comparison `T RHom(A, B) ⟶ RHom(T A, T B)` is the mate of the tensorator
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`). This file collects in a single statement
(`ProEtale.CondensedRing.isIso_ihomComparison_coefficientChange`) the coefficient maps for which
this comparison is known to be an isomorphism on bounded constructible complexes:

* the reductions `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` (on all complexes);
* the inclusions `E ⟶ F` of finite subextensions of `ℚ̄_ℓ / ℚ_ℓ`;
* the inclusions `𝒪_E ⟶ E`, `E ⟶ ℚ̄_ℓ`, and their composite `𝒪_E ⟶ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Change of coefficients for internal Hom.** On a separated `k`-scheme of finite type `X`, the
comparison `T RHom(A, B) ⟶ RHom(T A, T B)` for the extension of scalars `T` along `Λ ⟶ Λ'` is an
isomorphism for all bounded constructible `A` and `B` when `Λ ⟶ Λ'` is
1. the reduction `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`,
2. the inclusion `E ⟶ F` of finite subextensions of `ℚ̄_ℓ / ℚ_ℓ`,
3. the inclusion `𝒪_E ⟶ E`,
4. the inclusion `E ⟶ ℚ̄_ℓ`,
5. the composite `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`. -/
theorem isIso_ihomComparison_coefficientChange {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) (n : ℕ) :
    (∀ A B : DerivedCategory (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)),
      letI := Mod.extendScalarsMonoidal (integersModPowReduction X.left ℓ E.1 n)
      letI :=
        (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctorMonoidal
      IsIso ((Functor.LaxMonoidal.ihomComparison
        L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)) A).app B)) ∧
    (∀ A : PadicSubfieldConstructible X.left ℓ E,
      IsIso (Functor.LaxMonoidal.ihomComparison (constructibleExtendScalars X.left ℓ h) A)) ∧
    (∀ A : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧,
      IsIso (Functor.LaxMonoidal.ihomComparison
        (boundedConstructibleExtendScalars X.left ℓ E) A)) ∧
    (∀ A : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧,
      IsIso (Functor.LaxMonoidal.ihomComparison (constructibleToPadicAlgCl X.left ℓ E) A)) ∧
    (∀ A : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧,
      IsIso (Functor.LaxMonoidal.ihomComparison
        (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E)
          A)) :=
  ⟨isIso_ihomComparison_leftDerivedIntegersModPowReduction ℓ E.1 n X.left,
    isIso_ihomComparison_constructibleExtendScalars ℓ X h,
    isIso_ihomComparison_boundedConstructibleExtendScalars ℓ E,
    isIso_ihomComparison_constructibleToPadicAlgCl ℓ E,
    isIso_ihomComparison_boundedConstructibleIntegersToPadicAlgCl ℓ E⟩

end AlgebraicGeometry.ProEtale.CondensedRing
