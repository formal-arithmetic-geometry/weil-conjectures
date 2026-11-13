/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.InjectiveModuleSheafHCohomology

/-!
# Acyclicity of annihilator subsheaves of injective module sheaves

## References

* Stacks Project, Tags 03FD and 03FC.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The kernel of multiplication by a positive integer on an injective module sheaf
has acyclic underlying abelian cohomology on its own scheme. This is a statement
on one site; it asserts nothing about restriction to a closed subscheme.
(Stacks, Tags 03FD, 03FC.) -/
theorem subsingleton_H_kernel_nsmul_injective_module
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I]
    (n : ℕ) (_hn : 0 < n) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (kernel (n • 𝟙 I))) q) := by
  let r : Λ := n
  let φ := Ideal.Quotient.mk (Ideal.span {r})
  have : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).IsRightAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).isRightAdjoint
  let K := (sheafCompose X.smallEtaleTopology
    (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)).obj I
  have : Injective K :=
    Injective.injective_of_adjoint (Sheaf.restrictCoextendScalarsAdj _ φ) I
  let S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ShortComplex.mk ((Sheaf.restrictCoextendScalarsAdj _ φ).counit.app I)
      (r • 𝟙 I) (by
        ext U : 3
        exact (ModuleCat.coextendQuotientShortComplex r (I.obj.obj U)).zero)
  have hpre : (S.map (sheafToPresheaf _ _)).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ fun U ↦ ?_
    have h := ModuleCat.exact_coextendQuotientShortComplex r (I.obj.obj U)
    rw [ShortComplex.exact_iff_isZero_homology] at h
    exact h.of_iso ((S.map (sheafToPresheaf _ _)).mapHomologyIso
      ((CategoryTheory.evaluation _ _).obj U)).symm
  have hmono : Mono (S.map (sheafToPresheaf _ _)).f := by
    have (U : X.Etaleᵒᵖ) : Mono ((S.map (sheafToPresheaf _ _)).f.app U) :=
      ModuleCat.mono_coextendQuotientShortComplex_f r (I.obj.obj U)
    exact NatTrans.mono_of_mono_app _
  have : Mono S.f := (sheafToPresheaf _ _).mono_of_mono_map hmono
  have hex : S.Exact := by
    have e : S.map (sheafToPresheaf _ _ ⋙ presheafToSheaf _ _) ≅ S :=
      S.mapNatIso (asIso (sheafificationAdjunction _ _).counit)
    exact (ShortComplex.exact_iff_of_iso e).1 (hpre.map (presheafToSheaf _ _))
  let e := IsLimit.conePointUniqueUpToIso hex.fIsKernel (kernelIsKernel S.g)
  have hK := subsingleton_H_underlying_of_injective_module (Λ ⧸ Ideal.span {r}) X K q hq
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hS : Subsingleton (Sheaf.H (U.obj S.X₁) q) := hK
  have hE : Subsingleton (Sheaf.H (U.obj (kernel S.g)) q) := by
    let f := ((Sheaf.functorH _ q).mapIso (U.mapIso e)).hom
    have hf := (ConcreteCategory.bijective_of_isIso f).surjective
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hf y
    exact congrArg f (hS.elim x y)
  simpa only [S, r, Nat.cast_smul_eq_nsmul] using hE

end AlgebraicGeometry.Etale

