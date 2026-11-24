/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLocalFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction

/-! # Lattice compatibility of the continuous module encoding

## References

* Stacks Project, Modules on Sites
* Bhatt--Scholze, Section 6.8
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The explicit continuous module encodings preserve local finite freeness and
translate any specified etale lattice and its rationalization back to internal modules.
(Stacks, Tags 03DM, 03DO, 03D7, 03EK and 03EL; Bhatt--Scholze, Definition 6.8.3 and
Proposition 6.8.4 (6)) -/
theorem continuousModuleEncoding_lattice_compatibility
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    ((continuousFieldModuleEquivalence ℓ E X).functor.obj P).IsFiniteLocallyFree ∧
    ∀ (Y : Scheme.{u}) (f : Y ⟶ X) [Etale f]
      (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf ℓ E Y))),
      M.IsFiniteLocallyFree →
      Nonempty ((SheafOfModules.changeOfRings (lisseIntegerToField ℓ E Y) M).val ≅
        (PresheafOfModules.pushforward (lisseEtaleCoefficientIdentification ℓ E f)).obj
          ((continuousFieldModuleEquivalence ℓ E X).functor.obj P).val) →
      IsLocallyFree (condensedRingObj (integralCoeff ℓ E) Y)
        ((continuousIntegerModuleEquivalence ℓ E Y).inverse.obj M) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y)).obj
          ((continuousIntegerModuleEquivalence ℓ E Y).inverse.obj M) ≅
        (upperStar (Profinite.continuousMapRingObj E) f).obj P) := by
  refine ⟨continuousField_locallyFree ℓ E X P hP, ?_⟩
  intro Y f _ M hM hα
  let : M.IsFiniteLocallyFree := hM
  refine ⟨continuousInteger_inverse_locallyFree ℓ E Y M, ?_⟩
  obtain ⟨eS⟩ := continuousModuleEncoding_scalar_extension ℓ E Y M
  obtain ⟨eR⟩ := continuousField_module_restriction ℓ E X Y f P
  obtain ⟨eα⟩ := hα
  let F := continuousFieldModuleEquivalence ℓ E Y
  refine ⟨F.fullyFaithfulFunctor.preimageIso ?_⟩
  exact eS ≪≫ (SheafOfModules.fullyFaithfulForget _).preimageIso (eα ≪≫ eR.symm)

end AlgebraicGeometry.ProEtale.CondensedRing
