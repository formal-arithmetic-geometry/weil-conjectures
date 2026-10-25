/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersModPow
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.Sites.ZModModuleLift
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

/-!

# Reduction modulo `ℓ` of integral module objects

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`. The reduction
`𝒪_E ⟶ 𝒪_E ⧸ ℓ` is a continuous homomorphism onto a discrete ring, hence induces a morphism of
condensed rings `𝒪̲_E ⟶ (𝒪_E ⧸ ℓ)̲` and, pulled back to a scheme `X`, a morphism of coefficient
ring objects `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓ)_X` (`ProEtale.padicIntegersToReduction`). Since `ℓ = 0` in
`𝒪_E ⧸ ℓ`, every module object over `(𝒪_E ⧸ ℓ)_X` is killed by `ℓ`
(`ProEtale.zsmul_id_eq_zero_of_reduction`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace Profinite

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓ)̲` of ring objects of condensed abelian groups, induced by the
continuous reduction map `𝒪_E ⟶ 𝒪_E ⧸ ℓ` onto a discrete ring. -/
noncomputable def padicIntegersRingObjToReduction :
    padicIntegersRingObj.{u} ℓ E ⟶ continuousMapRingObj (integersModPow ℓ E 1) :=
  letI := normedFieldOfAlgebra ℓ E
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap (integersModPowMk ℓ E 1) (continuous_integersModPowMk ℓ E 1))

instance : IsMonHom (padicIntegersRingObjToReduction.{u} ℓ E) :=
  letI := normedFieldOfAlgebra ℓ E
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap (integersModPowMk ℓ E 1) (continuous_integersModPowMk ℓ E 1))))

/-- The integer `ℓ` is zero in `𝒪_E ⧸ ℓ`. -/
lemma natCast_eq_zero_integersModPow_one : (ℓ : integersModPow ℓ E 1) = 0 := by
  rw [← map_natCast (integersModPowMk ℓ E 1)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))

/-- Multiplication by `ℓ` is zero on the condensed ring `(𝒪_E ⧸ ℓ)̲`. -/
lemma zsmul_id_continuousMapRingObj_integersModPow_one :
    (ℓ : ℤ) • 𝟙 (continuousMapRingObj.{u} (integersModPow ℓ E 1)) = 0 := by
  ext S x
  obtain ⟨x⟩ := x
  change ULift.up ((ℓ : ℤ) • x) = ULift.up 0
  congr 1
  ext s
  change (ℓ : ℤ) • x s = 0
  rw [natCast_zsmul, nsmul_eq_mul, natCast_eq_zero_integersModPow_one, zero_mul]

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- The coefficient ring object `(𝒪_E ⧸ ℓ)_X = p_X^* (𝒪_E ⧸ ℓ)̲` on `X_proét`. -/
noncomputable abbrev reductionRingObj : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj (integersModPow ℓ E.1 1)) X

/-- The reduction `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓ)_X` of coefficient ring objects on `X_proét`: the pullback
along `p_X` of the reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓ)̲` of condensed rings. -/
noncomputable abbrev padicIntegersToReduction :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X ⟶ reductionRingObj X ℓ E :=
  coefficientMap (Profinite.padicIntegersRingObjToReduction ℓ E.1) X

/-- Multiplication by `ℓ` is zero on the coefficient ring object `(𝒪_E ⧸ ℓ)_X`. -/
lemma zsmul_id_reductionRingObj : (ℓ : ℤ) • 𝟙 (reductionRingObj X ℓ E) = 0 := by
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  rw [← (upperStarFromPoint X).map_id, ← Functor.map_zsmul,
    Profinite.zsmul_id_continuousMapRingObj_integersModPow_one, Functor.map_zero]

/-- Every module object over `(𝒪_E ⧸ ℓ)_X` is killed by `ℓ`. -/
lemma zsmul_id_eq_zero_of_reduction
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (reductionRingObj X ℓ E)) :
    (ℓ : ℤ) • 𝟙 M.X = 0 := by
  have h1 : η[reductionRingObj X ℓ E] ▷ M.X ≫ ModObj.smul (M := reductionRingObj X ℓ E) (X := M.X) =
      (λ_ M.X).hom := by
    simpa using ModObj.one_smul (M := reductionRingObj X ℓ E) M.X
  have h2 : (ℓ : ℤ) • η[reductionRingObj X ℓ E] = 0 := by
    rw [← Category.comp_id η[reductionRingObj X ℓ E], ← Preadditive.comp_zsmul,
      zsmul_id_reductionRingObj, Limits.comp_zero]
  have h3 : ((ℓ : ℤ) • η[reductionRingObj X ℓ E]) ▷ M.X =
      (ℓ : ℤ) • (η[reductionRingObj X ℓ E] ▷ M.X) :=
    (tensorRight M.X).map_zsmul
  rw [h2, MonoidalPreadditive.zero_whiskerRight] at h3
  have h4 : (ℓ : ℤ) • (λ_ M.X).hom = 0 := by
    rw [← h1, ← Preadditive.zsmul_comp]
    exact (congrArg (· ≫ _) h3.symm).trans Limits.zero_comp
  rw [← Iso.inv_hom_id (λ_ M.X), ← Preadditive.comp_zsmul, h4, Limits.comp_zero]

/-- An `(𝒪_E ⧸ ℓ)_X`-module object, regarded as a pro-étale sheaf of `ℤ/ℓ`-modules: its underlying
abelian sheaf is killed by `ℓ` (`ProEtale.zsmul_id_eq_zero_of_reduction`). -/
noncomputable def reductionModuleSheaf :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (reductionRingObj X ℓ E) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) :=
  Sheaf.zmodModuleLift ℓ (Mod.forget _) (zsmul_id_eq_zero_of_reduction X ℓ E)

instance : (reductionModuleSheaf X ℓ E).Additive :=
  inferInstanceAs
    (Sheaf.zmodModuleLift ℓ (Mod.forget _) (zsmul_id_eq_zero_of_reduction X ℓ E)).Additive

instance : PreservesFiniteLimits (reductionModuleSheaf X ℓ E) :=
  inferInstanceAs (PreservesFiniteLimits
    (Sheaf.zmodModuleLift ℓ (Mod.forget _) (zsmul_id_eq_zero_of_reduction X ℓ E)))

instance : PreservesFiniteColimits (reductionModuleSheaf X ℓ E) :=
  inferInstanceAs (PreservesFiniteColimits
    (Sheaf.zmodModuleLift ℓ (Mod.forget _) (zsmul_id_eq_zero_of_reduction X ℓ E)))

/-- The **derived reduction modulo `ℓ`** `K ↦ K ⊗ᴸ_{𝒪_{E,X}} (𝒪_E ⧸ ℓ)_X` of complexes of
`𝒪_{E,X}`-module objects, regarded in the derived category of pro-étale sheaves of
`ℤ/ℓ`-modules: the derived extension of scalars along `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓ)_X`, followed by the
exact functor `ProEtale.reductionModuleSheaf`. -/
noncomputable def derivedReduction :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) ⥤
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
  (Mod.extendScalars (padicIntegersToReduction X ℓ E)).leftDerivedFunctor ⋙
    (reductionModuleSheaf X ℓ E).mapDerivedCategory

/-! ### Inputs from other subsections -/

variable [IsNoetherian X]

/-- Blueprint `sk-prop-integral-criterion` (section `sec-proetale-coefficients`), implication
(1) ⇒ (2), for the reductions `K_n = K ⊗ᴸ_{𝒪_{E,X}} (𝒪_E ⧸ π_E^n)_X` of
`sk-def-pe-derived-completion` at `π_E^n = ℓ` (up to a unit): on a noetherian scheme `X`, the
reduction of a bounded constructible `𝒪_E`-complex is a bounded constructible complex with
coefficients in `𝒪_E ⧸ ℓ`, hence, regarded with coefficients `ℤ/ℓ`, of étale origin
(`ProEtale.DerivedCategory.boundedConstructible`; a finite `𝒪_E ⧸ ℓ`-module sheaf is
constructible if and only if its underlying `ℤ/ℓ`-module sheaf is). -/
theorem boundedConstructible_derivedReduction_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) X
      ((derivedReduction X ℓ E).obj K) :=
  sorry

/-- Blueprint `sk-lem-pe-derived-nakayama` (section `sec-proetale-coefficients`): a morphism
between derived complete `𝒪_{E,X}`-complexes is an isomorphism whenever its derived reduction is
one. Here it is applied to bounded constructible `𝒪_E`-complexes on a noetherian scheme, which
are derived complete by `sk-prop-integral-criterion`, (1) ⇒ (2), and to the reduction modulo
`ℓ = π_E^e` (up to a unit), whose vanishing implies that of the first reduction
`K ⊗ᴸ (𝒪_E ⧸ π_E)_X = (K ⊗ᴸ (𝒪_E ⧸ ℓ)_X) ⊗ᴸ_{(𝒪_E ⧸ ℓ)_X} (𝒪_E ⧸ π_E)_X`; regarding the
reduction with coefficients `ℤ/ℓ` does not change whether it is an isomorphism. -/
theorem isIso_of_isIso_derivedReduction_map
    {K L : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)}
    (φ : K ⟶ L)
    (h : IsIso ((derivedReduction X ℓ E).map ((boundedConstructible _).ι.map φ))) :
    IsIso φ :=
  sorry

end AlgebraicGeometry.ProEtale
