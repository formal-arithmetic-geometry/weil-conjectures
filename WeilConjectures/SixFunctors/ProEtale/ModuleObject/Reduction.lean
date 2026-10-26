/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersResidueField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.Sites.ZModModuleLift
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

/-!

# The first derived reduction of integral module objects

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E = 𝒪_E ⧸ π_E`. The residue map `𝒪_E ⟶ 𝔽_E` is a continuous homomorphism onto a discrete
ring, hence induces a morphism of condensed rings `𝒪̲_E ⟶ 𝔽̲_E` and, pulled back to a scheme `X`,
a morphism of coefficient ring objects `𝒪_{E,X} ⟶ 𝔽_{E,X}`
(`ProEtale.padicIntegersToResidueField`). Since `ℓ = 0` in `𝔽_E`, every module object over
`𝔽_{E,X}` is killed by `ℓ` (`ProEtale.zsmul_id_eq_zero_of_residueField`), hence is a pro-étale
sheaf of `ℤ/ℓ`-modules (`ProEtale.residueFieldModuleSheaf`). The *first derived reduction*
`K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` of blueprint `sk-def-pe-derived-completion`, regarded with
coefficients `ℤ/ℓ`, is `ProEtale.derivedReduction`.

## Inputs from other subsections

- `ProEtale.boundedConstructible_derivedReduction_obj`: blueprint `sk-prop-integral-criterion`
  (section `sec-proetale-coefficients`), implication (1) ⇒ (2), second half.

-/
@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace Profinite

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The residue map `𝒪̲_E ⟶ 𝔽̲_E` of ring objects of condensed abelian groups, induced by the
continuous residue map `𝒪_E ⟶ 𝔽_E` onto the discrete residue field. -/
noncomputable def padicIntegersRingObjToResidueField :
    padicIntegersRingObj.{u} ℓ E ⟶ continuousMapRingObj (integersResidueField ℓ E) :=
  letI := normedFieldOfAlgebra ℓ E
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap (integersResidue ℓ E) (continuous_integersResidue ℓ E))

instance : IsMonHom (padicIntegersRingObjToResidueField.{u} ℓ E) :=
  letI := normedFieldOfAlgebra ℓ E
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap (integersResidue ℓ E) (continuous_integersResidue ℓ E))))

/-- Multiplication by `ℓ` is zero on the condensed ring `𝔽̲_E`. -/
lemma zsmul_id_continuousMapRingObj_integersResidueField :
    (ℓ : ℤ) • 𝟙 (continuousMapRingObj.{u} (integersResidueField ℓ E)) = 0 := by
  ext S x
  obtain ⟨x⟩ := x
  change ULift.up ((ℓ : ℤ) • x) = ULift.up 0
  congr 1
  ext s
  change (ℓ : ℤ) • x s = 0
  rw [natCast_zsmul, nsmul_eq_mul, natCast_eq_zero_integersResidueField, zero_mul]

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- The coefficient ring object `𝔽_{E,X} = p_X^* 𝔽̲_E` on `X_proét`. -/
noncomputable abbrev residueFieldRingObj : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) X

/-- The residue map `𝒪_{E,X} ⟶ 𝔽_{E,X}` of coefficient ring objects on `X_proét`: the pullback
along `p_X` of the residue map `𝒪̲_E ⟶ 𝔽̲_E` of condensed rings. -/
noncomputable abbrev padicIntegersToResidueField :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X ⟶ residueFieldRingObj X ℓ E :=
  coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X

/-- Multiplication by `ℓ` is zero on the coefficient ring object `𝔽_{E,X}`. -/
lemma zsmul_id_residueFieldRingObj : (ℓ : ℤ) • 𝟙 (residueFieldRingObj X ℓ E) = 0 := by
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  rw [← (upperStarFromPoint X).map_id, ← Functor.map_zsmul,
    Profinite.zsmul_id_continuousMapRingObj_integersResidueField, Functor.map_zero]

/-- Every module object over `𝔽_{E,X}` is killed by `ℓ`. -/
lemma zsmul_id_eq_zero_of_residueField
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E)) :
    (ℓ : ℤ) • 𝟙 M.X = 0 := by
  have h1 : η[residueFieldRingObj X ℓ E] ▷ M.X ≫
      ModObj.smul (M := residueFieldRingObj X ℓ E) (X := M.X) = (λ_ M.X).hom := by
    simpa using ModObj.one_smul (M := residueFieldRingObj X ℓ E) M.X
  have h2 : (ℓ : ℤ) • η[residueFieldRingObj X ℓ E] = 0 := by
    rw [← Category.comp_id η[residueFieldRingObj X ℓ E], ← Preadditive.comp_zsmul,
      zsmul_id_residueFieldRingObj, Limits.comp_zero]
  have h3 : ((ℓ : ℤ) • η[residueFieldRingObj X ℓ E]) ▷ M.X =
      (ℓ : ℤ) • (η[residueFieldRingObj X ℓ E] ▷ M.X) :=
    (tensorRight M.X).map_zsmul
  rw [h2, MonoidalPreadditive.zero_whiskerRight] at h3
  have h4 : (ℓ : ℤ) • (λ_ M.X).hom = 0 := by
    rw [← h1, ← Preadditive.zsmul_comp]
    exact (congrArg (· ≫ _) h3.symm).trans Limits.zero_comp
  rw [← Iso.inv_hom_id (λ_ M.X), ← Preadditive.comp_zsmul, h4, Limits.comp_zero]

/-- An `𝔽_{E,X}`-module object, regarded as a pro-étale sheaf of `ℤ/ℓ`-modules: its underlying
abelian sheaf is killed by `ℓ` (`ProEtale.zsmul_id_eq_zero_of_residueField`). -/
noncomputable def residueFieldModuleSheaf :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) :=
  Sheaf.zmodModuleLift ℓ (Mod.forget _) (zsmul_id_eq_zero_of_residueField X ℓ E)

instance : (residueFieldModuleSheaf X ℓ E).Additive :=
  inferInstanceAs
    (Sheaf.zmodModuleLift ℓ (Mod.forget _) (zsmul_id_eq_zero_of_residueField X ℓ E)).Additive

instance : PreservesFiniteLimits (residueFieldModuleSheaf X ℓ E) :=
  inferInstanceAs (PreservesFiniteLimits
    (Sheaf.zmodModuleLift ℓ (Mod.forget _) (zsmul_id_eq_zero_of_residueField X ℓ E)))

instance : PreservesFiniteColimits (residueFieldModuleSheaf X ℓ E) :=
  inferInstanceAs (PreservesFiniteColimits
    (Sheaf.zmodModuleLift ℓ (Mod.forget _) (zsmul_id_eq_zero_of_residueField X ℓ E)))

/-- The **first derived reduction** `K ↦ K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` of complexes of
`𝒪_{E,X}`-module objects (blueprint `sk-def-pe-derived-completion`), regarded in the derived
category of pro-étale sheaves of `ℤ/ℓ`-modules: the derived extension of scalars along the
residue map `𝒪_{E,X} ⟶ 𝔽_{E,X}`, followed by the exact functor
`ProEtale.residueFieldModuleSheaf`. -/
noncomputable def derivedReduction :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) ⥤
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
  (Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor ⋙
    (residueFieldModuleSheaf X ℓ E).mapDerivedCategory

/-! ### Inputs from other subsections -/

variable [IsNoetherian X]

/-- Blueprint `sk-prop-integral-criterion` (section `sec-proetale-coefficients`), implication
(1) ⇒ (2), its second half: on a noetherian scheme `X`, the first derived reduction
`K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` of a bounded constructible `𝒪_E`-complex `K` lies in
`Dᵇc(X, 𝔽_E)`. Here `K₁` is regarded with coefficients `ℤ/ℓ` (a sheaf of finite `𝔽_E`-modules is
constructible if and only if its underlying sheaf of `ℤ/ℓ`-modules is), and the finite-coefficient
`Dᵇc` is read as the complexes of étale origin (`ProEtale.DerivedCategory.boundedConstructible`;
for finite coefficients the two readings agree, blueprint `sk-thm-pe-constructible-comparison`).
-/
theorem boundedConstructible_derivedReduction_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) X
      ((derivedReduction X ℓ E).obj K) :=
  sorry


end AlgebraicGeometry.ProEtale
