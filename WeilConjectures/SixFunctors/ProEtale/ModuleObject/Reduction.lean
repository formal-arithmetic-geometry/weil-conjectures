/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersResidueField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.Sites.ModuleLift
public import WeilConjectures.CategoryTheory.ModuleObjects.SectionAction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.Sites.TraceFormula.ZModModuleLift

/-!

# The first derived reduction of integral module objects

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E = 𝒪_E ⧸ π_E`. The residue map `𝒪_E ⟶ 𝔽_E` is a continuous homomorphism onto a discrete
ring, hence induces a morphism of condensed rings `𝒪̲_E ⟶ 𝔽̲_E` and, pulled back to a scheme `X`,
a morphism of coefficient ring objects `𝒪_{E,X} ⟶ 𝔽_{E,X}`
(`ProEtale.padicIntegersToResidueField`). The residue field `𝔽_E` acts on every module object over
`𝔽_{E,X}` through the constant global sections, so that such a module object is a pro-étale sheaf
of `𝔽_E`-modules (`ProEtale.residueFieldModuleSheaf`). The *first derived reduction*
`K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` of blueprint `sk-def-pe-derived-completion`, as a complex of
pro-étale sheaves of `𝔽_E`-modules, is `ProEtale.derivedReduction`.

-/
@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace Profinite

open _root_.PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The residue map `𝒪̲_E ⟶ 𝔽̲_E` of ring objects of condensed abelian groups, induced by the
continuous residue map `𝒪_E ⟶ 𝔽_E` onto the discrete residue field. -/
noncomputable def padicIntegersRingObjToResidueField :
    padicIntegersRingObj.{u} ℓ E ⟶ continuousMapRingObj (integersResidueField ℓ E) :=
  letI := normedFieldOfAlgebra ℓ E
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap (integersResidue ℓ E) (continuous_integersResidue ℓ E))

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

instance : IsMonHom (padicIntegersRingObjToResidueField.{u} ℓ E) :=
  letI := normedFieldOfAlgebra ℓ E
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap (integersResidue ℓ E) (continuous_integersResidue ℓ E))))

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The coefficient ring object `𝔽_{E,X} = p_X^* 𝔽̲_E` on `X_proét`. -/
noncomputable abbrev residueFieldRingObj : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E)) X

/-- The residue map `𝒪_{E,X} ⟶ 𝔽_{E,X}` of coefficient ring objects on `X_proét`: the pullback
along `p_X` of the residue map `𝒪̲_E ⟶ 𝔽̲_E` of condensed rings. -/
noncomputable abbrev padicIntegersToResidueField :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X ⟶ residueFieldRingObj X ℓ E :=
  coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E) X

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

/-- The residue field `𝔽_E`, lifted to the universe `u + 1` of the coefficient rings of pro-étale
sheaves of modules on `u`-schemes. -/
def ResidueFieldCoeff : Type (u + 1) :=
  ULift.{u + 1} (integersResidueField ℓ E)

noncomputable instance : CommRing (ResidueFieldCoeff.{u} ℓ E) :=
  inferInstanceAs (CommRing (ULift.{u + 1} (integersResidueField ℓ E)))

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The prime `ℓ` is zero in `𝔽_E`. -/
lemma natCast_eq_zero_residueFieldCoeff : ((ℓ : ℕ) : ResidueFieldCoeff.{u} ℓ E) = 0 :=
  ULift.ext _ _ (natCast_eq_zero_integersResidueField ℓ E)

/-- The constants `𝔽_E ⟶ Γ(𝔽_{E,X})`: an element of the residue field `𝔽_E` is the constant
function `X → 𝔽_E`, a global section of `𝔽_{E,X} = C(-, 𝔽_E)_X`
(`ProEtale.continuousMapCoefficientSectionRingHom`). -/
noncomputable def residueFieldSectionRingHom :
    ResidueFieldCoeff.{u} ℓ E →+* Γ (residueFieldRingObj X ℓ E) :=
  (continuousMapCoefficientSectionRingHom X (integersResidueField ℓ E)).comp
    ((algebraMap (integersResidueField ℓ E) C(X, integersResidueField ℓ E)).comp
      (ULift.ringEquiv : ULift.{u + 1} (integersResidueField ℓ E) ≃+* _).toRingHom)

/-- An `𝔽_{E,X}`-module object, regarded as a pro-étale sheaf of `𝔽_E`-modules: `𝔽_E` acts through
the constant global sections of `𝔽_{E,X}` (`ProEtale.residueFieldSectionRingHom`). -/
noncomputable def residueFieldModuleSheaf :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) :=
  Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c))

instance : (residueFieldModuleSheaf X ℓ E).Additive :=
  inferInstanceAs (Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c))).Additive

instance : PreservesFiniteLimits (residueFieldModuleSheaf X ℓ E) :=
  inferInstanceAs (PreservesFiniteLimits (Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c))))

instance : PreservesFiniteColimits (residueFieldModuleSheaf X ℓ E) :=
  inferInstanceAs (PreservesFiniteColimits (Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c))))

instance : (residueFieldModuleSheaf X ℓ E).ReflectsIsomorphisms :=
  inferInstanceAs (Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f
      (residueFieldSectionRingHom X ℓ E c))).ReflectsIsomorphisms

/-- The **first derived reduction** `K ↦ K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` of complexes of
`𝒪_{E,X}`-module objects (blueprint `sk-def-pe-derived-completion`), regarded in the derived
category of pro-étale sheaves of `𝔽_E`-modules: the derived extension of scalars along the
residue map `𝒪_{E,X} ⟶ 𝔽_{E,X}`, followed by the exact functor
`ProEtale.residueFieldModuleSheaf`. -/
noncomputable def derivedReduction :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ⥤
      DerivedCategory (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E))) :=
  (Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor ⋙
    (residueFieldModuleSheaf X ℓ E).mapDerivedCategory

end AlgebraicGeometry.ProEtale
