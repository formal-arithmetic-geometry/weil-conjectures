/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# The residue field module sheaves are compatible with the derived tensor products

Write `G_X = residueFieldModuleSheaf X ℓ E` for the equivalence between module objects over
`𝔽_{E,X}` and pro-étale sheaves of `𝔽_E`-modules. The derived equivalences `D(G_X)` commute with
the derived tensor products, compatibly with the tensor comparisons of the derived pullbacks and
the isomorphisms `Lf^* ⋙ D(G_X) ≅ D(G_Y) ⋙ Lf^*` (`ProEtale.residueFieldDerivedUpperStarIso`)
(`ProEtale.exists_comparisonCompatible_residueFieldDerivedUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The residue field `𝔽_E` is a noetherian ring, being finite. -/
instance isNoetherianRing_residueFieldCoeff : IsNoetherianRing (ResidueFieldCoeff.{u} ℓ E) :=
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E)))
  inferInstance

/-- **`D(G)` is monoidal, compatibly with the derived pullbacks**: there are isomorphisms
`D(G_X)(A ⊗ᴸ B) ≅ D(G_X) A ⊗ᴸ D(G_X) B` such that the isomorphism
`Lf^* ⋙ D(G_X) ≅ D(G_Y) ⋙ Lf^*` is compatible with them and with the tensor comparisons of the
derived pullbacks of module objects over `𝔽̲_E` and of pro-étale sheaves of `𝔽_E`-modules. -/
theorem exists_comparisonCompatible_residueFieldDerivedUpperStarIso :
    ∃ (m_X : (Functor.postcompose₂.obj (residueFieldModuleSheaf X ℓ E).mapDerivedCategory).obj
        (curriedTensor _) ≅
      (((Functor.whiskeringLeft₂ _).obj (residueFieldModuleSheaf X ℓ E).mapDerivedCategory).obj
        (residueFieldModuleSheaf X ℓ E).mapDerivedCategory).obj (curriedTensor _))
      (m_Y : (Functor.postcompose₂.obj (residueFieldModuleSheaf Y ℓ E).mapDerivedCategory).obj
        (curriedTensor _) ≅
      (((Functor.whiskeringLeft₂ _).obj (residueFieldModuleSheaf Y ℓ E).mapDerivedCategory).obj
        (residueFieldModuleSheaf Y ℓ E).mapDerivedCategory).obj (curriedTensor _)),
      Adjunction.ComparisonCompatible (residueFieldDerivedUpperStarIso ℓ E f).symm
        (leftDerivedUpperStarTensor
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f)
        (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f)
        m_X m_Y :=
  sorry

end AlgebraicGeometry.ProEtale
