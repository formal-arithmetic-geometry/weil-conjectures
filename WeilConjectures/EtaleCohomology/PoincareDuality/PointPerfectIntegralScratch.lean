/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DerivedCompleteScratch
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportTorsion

@[expose] public section

universe u

open CategoryTheory Opposite Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The derived global sections `RΓ(X, -)` are right adjoint to the (exact) constant sheaf
functor on derived categories. -/
noncomputable def derivedConstantSheafGlobalSectionsAdjunction (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor ⊣
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X :=
  (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).derivedAdjunction

example (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor.Linear Λ :=
  Functor.linear_of_iso Λ (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm


/-- The derived global sections are `Λ`-linear, being right adjoint to a `Λ`-linear functor. -/
instance linear_rightDerivedGlobalSections (X : Scheme.{u}) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).Linear Λ :=
  have : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor.Linear Λ :=
    Functor.linear_of_iso Λ (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm
  (derivedConstantSheafGlobalSectionsAdjunction X).right_adjoint_linear (R := Λ)

/-- If `M ∈ D(X_ét, Λ)` receives no nonzero map from objects on which `ϖ` acts invertibly, neither
does `RΓ(X, M) ∈ D(Λ)`. -/
lemma rightDerivedGlobalSections_hom_eq_zero {X : Scheme.{u}} {ϖ : Λ}
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal M)
    (L : _root_.DerivedCategory (ModuleCat.{u + 1} Λ))
    (f : L ⟶ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj M)
    (hL : IsIso (ϖ • 𝟙 L)) : f = 0 := by
  let adj := derivedConstantSheafGlobalSectionsAdjunction (Λ := Λ) X
  have : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor.Linear Λ :=
    Functor.linear_of_iso Λ (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm
  have := adj.right_adjoint_additive
  have hL' : _root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor.obj L) := by
    change IsIso (ϖ • 𝟙 _)
    rw [← Functor.map_id, ← Functor.map_smul]
    infer_instance
  rw [← (adj.homEquiv L M).apply_symm_apply f, hM ((adj.homEquiv L M).symm f) hL',
    Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

end AlgebraicGeometry.Etale
