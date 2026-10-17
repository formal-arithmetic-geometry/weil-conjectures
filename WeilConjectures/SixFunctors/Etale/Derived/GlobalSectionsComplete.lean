/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.SmulInvertible
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-!
# Derived global sections, linearity and reduction modulo a nonzerodivisor

Let `Λ` be a commutative ring. This file records three facts about the passage from
`D(X_ét, Λ)` to complexes of `Λ`-modules used at the integral stage of `sk-lem-finite`:

- `AlgebraicGeometry.Etale.linear_rightDerivedGlobalSections`: the derived global sections
  `RΓ(X, -)` are `Λ`-linear, being right adjoint to the derived constant sheaf functor;
- `AlgebraicGeometry.Etale.rightDerivedGlobalSections_hom_eq_zero`: if `M ∈ D(X_ét, Λ)` receives
  no nonzero map from an object on which `ϖ` acts invertibly (for `ϖ` a nonzerodivisor of `Λ`
  this is derived `ϖ`-completeness, `DerivedCategory.derivedComplete_iff_rightOrthogonal`),
  neither does `RΓ(X, M)`;
- `AlgebraicGeometry.Etale.exists_distinguished_smul_map_reductionModIdeal`: a triangulated
  `Λ`-linear functor `Φ` carries the triangle `K ──ϖⁿ──▶ K ⟶ K ⊗ᴸ Λ/(ϖⁿ) ⟶ K⟦1⟧` to a
  distinguished triangle `Φ K ──ϖⁿ──▶ Φ K ⟶ Φ(K ⊗ᴸ Λ/(ϖⁿ)) ⟶ Φ K⟦1⟧`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The derived global sections `RΓ(X, -)` are right adjoint to the derived constant sheaf
functor, the derived functor of the exact functor `M ↦ M_X`. -/
noncomputable def derivedConstantSheafGlobalSectionsAdjunction (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor ⊣
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X :=
  (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).derivedAdjunction

/-- The derived constant sheaf functor is `Λ`-linear, being isomorphic to the functor induced
on derived categories by the `Λ`-linear exact constant sheaf functor. -/
instance linear_leftDerivedFunctor_constantSheaf (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor.Linear Λ :=
  Functor.linear_of_iso Λ (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm

/-- The derived global sections `RΓ(X, -)` are `Λ`-linear, being right adjoint to a `Λ`-linear
functor. -/
instance linear_rightDerivedGlobalSections (X : Scheme.{u}) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).Linear Λ :=
  (derivedConstantSheafGlobalSectionsAdjunction X).right_adjoint_linear (R := Λ)

/-- The derived global sections `RΓ(X, -)` are triangulated, as every right derived functor. -/
instance isTriangulated_rightDerivedGlobalSections (X : Scheme.{u}) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
  inferInstanceAs
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated

/-- If `M ∈ D(X_ét, Λ)` receives no nonzero map from an object on which `ϖ` acts invertibly,
neither does `RΓ(X, M) ∈ D(Λ)`: a map `L ⟶ RΓ(X, M)` is the transpose of a map `L_X ⟶ M`, and
`ϖ` acts invertibly on `L_X`, the derived constant sheaf functor being `Λ`-linear. -/
lemma rightDerivedGlobalSections_hom_eq_zero {X : Scheme.{u}} {ϖ : Λ}
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal M)
    (L : _root_.DerivedCategory (ModuleCat.{u + 1} Λ))
    (f : L ⟶ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj M)
    (hL : IsIso (ϖ • 𝟙 L)) : f = 0 := by
  let adj := derivedConstantSheafGlobalSectionsAdjunction (Λ := Λ) X
  have := adj.right_adjoint_additive
  have hL' : IsIso (ϖ • 𝟙
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor.obj L)) := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  rw [← (adj.homEquiv L M).apply_symm_apply f, hM ((adj.homEquiv L M).symm f) hL',
    Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

/-- **Reduction modulo `ϖⁿ` through a triangulated linear functor.** For a nonzerodivisor `ϖ`
of `Λ`, `n : ℕ` and a triangulated `Λ`-linear functor `Φ` out of `D(X_ét, Λ)`, the image
`Φ(K ⊗ᴸ Λ/(ϖⁿ))` of the reduction of `K` is the third vertex of a distinguished triangle
`Φ K ──ϖⁿ──▶ Φ K ⟶ Φ(K ⊗ᴸ Λ/(ϖⁿ)) ⟶ Φ K⟦1⟧`: it is the image under `Φ(K ⊗ᴸ -)` of the
distinguished triangle `Λ ──ϖⁿ──▶ Λ ⟶ Λ/(ϖⁿ) ⟶ Λ⟦1⟧` of constant sheaves. -/
lemma exists_distinguished_smul_map_reductionModIdeal {D : Type*} [Category D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [Linear Λ D] {X : Scheme.{u}}
    (Φ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ D)
    [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Linear Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ (g : Φ.obj K ⟶ Φ.obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K))
      (h : Φ.obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) ⟶ (Φ.obj K)⟦(1 : ℤ)⟧),
      Triangle.mk (ϖ ^ n • 𝟙 (Φ.obj K)) g h ∈ distTriang D := by
  let FX := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  let TX := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ rfl n
  let T := Φ.mapTriangle.obj (FX.mapTriangle.obj TX)
  have hT : T ∈ distTriang D :=
    Φ.map_distinguished _ (FX.map_distinguished _
      (_root_.DerivedCategory.quotPowTriangle_distinguished _ hϖ rfl n))
  have h₁ : T.mor₁ = ϖ ^ n • 𝟙 T.obj₁ := by
    change Φ.map (FX.map TX.mor₁) = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
      CategoryTheory.Functor.map_id, Functor.map_smul, CategoryTheory.Functor.map_id]
  let e : T.obj₁ ≅ Φ.obj K := Φ.mapIso (derivedTensorSingleUnitIso K)
  refine ⟨e.inv ≫ T.mor₂, T.mor₃ ≫ e.hom⟦(1 : ℤ)⟧', isomorphic_distinguished T hT _ ?_⟩
  refine Triangle.isoMk _ _ e.symm e.symm (Iso.refl _) ?_ ?_ ?_
  · simp [h₁]
  · simp
  · simp only [Triangle.mk_mor₃, Iso.symm_hom, Iso.refl_hom, Category.id_comp, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.comp_id]

end AlgebraicGeometry.Etale
