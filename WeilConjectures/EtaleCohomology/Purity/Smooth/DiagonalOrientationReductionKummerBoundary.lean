/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionKummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsFrame
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange

/-!
# The reduction of coefficients and the localization boundaries

Let `Ψ = - ⊗ᴸ_Λ Λ'` be the derived extension of scalars along a surjection `ρ : Λ →+* Λ'` of
finite rings with principal kernel. This file shows that `Ψ` commutes with the boundary of the
supported localization triangle `Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶ [1]`
(`AlgebraicGeometry.Etale.map_supportedLocalizationBoundary_comp`), hence with the localization
boundaries on classes `H¹(U_f, Λ(1)) ⟶ H²_{V(f)}(U, Λ(1))`
(`AlgebraicGeometry.Etale.reductionSupportedCoefficientChange_mapSupportedClass_localizationBoundaryClass`,
the hypothesis `hδ` of `MonoidalSupportedCoefficientChange.preservesKummerBoundaries`, blueprint
`det-sp-purity-coefficient-change`), given identifications `σ X : Ψ Λ_X(1) ≅ Λ'_X(1)` compatible
with restriction and with the Tate data. Along the way, the comparisons of `Ψ` with `Le^*` and
`Rj_*` are shown to commute with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section Shift

variable {U X : Scheme.{u}} (e : U ⟶ X)

instance commShift_leftDerivedUpperStarRestrictScalarsIso_hom :
    NatTrans.CommShift (leftDerivedUpperStarRestrictScalarsIso ρ e).hom ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} Λ) e).inv ℤ := NatTrans.CommShift.of_iso_inv _ ℤ
  dsimp only [leftDerivedUpperStarRestrictScalarsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

instance commShift_derivedExtendScalarsPullbackMap :
    NatTrans.CommShift (derivedExtendScalarsPullbackMap hρ ha e) ℤ := by
  dsimp only [derivedExtendScalarsPullbackMap, mateEquiv, Equiv.coe_fn_symm_mk, TwoSquare.natTrans,
    TwoSquare.mk]
  infer_instance

instance commShift_derivedExtendScalarsPullbackIso_inv :
    NatTrans.CommShift (derivedExtendScalarsPullbackIso hρ ha e).inv ℤ :=
  have : NatTrans.CommShift (derivedExtendScalarsPullbackIso hρ ha e).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (derivedExtendScalarsPullbackMap hρ ha e) ℤ)
  NatTrans.CommShift.of_iso_inv _ ℤ

instance commShift_derivedExtendScalarsLowerStarMap :
    NatTrans.CommShift (derivedExtendScalarsLowerStarMap hρ ha e) ℤ :=
  NatTrans.CommShift.mateEquiv _ _ _

end Shift

section Boundary

variable [Finite Λ] [Finite Λ'] {X Z V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The comparison of supports `Ψ(Ri_! Ri^! L) ⟶ Ri_! Ri^! L'` of the derived extension of scalars,
for `σ : Ψ L ≅ L'`: the commutation of `Ψ` with `Ri_!`, followed by `Ri_!` of the comparison
`Ψ Ri^! L ⟶ Ri^! Ψ L` and of `Ri^! σ`. -/
noncomputable def derivedExtendScalarsSupportsMap {L : 𝐃(X, Λ)} {L' : 𝐃(X, Λ')}
    (σ : (derivedExtendScalars hρ ha X).obj L ≅ L') :
    (derivedExtendScalars hρ ha X).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) ⟶
      (R(i)_![ModuleCat.{u + 1} Λ']).obj ((R(i)^![Λ']).obj L') :=
  (derivedExtendScalarsLowerShriekIso hρ ha i).hom.app _ ≫
    (R(i)_![ModuleCat.{u + 1} Λ']).map ((derivedExtendScalarsUpperShriekMap hρ ha i).app L ≫
      (R(i)^![Λ']).map σ.hom)

/-- The comparison of supports is compatible with the counits of `Ri_! ⊣ Ri^!`. -/
@[reassoc]
lemma derivedExtendScalarsSupportsMap_comp_counit {L : 𝐃(X, Λ)} {L' : 𝐃(X, Λ')}
    (σ : (derivedExtendScalars hρ ha X).obj L ≅ L') :
    derivedExtendScalarsSupportsMap hρ ha i σ ≫
        (rightDerivedUpperShriekAdjunction Λ' i).counit.app L' =
      (derivedExtendScalars hρ ha X).map ((rightDerivedUpperShriekAdjunction Λ i).counit.app L) ≫
        σ.hom := by
  rw [derivedExtendScalarsSupportsMap, Functor.map_comp, Category.assoc, Category.assoc,
    (rightDerivedUpperShriekAdjunction Λ' i).counit_naturality σ.hom,
    reassoc_of% (map_derivedExtendScalarsUpperShriekMap_app_comp_counit hρ ha i L),
    Iso.hom_inv_id_app_assoc]

/-- **The derived extension of scalars commutes with the supported localization boundary.** Let
`i : Z ⟶ X` be a closed immersion with open complement `j : V ⟶ X`. For `L ∈ D(X_ét, Λ)` and
`σ : Ψ L ≅ L'`, the boundaries `δ_L` and `δ_{L'}` of the supported localization triangles are
compatible with the comparison of supports and the comparison `Ψ Rj_* ⟶ Rj_* Ψ`:

```
  Ψ Rj_* Lj^* L ──Ψ δ_L──▶ Ψ((Ri_! Ri^! L)[1]) ≅ (Ψ Ri_! Ri^! L)[1]
        │                                            │
        ▼                                            ▼
  Rj_* Lj^* L' ──────────δ_{L'}──────────▶ (Ri_! Ri^! L')[1]
```

The image under `Ψ` of the triangle of `L` is distinguished and its first term is supported on
`Z`, so `σ` extends uniquely to a morphism of triangles towards the triangle of `L'`
[BBD, 1.1.9]; its outer components are the comparisons, characterized by the adjacent squares. -/
theorem map_supportedLocalizationBoundary_comp (j : V ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (L : 𝐃(X, Λ)) (L' : 𝐃(X, Λ'))
    (σ : (derivedExtendScalars hρ ha X).obj L ≅ L') :
    (derivedExtendScalars hρ ha X).map (supportedLocalizationBoundary Λ i j hij L) ≫
        ((derivedExtendScalars hρ ha X).commShiftIso (1 : ℤ)).hom.app _ ≫
          (derivedExtendScalarsSupportsMap hρ ha i σ)⟦(1 : ℤ)⟧' =
      (derivedExtendScalarsLowerStarMap hρ ha j).app _ ≫
        (R((j)_*[ModuleCat.{u + 1} Λ'])).map ((derivedExtendScalarsPullbackIso hρ ha j).hom.app L ≫
          (L((j)^*[ModuleCat.{u + 1} Λ'])).map σ.hom) ≫
          supportedLocalizationBoundary Λ' i j hij L' := by
  set T₁ := (derivedExtendScalars hρ ha X).mapTriangle.obj
    (supportedLocalizationTriangle Λ i j L (supportedLocalizationBoundary Λ i j hij L))
  have hT₁ : T₁ ∈ distTriang _ :=
    (derivedExtendScalars hρ ha X).map_distinguished _
      (supportedLocalizationTriangle_mem_distTriang Λ i j hij L)
  have hT₂ := supportedLocalizationTriangle_mem_distTriang Λ' i j hij L'
  have e₂ : T₁.mor₂ = (derivedExtendScalars hρ ha X).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app L) := rfl
  have e₃ : T₁.mor₃ = (derivedExtendScalars hρ ha X).map (supportedLocalizationBoundary Λ i j hij L) ≫
      ((derivedExtendScalars hρ ha X).commShiftIso (1 : ℤ)).hom.app _ := rfl
  -- the first term is supported on `Z`
  have hz : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ'])).obj T₁.obj₁) :=
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ') i
      j (by rw [hij]; exact disjoint_compl_left) j subset_rfl _).of_iso
      ((L((j)^*[ModuleCat.{u + 1} Λ'])).mapIso ((derivedExtendScalarsLowerShriekIso hρ ha i).app _))
  have hz₁ : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ'])).obj (T₁.obj₁⟦(1 : ℤ)⟧)) :=
    ((shiftFunctor _ (1 : ℤ)).map_isZero hz).of_iso
      (((L((j)^*[ModuleCat.{u + 1} Λ'])).commShiftIso (1 : ℤ)).app _)
  have : Subsingleton (T₁.obj₁⟦(1 : ℤ)⟧ ⟶ (supportedLocalizationTriangle Λ' i j L'
      (supportedLocalizationBoundary Λ' i j hij L')).obj₃) :=
    subsingleton_hom_rightDerivedLowerStar_of_isZero (ModuleCat.{u + 1} Λ') j hz₁ _
  -- the middle component `σ` extends to a morphism of triangles
  obtain ⟨φ, hφ⟩ := exists_triangleHom_of_comp_eq_zero hT₁ hT₂ σ.hom
    (@Subsingleton.elim _ (subsingleton_hom_rightDerivedLowerStar_of_isZero
      (ModuleCat.{u + 1} Λ') j hz _) _ _)
  -- its first component is the comparison of supports
  have h₁ : φ.hom₁ = derivedExtendScalarsSupportsMap hρ ha i σ :=
    (existsUnique_comp_counit_of_isZero Λ' i j hij hz _).unique
      (by have h := φ.comm₁; rw [hφ] at h; exact h.symm)
      (derivedExtendScalarsSupportsMap_comp_counit hρ ha i σ)
  -- its last component is the comparison `Ψ Rj_* ⟶ Rj_* Ψ`
  have h₃ : φ.hom₃ = (derivedExtendScalarsLowerStarMap hρ ha j).app _ ≫
      (R((j)_*[ModuleCat.{u + 1} Λ'])).map ((derivedExtendScalarsPullbackIso hρ ha j).hom.app L ≫
        (L((j)^*[ModuleCat.{u + 1} Λ'])).map σ.hom) := by
    refine Triangle.cancel_mor₂_of_subsingleton hT₁ ?_
    rw [φ.comm₂, hφ]
    rw [e₂]
    erw [map_unit_comp_derivedExtendScalarsLowerStarMap_app_assoc]
    dsimp only [Functor.id_obj]
    rw [← Functor.map_comp, Iso.inv_hom_id_app_assoc]
    exact ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') j).unit_naturality
      σ.hom).symm
  have h := φ.comm₃
  rw [h₁, h₃] at h
  rw [e₃, Category.assoc, Category.assoc] at h
  exact h


/-- **The comparison of supports commutes with shifts**: through the shift compatibilities
`(Ri_! Ri^! L)[n] ≅ Ri_! Ri^! (L[n])` of `Ri_!` and `Ri^!`, the comparison of supports at `L[n]`
(along `Ψ(L[n]) ≅ (Ψ L)[n] ≅ L'[n]`) is the shift of the comparison of supports at `L`. Both
sides are maps out of an object supported on `Z`, so they are determined by their composites
with the counit. -/
lemma map_shiftSupports_comp_derivedExtendScalarsSupportsMap {L : 𝐃(X, Λ)} {L' : 𝐃(X, Λ')}
    (σ : (derivedExtendScalars hρ ha X).obj L ≅ L') (n : ℤ) :
    (derivedExtendScalars hρ ha X).map (((R(i)_![ModuleCat.{u + 1} Λ]).commShiftIso n).inv.app _ ≫
        (R(i)_![ModuleCat.{u + 1} Λ]).map (((R(i)^![Λ]).commShiftIso n).inv.app L)) ≫
        derivedExtendScalarsSupportsMap hρ ha i
          (((derivedExtendScalars hρ ha X).commShiftIso n).app L ≪≫ (shiftFunctor _ n).mapIso σ) =
      ((derivedExtendScalars hρ ha X).commShiftIso n).hom.app _ ≫
        (derivedExtendScalarsSupportsMap hρ ha i σ)⟦n⟧' ≫
          ((R(i)_![ModuleCat.{u + 1} Λ']).commShiftIso n).inv.app _ ≫
            (R(i)_![ModuleCat.{u + 1} Λ']).map (((R(i)^![Λ']).commShiftIso n).inv.app L') := by
  have := (rightDerivedUpperShriekAdjunction Λ i).commShift_of_leftAdjoint ℤ
  have := (rightDerivedUpperShriekAdjunction Λ' i).commShift_of_leftAdjoint ℤ
  have hd : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  have hz : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ'])).obj
      ((derivedExtendScalars hρ ha X).obj
        (((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))⟦n⟧))) := by
    refine ((shiftFunctor _ n).map_isZero
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ')
        i i.openComplement.ι hd i.openComplement.ι subset_rfl
        ((derivedExtendScalars hρ ha Z).obj ((R(i)^![Λ]).obj L)))).of_iso ?_
    exact (L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ'])).mapIso
        (((derivedExtendScalars hρ ha X).commShiftIso n).app _ ≪≫
          (shiftFunctor _ n).mapIso ((derivedExtendScalarsLowerShriekIso hρ ha i).app _)) ≪≫
      ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ'])).commShiftIso n).app _
  refine (existsUnique_comp_counit_of_isZero Λ' i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι hz _).unique ?_ rfl
  have h₁ := (rightDerivedUpperShriekAdjunction Λ i).commShiftIso_inv_app_counit_app ℤ n L
  have h₂ := (rightDerivedUpperShriekAdjunction Λ' i).commShiftIso_inv_app_counit_app ℤ n L'
  simp only [Functor.commShiftIso_comp_inv_app, Category.assoc] at h₁ h₂
  rw [Category.assoc, derivedExtendScalarsSupportsMap_comp_counit, ← Functor.map_comp_assoc,
    Category.assoc, h₁, Category.assoc, Category.assoc, Category.assoc, h₂,
    ← Functor.map_comp, derivedExtendScalarsSupportsMap_comp_counit, Functor.map_comp,
    ← Functor.commShiftIso_hom_naturality_assoc]
  rfl


omit [Finite Λ] [Finite Λ'] in
/-- The image under `Ψ` of the adjoint `K ⟶ Rj_* (M[1]) ≅ (Rj_* M)[1]` of a class
`y : Lj^* K ⟶ M[1]`, followed by the comparison `Ψ Rj_* ⟶ Rj_* Ψ` and `w : Ψ M ⟶ N`, is the
adjoint of `Lj^* Ψ K ≅ Ψ Lj^* K ⟶ Ψ(M[1]) ≅ (Ψ M)[1] ⟶ N[1]`: this combines the compatibility of
the comparison with the units, its naturality and its compatibility with the shifts. -/
lemma map_adjoint_comp_derivedExtendScalarsLowerStarMap (j : V ⟶ X) (K : 𝐃(X, Λ)) (M : 𝐃(V, Λ))
    (N : 𝐃(V, Λ')) (y : (L((j)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ M⟦(1 : ℤ)⟧)
    (w : (derivedExtendScalars hρ ha V).obj M ⟶ N) :
    (derivedExtendScalars hρ ha X).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K ≫
          (R((j)_*[ModuleCat.{u + 1} Λ])).map y ≫
            ((R((j)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app M) ≫
        ((derivedExtendScalars hρ ha X).commShiftIso (1 : ℤ)).hom.app _ ≫
          ((derivedExtendScalarsLowerStarMap hρ ha j).app M ≫
            (R((j)_*[ModuleCat.{u + 1} Λ'])).map w)⟦(1 : ℤ)⟧' =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') j).unit.app
          ((derivedExtendScalars hρ ha X).obj K) ≫
        (R((j)_*[ModuleCat.{u + 1} Λ'])).map ((derivedExtendScalarsPullbackIso hρ ha j).inv.app K ≫
          (derivedExtendScalars hρ ha V).map y ≫
            ((derivedExtendScalars hρ ha V).commShiftIso (1 : ℤ)).hom.app M ≫ w⟦(1 : ℤ)⟧') ≫
          ((R((j)_*[ModuleCat.{u + 1} Λ'])).commShiftIso (1 : ℤ)).hom.app N := by
  have h₁ := NatTrans.shift_app_comm (derivedExtendScalarsLowerStarMap hρ ha j) (1 : ℤ) M
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at h₁
  have h₂ := (derivedExtendScalarsLowerStarMap hρ ha j).naturality y
  have h₃ := map_unit_comp_derivedExtendScalarsLowerStarMap_app hρ ha j K
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁]
  erw [reassoc_of% h₂]
  rw [reassoc_of% h₃, ← Functor.commShiftIso_hom_naturality]

omit [Finite Λ] [Finite Λ'] in
/-- The image under a functor commuting with shifts of a degree-one class `g` read in degree two
through `(Q[1])[1] ≅ Q[2]`. -/
lemma _root_.CategoryTheory.Functor.map_shift_comp_shiftFunctorAdd'_inv_app {C D : Type*}
    [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
    {P Q : C} {Q' : D} (g : P ⟶ Q⟦(1 : ℤ)⟧) (S : F.obj Q ⟶ Q') :
    F.map (g⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).inv.app Q) ≫
        (F.commShiftIso (2 : ℤ)).hom.app Q ≫ S⟦(2 : ℤ)⟧' =
      (F.commShiftIso (1 : ℤ)).hom.app P ≫
        (F.map g ≫ (F.commShiftIso (1 : ℤ)).hom.app Q ≫ S⟦(1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' D (1 : ℤ) 1 2 rfl).inv.app Q' := by
  have h := (shiftFunctorAdd' D (1 : ℤ) 1 2 rfl).inv.naturality S
  simp only [Functor.comp_obj, Functor.comp_map] at h
  rw [F.commShiftIso_add' (a := (1 : ℤ)) (b := 1) (c := 2) rfl, Functor.CommShift.isoAdd'_hom_app,
    Category.assoc, ← F.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id, Category.assoc]
  rw [F.commShiftIso_hom_naturality_assoc]
  simp only [Functor.map_comp, Category.assoc, h]


end Boundary

section Constant

/-- The identifications `Ψ Λ_X ≅ Λ'_X` are compatible with the derived pullbacks, in the form
used to restrict classes. -/
@[reassoc]
lemma leftDerivedUpperStar_map_derivedExtendScalarsConstantComplexIso_inv {U X : Scheme.{u}}
    (e : U ⟶ X) :
    (L((e)^*[ModuleCat.{u + 1} Λ'])).map (derivedExtendScalarsConstantComplexIso hρ ha X).inv ≫
        (derivedExtendScalarsPullbackIso hρ ha e).inv.app _ ≫
          (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarConstantComplexIso Λ e).hom =
      (leftDerivedUpperStarConstantComplexIso Λ' e).hom ≫
        (derivedExtendScalarsConstantComplexIso hρ ha U).inv := by
  rw [← cancel_mono (derivedExtendScalarsConstantComplexIso hρ ha U).hom, Category.assoc,
    Category.assoc, derivedExtendScalarsConstantComplexIso_hom_pullback, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Constant

section Class

attribute [local instance] HasInvertibleExponent.opens

variable [Finite Λ] [Finite Λ'] [HasTateTwist Λ] [HasTateTwist Λ'] {U : Scheme.{u}}
  [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] (f : Γ(U, ⊤))

/-- **The derived extension of scalars commutes with the localization boundary on classes**
(`AlgebraicGeometry.Etale.localizationBoundaryClass`), through identifications
`σ_U : Ψ Λ_U(1) ≅ Λ'_U(1)` and `σ_{U_f} : Ψ Λ_{U_f}(1) ≅ Λ'_{U_f}(1)` compatible with the
restriction to `U_f`: the image of `∂α` under `Ψ`, read in `H²_{V(f)}(U, Λ'(1))` through the
comparison of supports, is `∂` of the image of `α`. -/
theorem derivedExtendScalars_map_localizationBoundaryClass
    (σU : (derivedExtendScalars hρ ha U).obj (tateObject Λ U 1) ≅ tateObject Λ' U 1)
    (σV : (derivedExtendScalars hρ ha (U.basicOpen f)).obj (tateObject Λ (U.basicOpen f) 1) ≅
      tateObject Λ' (U.basicOpen f) 1)
    (hσ : (derivedExtendScalars hρ ha (U.basicOpen f)).map
        (leftDerivedUpperStarTateObjectIso (Λ := Λ) (U.basicOpen f).ι 1).hom ≫ σV.hom =
      (derivedExtendScalarsPullbackIso hρ ha (U.basicOpen f).ι).hom.app _ ≫
        (L(((U.basicOpen f).ι)^*[ModuleCat.{u + 1} Λ'])).map σU.hom ≫
          (leftDerivedUpperStarTateObjectIso (Λ := Λ') (U.basicOpen f).ι 1).hom)
    (α : constantComplex Λ (U.basicOpen f) ⟶ (tateObject Λ (U.basicOpen f) 1)⟦(1 : ℤ)⟧) :
    (derivedExtendScalarsConstantComplexIso hρ ha U).inv ≫
        (derivedExtendScalars hρ ha U).map (localizationBoundaryClass Λ f α) ≫
          ((derivedExtendScalars hρ ha U).commShiftIso (2 : ℤ)).hom.app _ ≫
            (derivedExtendScalarsSupportsMap hρ ha (U.zeroLocusSubschemeι {f}) σU)⟦(2 : ℤ)⟧' =
      localizationBoundaryClass Λ' f ((derivedExtendScalarsConstantComplexIso hρ ha _).inv ≫
        (derivedExtendScalars hρ ha _).map α ≫
          ((derivedExtendScalars hρ ha _).commShiftIso (1 : ℤ)).hom.app _ ≫ σV.hom⟦(1 : ℤ)⟧') := by
  have hij := range_zeroLocusSubschemeι_singleton f
  have key₁ := Functor.map_shift_comp_shiftFunctorAdd'_inv_app (derivedExtendScalars hρ ha U)
    (supportedLocalizationBoundary Λ (U.zeroLocusSubschemeι {f}) (U.basicOpen f).ι hij
      (tateObject Λ U 1))
    (derivedExtendScalarsSupportsMap hρ ha (U.zeroLocusSubschemeι {f}) σU)
  have key₂ := map_supportedLocalizationBoundary_comp hρ ha (U.zeroLocusSubschemeι {f})
    (U.basicOpen f).ι hij _ _ σU
  have key₃ := map_adjoint_comp_derivedExtendScalarsLowerStarMap hρ ha (U.basicOpen f).ι
    (constantComplex Λ U) _ _ ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫
      α ≫ (leftDerivedUpperStarTateObjectIso (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧')
    ((derivedExtendScalarsPullbackIso hρ ha (U.basicOpen f).ι).hom.app _ ≫
      (L(((U.basicOpen f).ι)^*[ModuleCat.{u + 1} Λ'])).map σU.hom)
  -- the restriction to `U_f` of the class
  have h₁ := leftDerivedUpperStar_map_derivedExtendScalarsConstantComplexIso_inv hρ ha
    (U.basicOpen f).ι
  have h₂ : (derivedExtendScalars hρ ha (U.basicOpen f)).map
        (leftDerivedUpperStarTateObjectIso (Λ := Λ) (U.basicOpen f).ι 1).inv ≫
      (derivedExtendScalarsPullbackIso hρ ha (U.basicOpen f).ι).hom.app _ ≫
        (L(((U.basicOpen f).ι)^*[ModuleCat.{u + 1} Λ'])).map σU.hom =
      σV.hom ≫ (leftDerivedUpperStarTateObjectIso (Λ := Λ') (U.basicOpen f).ι 1).inv := by
    rw [← cancel_mono (leftDerivedUpperStarTateObjectIso (Λ := Λ') (U.basicOpen f).ι 1).hom,
      Category.assoc, Category.assoc, ← hσ, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have h₂s := (shiftFunctor _ (1 : ℤ)).congr_map h₂
  rw [localizationBoundaryClass, localizationBoundaryClass, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit]
  have key₂s := (shiftFunctor _ (1 : ℤ)).congr_map key₂
  simp only [Functor.map_comp, Category.assoc] at key₁ key₂s key₃ h₂s ⊢
  rw [key₁, reassoc_of% key₂s, reassoc_of% key₃]
  have hn := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') (U.basicOpen f).ι).unit.naturality
    (derivedExtendScalarsConstantComplexIso hρ ha U).inv
  have hν := ((derivedExtendScalars hρ ha (U.basicOpen f)).commShiftIso (1 : ℤ)).hom.naturality
    (leftDerivedUpperStarTateObjectIso (Λ := Λ) (U.basicOpen f).ι 1).inv
  have h₁' := (R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ'])).congr_map h₁
  have hν' := (R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ'])).congr_map hν
  have h₂' := (R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ'])).congr_map h₂s
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
    Functor.map_comp] at hn h₁' hν' h₂'
  simp only [reassoc_of% hn, reassoc_of% h₁', reassoc_of% hν', reassoc_of% h₂']

omit [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] in
/-- The functor of `reductionSupportedCoefficientChange` is the derived extension of scalars. -/
lemma reductionSupportedCoefficientChange_functor
    (τ : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha) (X : Scheme.{u}) :
    (reductionSupportedCoefficientChange hρ ha τ).functor X = derivedExtendScalars hρ ha X :=
  rfl

omit [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] in
/-- The identification of the constant complexes of `reductionSupportedCoefficientChange`. -/
lemma reductionSupportedCoefficientChange_constantComplexIso
    (τ : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha) (X : Scheme.{u}) :
    (reductionSupportedCoefficientChange hρ ha τ).constantComplexIso X =
      derivedExtendScalarsConstantComplexIso hρ ha X := by
  unfold reductionSupportedCoefficientChange
  rfl

omit [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] in
/-- The comparison of supports of `AlgebraicGeometry.Etale.reductionSupportedCoefficientChange`
is `AlgebraicGeometry.Etale.derivedExtendScalarsSupportsMap`: both are characterized by their
composites with the counit. -/
lemma reductionSupportedCoefficientChange_supportsMap
    (τ : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha) {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {L : 𝐃(X, Λ)} {L' : 𝐃(X, Λ')}
    (σ : (derivedExtendScalars hρ ha X).obj L ≅ L') :
    (reductionSupportedCoefficientChange hρ ha τ).supportsMap i σ =
      derivedExtendScalarsSupportsMap hρ ha i σ := by
  have hd : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  have hz : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ'])).obj
      ((derivedExtendScalars hρ ha X).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)))) :=
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ')
      i i.openComplement.ι hd i.openComplement.ι subset_rfl
      ((derivedExtendScalars hρ ha Z).obj ((R(i)^![Λ]).obj L))).of_iso
      ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ'])).mapIso
        ((derivedExtendScalarsLowerShriekIso hρ ha i).app _))
  exact (existsUnique_comp_counit_of_isZero Λ' i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι hz _).unique
    ((reductionSupportedCoefficientChange hρ ha τ).supportsMap_comp_counit i σ)
    (derivedExtendScalarsSupportsMap_comp_counit hρ ha i σ)

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of coefficients commutes with the localization boundaries on classes** (the
hypothesis `hδ` of `MonoidalSupportedCoefficientChange.preservesKummerBoundaries`), for Tate data
`τ` whose degree-one component is `Ψ(Λ_U(1)[2]) ≅ (Ψ Λ_U(1))[2] ≅ Λ'_U(1)[2]` for identifications
`σ X : Ψ Λ_X(1) ≅ Λ'_X(1)` compatible with the restriction to `U_f`. -/
theorem reductionSupportedCoefficientChange_mapSupportedClass_localizationBoundaryClass
    (τ : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha)
    (σ : ∀ (X : Scheme.{u}) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X],
      (derivedExtendScalars hρ ha X).obj (tateObject Λ X 1) ≅ tateObject Λ' X 1)
    (hτ : (τ.iso U 1).hom = ((derivedExtendScalars hρ ha U).commShiftIso (2 * 1 : ℤ)).hom.app _ ≫
      (σ U).hom⟦(2 * 1 : ℤ)⟧')
    (hσ : (derivedExtendScalars hρ ha (U.basicOpen f)).map
        (leftDerivedUpperStarTateObjectIso (Λ := Λ) (U.basicOpen f).ι 1).hom ≫ (σ _).hom =
      (derivedExtendScalarsPullbackIso hρ ha (U.basicOpen f).ι).hom.app _ ≫
        (L(((U.basicOpen f).ι)^*[ModuleCat.{u + 1} Λ'])).map (σ U).hom ≫
          (leftDerivedUpperStarTateObjectIso (Λ := Λ') (U.basicOpen f).ι 1).hom)
    (α : constantComplex Λ (U.basicOpen f) ⟶ (tateObject Λ (U.basicOpen f) 1)⟦(1 : ℤ)⟧) :
    (reductionSupportedCoefficientChange hρ ha τ).mapSupportedClass _
        ((reductionSupportedCoefficientChange hρ ha τ).tateShiftIso U 1)
        (shiftSupportedClass Λ _ 2 (localizationBoundaryClass Λ f α)) =
      shiftSupportedClass Λ' _ 2 (localizationBoundaryClass Λ' f
        (((reductionSupportedCoefficientChange hρ ha τ).constantComplexIso _).inv ≫
          ((reductionSupportedCoefficientChange hρ ha τ).functor _).map α ≫
            (((derivedExtendScalars hρ ha _).commShiftIso (1 : ℤ)).app _ ≪≫
              (shiftFunctor _ (1 : ℤ)).mapIso (σ _)).hom)) := by
  have hτ₂ : (reductionSupportedCoefficientChange hρ ha τ).tateShiftIso U 1 =
      ((derivedExtendScalars hρ ha U).commShiftIso (2 : ℤ)).app _ ≪≫
        (shiftFunctor _ (2 : ℤ)).mapIso (σ U) := Iso.ext hτ
  have hs := map_shiftSupports_comp_derivedExtendScalarsSupportsMap hρ ha
    (U.zeroLocusSubschemeι {f}) (σ U) 2
  have hb := derivedExtendScalars_map_localizationBoundaryClass hρ ha f (σ U) (σ _) hσ α
  rw [SupportedCoefficientChange.mapSupportedClass, hτ₂, shiftSupportedClass, shiftSupportedClass,
    Functor.map_comp]
  have key : (derivedExtendScalarsConstantComplexIso hρ ha U).inv ≫
      ((derivedExtendScalars hρ ha U).map (localizationBoundaryClass Λ f α) ≫
        (derivedExtendScalars hρ ha U).map
          (((R(U.zeroLocusSubschemeι {f})_![ModuleCat.{u + 1} Λ]).commShiftIso (2 : ℤ)).inv.app _ ≫
            (R(U.zeroLocusSubschemeι {f})_![ModuleCat.{u + 1} Λ]).map
              (((R(U.zeroLocusSubschemeι {f})^![Λ]).commShiftIso (2 : ℤ)).inv.app _))) ≫
        derivedExtendScalarsSupportsMap hρ ha (U.zeroLocusSubschemeι {f})
          (((derivedExtendScalars hρ ha U).commShiftIso (2 : ℤ)).app (tateObject Λ U 1) ≪≫
            (shiftFunctor _ (2 : ℤ)).mapIso (σ U)) =
      localizationBoundaryClass Λ' f ((derivedExtendScalarsConstantComplexIso hρ ha _).inv ≫
          (derivedExtendScalars hρ ha _).map α ≫
            ((derivedExtendScalars hρ ha _).commShiftIso (1 : ℤ)).hom.app _ ≫
              (σ _).hom⟦(1 : ℤ)⟧') ≫
        ((R(U.zeroLocusSubschemeι {f})_![ModuleCat.{u + 1} Λ']).commShiftIso (2 : ℤ)).inv.app _ ≫
          (R(U.zeroLocusSubschemeι {f})_![ModuleCat.{u + 1} Λ']).map
            (((R(U.zeroLocusSubschemeι {f})^![Λ']).commShiftIso (2 : ℤ)).inv.app _) := by
    rw [Category.assoc, hs, reassoc_of% hb]
  rw [reductionSupportedCoefficientChange_supportsMap]
  simp only [reductionSupportedCoefficientChange_constantComplexIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, reductionSupportedCoefficientChange_functor]
  convert key using 3

end Class


end Etale

end AlgebraicGeometry
