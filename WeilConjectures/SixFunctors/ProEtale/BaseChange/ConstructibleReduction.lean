/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow

/-!
# Linear triangulated functors and the reductions `K ⊗ᴸ R/Iⁿ`

Let `(C, J)` and `(C', J')` be essentially small sites, `R` a commutative ring and `ϖ ∈ R` a
nonzerodivisor generating the ideal `I`. For a triangulated `R`-linear functor
`Φ : D(J, R) ⥤ D(J', R)` and every object `K`, the reductions satisfy
`Φ(K ⊗ᴸ R/Iⁿ) ≅ Φ(K) ⊗ᴸ R/Iⁿ` (`DerivedCategory.nonempty_iso_map_derivedCompletionDiagram_obj`):
both are cones of the multiplication by `ϖⁿ` on `Φ(K)`. This is the commutation of the
finite-level operations with the reduction towers used in blueprint
`def-weil-pbc-witness-compatibility`.

Moreover a right adjoint of an `R`-linear functor preserves derived completeness
(`DerivedCategory.derivedComplete_obj_of_adjunction`), by the characterisation of derived
completeness as right orthogonality to the objects on which `ϖ` acts invertibly
(`DerivedCategory.derivedComplete_iff_rightOrthogonal`). This is the completeness clause of
blueprint `prop-weil-pbc-direct-image-limits` for `Rf_*`.

## Implementation notes

The monoidal structure of `D(J, R)` is taken from the fields of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {C' : Type (u + 1)} [Category.{u} C'] [EssentiallySmall.{u + 1} C']
  {J' : GrothendieckTopology C'} {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high)
    (J : GrothendieckTopology C) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high)
    (J : GrothendieckTopology C) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high)
    (J : GrothendieckTopology C) :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high)
    (J : GrothendieckTopology C) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high)
    (J : GrothendieckTopology C) (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

noncomputable local instance (priority := high)
    (J' : GrothendieckTopology C') :
    MonoidalCategory (DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J' R).monoidalCategory

noncomputable local instance (priority := high)
    (J' : GrothendieckTopology C') :
    MonoidalPreadditive (DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J' R).monoidalPreadditive

noncomputable local instance (priority := high)
    (J' : GrothendieckTopology C') :
    MonoidalLinear R (DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J' R).monoidalLinear

noncomputable local instance (priority := high)
    (J' : GrothendieckTopology C') :
    (curriedTensor (DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J' R).commShift₂

noncomputable local instance (priority := high)
    (J' : GrothendieckTopology C') (K : DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J' R).isTriangulated_tensorLeft K

variable (J) in
/-- Every element of `Iⁿ` acts by zero on `R/Iⁿ`, placed in degree `0` of `D(J, R)`. -/
lemma smul_id_quotPowFunctor_obj_of_mem {I : Ideal R} {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    r • 𝟙 ((quotPowFunctor J I).obj (op n)) = 0 := by
  change r • 𝟙 ((singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).obj
    ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R (R ⧸ I ^ n)))) = 0
  have h : r • 𝟙 (ModuleCat.of R (R ⧸ I ^ n)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right _ _ hr
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_id, ← Functor.map_smul,
    ← Functor.map_smul, h, Functor.map_zero, Functor.map_zero]

variable (J) in
/-- Every element of `Iⁿ` acts by zero on the reduction `K ⊗ᴸ R/Iⁿ`. -/
lemma smul_id_derivedCompletionDiagram_obj_of_mem {I : Ideal R} {n : ℕ} {r : R}
    (hr : r ∈ I ^ n) (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    r • 𝟙 ((derivedCompletionDiagram J I K).obj (op n)) = 0 := by
  change r • 𝟙 (K ⊗ (quotPowFunctor J I).obj (op n)) = 0
  rw [← MonoidalCategory.whiskerLeft_id, ← MonoidalLinear.whiskerLeft_smul,
    smul_id_quotPowFunctor_obj_of_mem J hr, MonoidalPreadditive.whiskerLeft_zero]

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

/-- The first map of the triangle `Y ⊗ᴸ R ⟶ Y ⊗ᴸ R ⟶ Y ⊗ᴸ R/Iⁿ ⟶ (Y ⊗ᴸ R)⟦1⟧` is the
multiplication by `ϖⁿ`. -/
lemma tensorQuotPowTriangle_mor₁ (Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    (tensorQuotPowTriangle hϖ hI Y n).mor₁ =
      ϖ ^ n • 𝟙 (tensorQuotPowTriangle hϖ hI Y n).obj₁ := by
  change Y ◁ (quotPowTriangle J hϖ hI n).mor₁ = _
  rw [quotPowTriangle_mor₁, MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id]
  rfl

include hϖ hI in
/-- **Triangulated linear functors commute with the reductions.** For a nonzerodivisor `ϖ`
generating `I`, a triangulated `R`-linear functor `Φ : D(J, R) ⥤ D(J', R)` and `K ∈ D(J, R)`,
there is an isomorphism `Φ(K ⊗ᴸ R/Iⁿ) ≅ Φ(K) ⊗ᴸ R/Iⁿ`: both are cones of the multiplication by
`ϖⁿ` on `Φ(K)`. -/
theorem nonempty_iso_map_derivedCompletionDiagram_obj
    (Φ : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R)))
    [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Linear R]
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    Nonempty (Φ.obj ((derivedCompletionDiagram J I K).obj (op n)) ≅
      (derivedCompletionDiagram J' I (Φ.obj K)).obj (op n)) := by
  let T₁ := Φ.mapTriangle.obj (tensorQuotPowTriangle hϖ hI K n)
  let T₂ := tensorQuotPowTriangle (J := J') hϖ hI (Φ.obj K) n
  have h₁ : T₁ ∈ distTriang _ := Φ.map_distinguished _ (tensorQuotPowTriangle_distinguished hϖ hI K n)
  have h₂ : T₂ ∈ distTriang _ := tensorQuotPowTriangle_distinguished hϖ hI _ n
  have hT₁ : T₁.mor₁ = ϖ ^ n • 𝟙 T₁.obj₁ := by
    change Φ.map (tensorQuotPowTriangle hϖ hI K n).mor₁ = _
    rw [tensorQuotPowTriangle_mor₁, Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  let v : T₁.obj₁ ≅ T₂.obj₁ := Φ.mapIso (unitIso K).symm ≪≫ unitIso (Φ.obj K)
  obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ h₁ h₂
    (Arrow.isoMk v v (by
      change v.hom ≫ T₂.mor₁ = T₁.mor₁ ≫ v.hom
      rw [hT₁, tensorQuotPowTriangle_mor₁, Linear.comp_smul, Linear.smul_comp, comp_id, id_comp]
      rfl))
  exact ⟨Triangle.π₃.mapIso e⟩

include hϖ hI in
/-- A right adjoint `G` of an `R`-linear functor `F` between derived categories of sheaves of
`R`-modules preserves derived completeness for `I = (ϖ)`: a map `L ⟶ G K` from an object on
which `ϖ` acts invertibly corresponds to a map `F L ⟶ K`, and `ϖ` acts invertibly on `F L`. -/
lemma derivedComplete_obj_of_adjunction
    {F : DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    {G : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R))}
    (adj : F ⊣ G) [F.Additive] [F.Linear R] {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hK : derivedComplete J I K) : derivedComplete J' I (G.obj K) := by
  rw [derivedComplete_iff_rightOrthogonal hϖ hI] at hK ⊢
  intro L f (hL : IsIso (ϖ • 𝟙 L))
  have : IsIso (ϖ • 𝟙 (F.obj L)) := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  have h₀ : (adj.homEquiv L K).symm f = 0 := hK _ this
  have : G.Additive := adj.right_adjoint_additive
  rw [← (adj.homEquiv L K).apply_symm_apply f, h₀, adj.homEquiv_apply, Functor.map_zero,
    Limits.comp_zero]

end DerivedCategory
