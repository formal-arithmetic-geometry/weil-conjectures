/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Derived completeness for a principal ideal

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor.
This file shows that an object `K` of `D(J, R) = DerivedCategory (Sheaf J (ModuleCat R))` is
derived complete for the ideal `(ϖ)` (`DerivedCategory.derivedComplete`, defined by the Milnor
triangle `K ≅ R lim_n (K ⊗ᴸ R/ϖⁿ)`) if and only if every map to `K` from an object on which `ϖ`
acts invertibly vanishes. This is the characterisation `RHom(R[1/ϖ], K) = 0` of Stacks,
Tags 091Q and 0999, phrased with the class `DerivedCategory.smulInvertible J ϖ` of objects on
which `ϖ` acts invertibly (the objects `X ⊗ᴸ R[1/ϖ]`). As a consequence, the derived complete
objects form a triangulated subcategory.

## Main definitions

- `DerivedCategory.smulInvertible J ϖ`: the objects `X` of `D(J, R)` such that `ϖ • 𝟙 X` is an
  isomorphism.

## Main results

- `DerivedCategory.derivedComplete_iff_rightOrthogonal`: for `I = (ϖ)` with `ϖ` a
  nonzerodivisor, `K` is derived complete iff it is right orthogonal to
  `DerivedCategory.smulInvertible J ϖ`.
- `DerivedCategory.isTriangulated_derivedComplete`: the derived complete objects form a
  triangulated subcategory.

## Proof

If `K` is derived complete, the terms `K ⊗ᴸ R/ϖⁿ` of the tower are killed by `ϖⁿ`, so they
receive no nonzero maps from objects on which `ϖ` acts invertibly, and neither does their
homotopy limit `K`.

Conversely, let `K` be right orthogonal to `smulInvertible J ϖ`, let `F` be a homotopy limit of
the tower `K ⊗ᴸ R/ϖⁿ`, and let `φ : K ⟶ F` be a map extending the reductions, obtained by
comparing `F` with the Milnor triangle of the constant tower `K`. Its cone `X` is right
orthogonal to `smulInvertible J ϖ`. Tensoring with `M = R/ϖ` turns the reduction tower into a
tower which is pro-isomorphic to the constant tower `K ⊗ᴸ M`, because `ϖ` acts by zero on
`K ⊗ᴸ M`; since `- ⊗ᴸ M` is triangulated and commutes with products, `φ ⊗ᴸ M` is then an
isomorphism (`CategoryTheory.Pretriangulated.isIso_of_proIso`), so `X ⊗ᴸ M = 0`, that is `ϖ`
acts invertibly on `X`. Hence `X = 0` and `φ` is an isomorphism, which says that `K` is the
homotopy limit of its reductions.

## Implementation notes

The monoidal structure of `D(J, R)` and the instances attached to it are taken from the fields
of `DerivedCategory.sheafTensorStructure J R`, declared below as local instances of high
priority, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`. The statements of the main
results do not involve the monoidal structure.

-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

local instance : IsIso (sheafTensorStructure J R).ε := (sheafTensorStructure J R).isIso_ε

/-- The objects of `D(J, R)` on which `ϖ` acts invertibly. -/
def smulInvertible (ϖ : R) : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  fun X ↦ IsIso (ϖ • 𝟙 X)

variable {J}

instance (ϖ : R) (a : ℤ) : (smulInvertible J ϖ).IsStableUnderShiftBy a where
  le_shift X (hX : IsIso (ϖ • 𝟙 X)) := by
    change IsIso (ϖ • 𝟙 (X⟦a⟧))
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance

instance (ϖ : R) : (smulInvertible J ϖ).IsStableUnderShift ℤ where

lemma smulInvertible.pow {ϖ : R} {X : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hX : smulInvertible J ϖ X) (n : ℕ) : IsIso (ϖ ^ n • 𝟙 X) := by
  induction n with
  | zero => simp only [pow_zero, one_smul]; infer_instance
  | succ n ih =>
    have h₁ : IsIso (ϖ • 𝟙 X) := hX
    have e : ϖ ^ (n + 1) • 𝟙 X = (ϖ ^ n • 𝟙 X) ≫ (ϖ • 𝟙 X) := by
      rw [Linear.smul_comp, id_comp, smul_smul, pow_succ]
    rw [e]
    exact IsIso.comp_isIso' ih h₁

/-- There is no nonzero map from an object on which `ϖ` acts invertibly to an object killed by
`ϖⁿ`. -/
lemma smulInvertible.hom_eq_zero {ϖ : R} {X Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hX : smulInvertible J ϖ X) {n : ℕ} (hY : ϖ ^ n • 𝟙 Y = 0) (f : X ⟶ Y) : f = 0 := by
  have := hX.pow n
  rw [← cancel_epi (ϖ ^ n • 𝟙 X), comp_zero, Linear.smul_comp, id_comp, ← comp_id f,
    ← Linear.comp_smul, hY, comp_zero]

variable (J) in
/-- `ϖⁿ` acts by zero on `R/Iⁿ`, placed in degree `0` of `D(J, R)`, when `ϖ ∈ I`. -/
lemma smul_id_quotPowFunctor_obj {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ I) (n : ℕ) :
    ϖ ^ n • 𝟙 ((quotPowFunctor J I).obj (op n)) = 0 := by
  change ϖ ^ n • 𝟙 ((singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).obj
    ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R (R ⧸ I ^ n)))) = 0
  have h : ϖ ^ n • 𝟙 (ModuleCat.of R (R ⧸ I ^ n)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖ n)
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_id, ← Functor.map_smul,
    ← Functor.map_smul, h, Functor.map_zero, Functor.map_zero]

variable (J) in
/-- `ϖⁿ` acts by zero on the reduction `K ⊗ᴸ R/Iⁿ` when `ϖ ∈ I`. -/
lemma smul_id_derivedCompletionDiagram_obj {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ I)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    ϖ ^ n • 𝟙 ((derivedCompletionDiagram J I K).obj (op n)) = 0 := by
  change ϖ ^ n • 𝟙 (K ⊗ (quotPowFunctor J I).obj (op n)) = 0
  rw [← MonoidalCategory.whiskerLeft_id, ← MonoidalLinear.whiskerLeft_smul,
    smul_id_quotPowFunctor_obj J hϖ n, MonoidalPreadditive.whiskerLeft_zero]

/-- A derived complete object receives no nonzero map from an object on which `ϖ` acts
invertibly, when `ϖ ∈ I`. -/
lemma rightOrthogonal_of_derivedComplete {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ I)
    {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (hK : derivedComplete J I K) :
    (smulInvertible J ϖ).rightOrthogonal K := fun X f hX ↦
  IsHomotopyLimit.hom_ext_zero hK
    (fun n g ↦ hX.hom_eq_zero (smul_id_derivedCompletionDiagram_obj J hϖ K n) g)
    (fun n g ↦ (ObjectProperty.le_shift _ 1 X hX).hom_eq_zero
      (smul_id_derivedCompletionDiagram_obj J hϖ K n) g) f

section ShortExact

variable {I : Ideal R} {ϖ : R}

variable (I ϖ) in
/-- The short complex `R ⟶ R ⟶ R/Iⁿ` of `R`-modules, the first map being the multiplication
by `ϖⁿ`, when `ϖ ∈ I`. -/
noncomputable def quotPowShortComplex (hϖ : ϖ ∈ I) (n : ℕ) :
    ShortComplex (ModuleCat.{u + 1} R) :=
  ShortComplex.mk (ϖ ^ n • 𝟙 (𝟙_ (ModuleCat.{u + 1} R))) ((Ideal.quotPowCone I).π.app (op n))
    (by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      change Submodule.Quotient.mk (ϖ ^ n • x) = 0
      rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖ n))

lemma mem_of_eq_span (hI : I = Ideal.span {ϖ}) : ϖ ∈ I := hI ▸ Ideal.mem_span_singleton_self ϖ

lemma quotPowShortComplex_shortExact (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})
    (n : ℕ) : (quotPowShortComplex I ϖ (mem_of_eq_span hI) n).ShortExact := by
  subst hI
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro (y : R)
    change Submodule.Quotient.mk (p := Ideal.span {ϖ} ^ n) y = 0 ↔ ∃ x : R, ϖ ^ n • x = y
    rw [Submodule.Quotient.mk_eq_zero, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    simp [mul_comm, smul_eq_mul]
  · intro (x : R) (y : R) h
    change ϖ ^ n • x = ϖ ^ n • y at h
    rw [smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub] at h
    rw [← sub_eq_zero]
    exact (mem_nonZeroDivisors_iff.1 (pow_mem hϖ n)).1 _ h
  · exact Submodule.Quotient.mk_surjective _

variable (I ϖ) in
/-- The transition between the short complexes `quotPowShortComplex`: multiplication by `ϖ` on
the first term, the identity on the second, the projection `R/Iⁿ⁺¹ ⟶ R/Iⁿ` on the third. -/
noncomputable def quotPowShortComplexMap (hϖ : ϖ ∈ I) (n : ℕ) :
    quotPowShortComplex I ϖ hϖ (n + 1) ⟶ quotPowShortComplex I ϖ hϖ n where
  τ₁ := ϖ • 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := (Ideal.quotPowFunctor I).map (homOfLE n.le_succ).op
  comm₁₂ := by
    change (ϖ • 𝟙 (𝟙_ (ModuleCat.{u + 1} R))) ≫ (ϖ ^ n • 𝟙 _) =
      (ϖ ^ (n + 1) • 𝟙 (𝟙_ (ModuleCat.{u + 1} R))) ≫ 𝟙 _
    rw [comp_id, Linear.smul_comp, id_comp, smul_smul, ← pow_succ']
  comm₂₃ := by
    rw [id_comp]
    exact (Ideal.quotPowCone I).w (homOfLE n.le_succ).op

end ShortExact

section Triangles

variable (J) {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

include hϖ in
/-- The short exact sequence of constant sheaves `R ⟶ R ⟶ R/Iⁿ`. -/
lemma sheafQuotPowShortComplex_shortExact (n : ℕ) :
    ((quotPowShortComplex I ϖ (mem_of_eq_span hI) n).map
      (constantSheaf J (ModuleCat.{u + 1} R))).ShortExact :=
  (quotPowShortComplex_shortExact hϖ hI n).map_of_exact _

/-- The distinguished triangle `R ⟶ R ⟶ R/Iⁿ ⟶ R⟦1⟧` in `D(J, R)`. -/
noncomputable abbrev quotPowTriangle (n : ℕ) :
    Triangle (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafQuotPowShortComplex_shortExact J hϖ hI n).singleTriangle

lemma quotPowTriangle_distinguished (n : ℕ) : quotPowTriangle J hϖ hI n ∈ distTriang _ :=
  (sheafQuotPowShortComplex_shortExact J hϖ hI n).singleTriangle_distinguished

lemma quotPowTriangle_mor₁ (n : ℕ) :
    (quotPowTriangle J hϖ hI n).mor₁ = ϖ ^ n • 𝟙 (quotPowTriangle J hϖ hI n).obj₁ := by
  change (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
    ((constantSheaf J (ModuleCat.{u + 1} R)).map (ϖ ^ n • 𝟙 (𝟙_ (ModuleCat.{u + 1} R)))) = _
  rw [Functor.map_smul, Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The transition morphisms of triangles `quotPowTriangle (n + 1) ⟶ quotPowTriangle n`. -/
noncomputable def quotPowTriangleMap (n : ℕ) :
    quotPowTriangle J hϖ hI (n + 1) ⟶ quotPowTriangle J hϖ hI n :=
  ShortComplex.ShortExact.singleTriangle.map _ _
    ((constantSheaf J (ModuleCat.{u + 1} R)).mapShortComplex.map
      (quotPowShortComplexMap I ϖ (mem_of_eq_span hI) n))

lemma quotPowTriangleMap_hom₁ (n : ℕ) :
    (quotPowTriangleMap J hϖ hI n).hom₁ = ϖ • 𝟙 (quotPowTriangle J hϖ hI (n + 1)).obj₁ := by
  change (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
    ((constantSheaf J (ModuleCat.{u + 1} R)).map (ϖ • 𝟙 (𝟙_ (ModuleCat.{u + 1} R)))) = _
  rw [Functor.map_smul, Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

lemma quotPowTriangleMap_hom₂ (n : ℕ) :
    (quotPowTriangleMap J hϖ hI n).hom₂ = 𝟙 (quotPowTriangle J hϖ hI (n + 1)).obj₂ := by
  change (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
    ((constantSheaf J (ModuleCat.{u + 1} R)).map (𝟙 (𝟙_ (ModuleCat.{u + 1} R)))) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

end Triangles

section Products

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

/-- The isomorphism `Y ≅ Y ⊗ᴸ R`, where `R` is placed in degree `0`. -/
noncomputable def unitIso (Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Y ≅ Y ⊗ (singleFunctor _ 0).obj (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))) :=
  (ρ_ Y).symm ≪≫ whiskerLeftIso Y (asIso (sheafTensorStructure J R).ε)

@[reassoc]
lemma unitIso_hom_naturality {Y Y' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (f : Y ⟶ Y') : f ≫ (unitIso Y').hom = (unitIso Y).hom ≫
      f ▷ (singleFunctor _ 0).obj (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))) := by
  simp [unitIso, whisker_exchange]

/-- Tensoring with the unit `R` placed in degree `0` commutes with products. -/
noncomputable def isLimit_fan_whiskerRight_unit
    {Y : ℕ → DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    {P : Fan Y} (hP : IsLimit P) :
    IsLimit (Fan.mk (P.pt ⊗ (singleFunctor _ 0).obj (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))))
      fun j ↦ P.proj j ▷ _) :=
  Fan.IsLimit.mk _ (fun s ↦ Fan.IsLimit.lift hP (fun j ↦ s.proj j ≫ (unitIso (Y j)).inv) ≫
      (unitIso P.pt).hom)
    (fun s j ↦ by
      change (_ ≫ _) ≫ P.proj j ▷ _ = _
      simp only [assoc, ← unitIso_hom_naturality, Fan.IsLimit.fac_assoc, Iso.inv_hom_id,
        comp_id])
    (fun s m hm ↦ by
      rw [← Iso.comp_inv_eq]
      refine Fan.IsLimit.hom_ext hP _ _ fun j ↦ ?_
      rw [Fan.IsLimit.fac, ← cancel_mono (unitIso (Y j)).hom]
      simp only [assoc, unitIso_hom_naturality, Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]
      exact hm j)

/-- The triangle `Y ⊗ᴸ R ⟶ Y ⊗ᴸ R ⟶ Y ⊗ᴸ R/Iⁿ ⟶ (Y ⊗ᴸ R)⟦1⟧`. -/
noncomputable abbrev tensorQuotPowTriangle
    (Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    Triangle (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  ((curriedTensor _).obj Y).mapTriangle.obj (quotPowTriangle J hϖ hI n)

lemma tensorQuotPowTriangle_distinguished (Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    (n : ℕ) : tensorQuotPowTriangle hϖ hI Y n ∈ distTriang _ :=
  ((curriedTensor _).obj Y).map_distinguished _ (quotPowTriangle_distinguished J hϖ hI n)

/-- The morphism of triangles `tensorQuotPowTriangle Y n ⟶ tensorQuotPowTriangle Y' n` induced
by a map `Y ⟶ Y'`. -/
noncomputable def tensorQuotPowTriangleMap
    {Y Y' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (f : Y ⟶ Y') (n : ℕ) :
    tensorQuotPowTriangle hϖ hI Y n ⟶ tensorQuotPowTriangle hϖ hI Y' n where
  hom₁ := f ▷ (quotPowTriangle J hϖ hI n).obj₁
  hom₂ := f ▷ (quotPowTriangle J hϖ hI n).obj₂
  hom₃ := f ▷ (quotPowTriangle J hϖ hI n).obj₃
  comm₁ := whisker_exchange _ _
  comm₂ := whisker_exchange _ _
  comm₃ := by
    have h := NatTrans.shift_app_comm ((curriedTensor (DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} R)))).map f) (1 : ℤ) (quotPowTriangle J hϖ hI n).obj₁
    dsimp at h
    change (Y ◁ (quotPowTriangle J hϖ hI n).mor₃ ≫ (Functor.commShiftIso ((curriedTensor
      (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj Y) (1 : ℤ)).hom.app
        (quotPowTriangle J hϖ hI n).obj₁) ≫ (f ▷ (quotPowTriangle J hϖ hI n).obj₁)⟦(1 : ℤ)⟧' =
      f ▷ (quotPowTriangle J hϖ hI n).obj₃ ≫ Y' ◁ (quotPowTriangle J hϖ hI n).mor₃ ≫
        (Functor.commShiftIso ((curriedTensor (DerivedCategory
          (Sheaf J (ModuleCat.{u + 1} R)))).obj Y') (1 : ℤ)).hom.app
            (quotPowTriangle J hϖ hI n).obj₁
    rw [assoc, h, whisker_exchange_assoc]

/-- The transition morphism `Y ⊗ᴸ quotPowTriangle (n + 1) ⟶ Y ⊗ᴸ quotPowTriangle n`. -/
noncomputable def tensorQuotPowTriangleTransition
    (Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    tensorQuotPowTriangle hϖ hI Y (n + 1) ⟶ tensorQuotPowTriangle hϖ hI Y n :=
  ((curriedTensor _).obj Y).mapTriangle.map (quotPowTriangleMap J hϖ hI n)

/-- Tensoring with `R/Iⁿ` commutes with countable products. -/
noncomputable def isLimit_fan_whiskerRight_quotPow (n : ℕ)
    {Y : ℕ → DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} {P : Fan Y} (hP : IsLimit P) :
    IsLimit (Fan.mk (P.pt ⊗ (quotPowFunctor J I).obj (op n)) fun j ↦ P.proj j ▷ _) := by
  let T := fun j ↦ tensorQuotPowTriangle hϖ hI (Y j) n
  let ψ : tensorQuotPowTriangle hϖ hI P.pt n ⟶ productTriangle T :=
    productTriangle.lift T fun j ↦ tensorQuotPowTriangleMap hϖ hI (P.proj j) n
  have hU := isLimit_fan_whiskerRight_unit (J := J) hP
  have h₁ : IsIso ψ.hom₁ := by
    have : ψ.hom₁ = (hU.conePointUniqueUpToIso (productIsProduct _)).hom := by
      refine Pi.hom_ext _ _ fun j ↦ ?_
      erw [IsLimit.conePointUniqueUpToIso_hom_comp hU (productIsProduct _) ⟨j⟩]
      simp [ψ, tensorQuotPowTriangleMap]
      rfl
    rw [this]
    infer_instance
  have h₂ : IsIso ψ.hom₂ := by
    have : ψ.hom₂ = (hU.conePointUniqueUpToIso (productIsProduct _)).hom := by
      refine Pi.hom_ext _ _ fun j ↦ ?_
      erw [IsLimit.conePointUniqueUpToIso_hom_comp hU (productIsProduct _) ⟨j⟩]
      simp [ψ, tensorQuotPowTriangleMap]
      rfl
    rw [this]
    infer_instance
  have h₃ : IsIso ψ.hom₃ := isIso₃_of_isIso₁₂ ψ (tensorQuotPowTriangle_distinguished hϖ hI _ n)
    (productTriangle_distinguished T fun j ↦ tensorQuotPowTriangle_distinguished hϖ hI _ n) h₁ h₂
  refine IsLimit.ofIsoLimit (productIsProduct _) (Fan.ext (asIso ψ.hom₃).symm fun j ↦ ?_)
  rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
  simp only [ψ, productTriangle.lift_hom₃, tensorQuotPowTriangleMap, Fan.mk_pt]
  exact Pi.lift_π _ _

/-- Tensoring with `R/I` commutes with countable products. -/
noncomputable def isLimit_fan_whiskerRight_quot
    {Y : ℕ → DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} {P : Fan Y} (hP : IsLimit P) :
    IsLimit (Fan.mk (P.pt ⊗ (quotPowFunctor J I).obj (op 1)) fun j ↦ P.proj j ▷ _) :=
  isLimit_fan_whiskerRight_quotPow hϖ hI 1 hP

end Products

section Main

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

lemma derivedCompletionCone_π_app (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    (n : ℕ) : (derivedCompletionCone J I K).π.app (op n) =
      (unitIso K).hom ≫ (tensorQuotPowTriangle hϖ hI K n).mor₂ := by
  change (ρ_ K).inv ≫ K ◁ ((sheafTensorStructure J R).ε ≫
      (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
        ((constantSheaf J (ModuleCat.{u + 1} R)).map ((Ideal.quotPowCone I).π.app (op n)))) =
    ((ρ_ K).inv ≫ K ◁ (sheafTensorStructure J R).ε) ≫
      K ◁ (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
        ((constantSheaf J (ModuleCat.{u + 1} R)).map ((Ideal.quotPowCone I).π.app (op n)))
  rw [MonoidalCategory.whiskerLeft_comp, assoc]

include hI in
lemma smul_id_tensor_quot (Z : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ϖ • 𝟙 (Z ⊗ (quotPowFunctor J I).obj (op 1)) = 0 := by
  have := smul_id_quotPowFunctor_obj J (mem_of_eq_span hI) 1
  rw [pow_one] at this
  rw [← MonoidalCategory.whiskerLeft_id, ← MonoidalLinear.whiskerLeft_smul, this,
    MonoidalPreadditive.whiskerLeft_zero]

include hI in
lemma tensor_whisker_smul_eq_zero (K Z : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    (n : ℕ) : (K ◁ ((ϖ ^ (n + 1)) • 𝟙 Z)) ▷ (quotPowFunctor J I).obj (op 1) = 0 := by
  rw [MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id,
    MonoidalLinear.smul_whiskerRight, MonoidalCategory.id_whiskerRight, pow_succ, mul_smul,
    smul_id_tensor_quot hI, smul_zero]

include hϖ hI in
/-- An object which is right orthogonal to the objects on which `ϖ` acts invertibly is derived
complete for `I = (ϖ)`. -/
theorem derivedComplete_of_rightOrthogonal {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hK : (smulInvertible J ϖ).rightOrthogonal K) : derivedComplete J I K := by
  have hϖI := mem_of_eq_span hI
  let G := derivedCompletionDiagram J I K
  let c := derivedCompletionCone J I K
  let P : Fan fun n : ℕ ↦ G.obj (op n) := Fan.mk _ (Pi.π _)
  have hP : IsLimit P := productIsProduct _
  obtain ⟨F, ι, ε, hT⟩ := distinguished_cocone_triangle₁ (𝟙 P.pt - towerShift hP)
  -- the Milnor triangle of the constant tower `K`
  let c₀ : Cone ((Functor.const ℕᵒᵖ).obj K) := { pt := K, π := 𝟙 _ }
  have : ∀ n, IsIso (c₀.π.app n) := fun n ↦ by dsimp [c₀]; infer_instance
  obtain ⟨PK, hPK, δK, hTK⟩ := IsHomotopyLimit.of_isIso_π c₀
  let m := productTowerMap (PF := PK) hP c.π
  obtain ⟨φ, hφ₁, hφ₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hTK hT m m
    (productTowerMap_comp_sub_towerShift hPK hP c.π).symm
  replace hφ₁ : Fan.IsLimit.lift hPK (fun n ↦ c₀.π.app (op n)) ≫ m = φ ≫ ι := hφ₁
  replace hφ₃ : δK ≫ φ⟦(1 : ℤ)⟧' = m ≫ ε := hφ₃
  have hlift : Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) =
      Fan.IsLimit.lift hPK (fun n ↦ c₀.π.app (op n)) ≫ m :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [m, c₀]
  -- `F` is right orthogonal to `smulInvertible J ϖ`
  have hF : (smulInvertible J ϖ).rightOrthogonal F := by
    intro L f hL
    have h₀ : f ≫ ι = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [zero_comp]
      exact hL.hom_eq_zero (smul_id_derivedCompletionDiagram_obj J hϖI K n) _
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ hT (f⟦(1 : ℤ)⟧')
      (by rw [Triangle.mk_mor₁, ← Functor.map_comp, h₀, Functor.map_zero])
    have : g = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [zero_comp]
      exact (ObjectProperty.le_shift _ 1 L hL).hom_eq_zero
        (smul_id_derivedCompletionDiagram_obj J hϖI K n) _
    rw [this, zero_comp] at hg
    exact (shiftFunctor _ (1 : ℤ)).map_eq_zero_iff.mp hg
  -- the cone `X` of `φ` is right orthogonal to `smulInvertible J ϖ`
  obtain ⟨X, g, h, hX⟩ := distinguished_cocone_triangle φ
  have hXorth : (smulInvertible J ϖ).rightOrthogonal X := by
    intro L f hL
    have hK1 : (smulInvertible J ϖ).rightOrthogonal (K⟦(1 : ℤ)⟧) :=
      ObjectProperty.le_shift _ 1 K hK
    obtain ⟨f', hf'⟩ := Triangle.coyoneda_exact₃ _ hX f (hK1 _ hL)
    rw [hf', hF f' hL, zero_comp]
  -- `ϖ` acts invertibly on `X`, through `X ⊗ᴸ R/ϖ = 0`
  let M := (quotPowFunctor J I).obj (op 1)
  let TM := (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj M
  let F' : ℕᵒᵖ ⥤ _ := (Functor.const ℕᵒᵖ).obj K ⋙ TM
  let G' : ℕᵒᵖ ⥤ _ := G ⋙ TM
  let PM : Fan fun n : ℕ ↦ G'.obj (op n) := Fan.mk (P.pt ⊗ M) fun j ↦ P.proj j ▷ M
  have hPM : IsLimit PM := isLimit_fan_whiskerRight_quot hϖ hI hP
  let PKM : Fan fun n : ℕ ↦ F'.obj (op n) := Fan.mk (PK.pt ⊗ M) fun j ↦ PK.proj j ▷ M
  have hPKM : IsLimit PKM := isLimit_fan_whiskerRight_quot hϖ hI hPK
  have htK : TM.map (towerShift hPK) = towerShift hPKM :=
    Fan.IsLimit.hom_ext hPKM _ _ fun n ↦ by
      change TM.map _ ≫ TM.map _ = _
      rw [towerShift_proj, ← TM.map_comp, towerShift_proj, TM.map_comp]
      rfl
  have ht : TM.map (towerShift hP) = towerShift hPM :=
    Fan.IsLimit.hom_ext hPM _ _ fun n ↦ by
      change TM.map _ ≫ TM.map _ = _
      rw [towerShift_proj, ← TM.map_comp, towerShift_proj, TM.map_comp]
      rfl
  have hTKM : Triangle.mk (TM.map (Fan.IsLimit.lift hPK fun n ↦ c₀.π.app (op n)))
      (𝟙 _ - towerShift hPKM) (TM.map δK ≫ (TM.commShiftIso (1 : ℤ)).hom.app K) ∈
        distTriang _ :=
    isomorphic_distinguished _ (TM.map_distinguished _ hTK) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl)
        (by
          simp only [Triangle.mk_mor₂, Iso.refl_hom, comp_id, id_comp]
          change _ = TM.map (𝟙 PK.pt - towerShift hPK)
          rw [Functor.map_sub, CategoryTheory.Functor.map_id, htK]
          rfl)
        (by simp; rfl))
  have hTFM : Triangle.mk (TM.map ι) (𝟙 _ - towerShift hPM)
      (TM.map ε ≫ (TM.commShiftIso (1 : ℤ)).hom.app F) ∈ distTriang _ :=
    isomorphic_distinguished _ (TM.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl)
        (by
          simp only [Triangle.mk_mor₂, Iso.refl_hom, comp_id, id_comp]
          change _ = TM.map (𝟙 P.pt - towerShift hP)
          rw [Functor.map_sub, CategoryTheory.Functor.map_id, ht]
          rfl)
        (by simp; rfl))
  let a : F' ⟶ G' := Functor.whiskerRight c.π TM
  have hb (n : ℕ) : ∃ b : G'.obj (op (n + 1)) ⟶ F'.obj (op n),
      b ≫ a.app (op n) = G'.map (homOfLE n.le_succ).op ∧
        a.app (op (n + 1)) ≫ b = F'.map (homOfLE n.le_succ).op := by
    have h₁ := tensor_whisker_smul_eq_zero hI K
      (quotPowTriangle J hϖ hI (n + 1)).obj₁ 0
    rw [zero_add, pow_one] at h₁
    obtain ⟨b, hb₁, hb₂⟩ := exists_lift_of_mor₁_eq_zero
      (TM.map_distinguished _ (tensorQuotPowTriangle_distinguished hϖ hI K (n + 1)))
      (TM.map_distinguished _ (tensorQuotPowTriangle_distinguished hϖ hI K n))
      (by
        change TM.map (K ◁ (quotPowTriangle J hϖ hI (n + 1)).mor₁) = 0
        rw [quotPowTriangle_mor₁]
        exact tensor_whisker_smul_eq_zero hI K _ n)
      (TM.mapTriangle.map (tensorQuotPowTriangleTransition hϖ hI K n))
      (by
        change TM.map (K ◁ (quotPowTriangleMap J hϖ hI n).hom₁) = 0
        rw [quotPowTriangleMap_hom₁]
        exact h₁)
    refine ⟨b ≫ TM.map (unitIso K).inv, ?_, ?_⟩
    · change _ ≫ TM.map (c.π.app (op n)) = _
      rw [derivedCompletionCone_π_app hϖ hI, TM.map_comp, assoc, ← TM.map_comp_assoc,
        Iso.inv_hom_id, CategoryTheory.Functor.map_id, id_comp]
      exact hb₂
    · change TM.map (c.π.app (op (n + 1))) ≫ _ = _
      rw [derivedCompletionCone_π_app hϖ hI, TM.map_comp, assoc]
      erw [reassoc_of% hb₁]
      change TM.map _ ≫ TM.map (K ◁ (quotPowTriangleMap J hϖ hI n).hom₂) ≫ _ = _
      rw [quotPowTriangleMap_hom₂, MonoidalCategory.whiskerLeft_id,
        CategoryTheory.Functor.map_id, id_comp, ← TM.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id]
      simp [F']
      rfl
  choose b hb₁ hb₂ using hb
  have hm : productTowerMap (PF := PKM) hPM a = TM.map m :=
    Fan.IsLimit.hom_ext hPM _ _ fun n ↦ by
      rw [productTowerMap_proj]
      change _ = TM.map _ ≫ TM.map _
      rw [← TM.map_comp, productTowerMap_proj, TM.map_comp]
      rfl
  have hφM : IsIso (TM.map φ) := isIso_of_proIso hPKM hPM hTKM hTFM a b hb₁ hb₂ (TM.map φ)
    (by rw [hm]; dsimp; rw [← TM.map_comp, ← TM.map_comp, hφ₁])
    (by
      rw [hm, assoc, ← TM.commShiftIso_hom_naturality, ← TM.map_comp_assoc, hφ₃,
        TM.map_comp_assoc])
  have hXM : IsZero (X ⊗ M) :=
    (Triangle.isZero₃_iff_isIso₁ _ (TM.map_distinguished _ hX)).2 hφM
  have hXinv : smulInvertible J ϖ X := by
    have h₁ := (Triangle.isZero₃_iff_isIso₁ _ (tensorQuotPowTriangle_distinguished hϖ hI X 1)).1 hXM
    change IsIso (X ◁ (quotPowTriangle J hϖ hI 1).mor₁) at h₁
    rw [quotPowTriangle_mor₁, pow_one, MonoidalLinear.whiskerLeft_smul,
      MonoidalCategory.whiskerLeft_id] at h₁
    change IsIso (ϖ • 𝟙 X)
    have : ϖ • 𝟙 X = (unitIso X).hom ≫ (ϖ • 𝟙 _) ≫ (unitIso X).inv := by
      rw [Linear.smul_comp, id_comp, Linear.comp_smul, Iso.hom_inv_id]
    have h₂ : IsIso (ϖ • 𝟙 (X ⊗ (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).obj
        (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))))) := h₁
    rw [this]
    infer_instance
  have hXzero : IsZero X := by
    rw [IsZero.iff_id_eq_zero]
    exact hXorth (𝟙 X) hXinv
  have : IsIso φ := (Triangle.isZero₃_iff_isIso₁ _ hX).1 hXzero
  refine ⟨_, hP, ε ≫ (inv φ)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (asIso φ) (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_)⟩
  · change Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) ≫ 𝟙 _ = φ ≫ ι
    rw [comp_id, hlift, hφ₁]
  · change (ε ≫ (inv φ)⟦(1 : ℤ)⟧') ≫ φ⟦(1 : ℤ)⟧' = 𝟙 _ ≫ ε
    rw [assoc, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, comp_id,
      id_comp]

include hϖ hI in
/-- For `I = (ϖ)` with `ϖ` a nonzerodivisor, an object of `D(J, R)` is derived complete if and
only if it receives no nonzero map from an object on which `ϖ` acts invertibly: this is the
characterisation `RHom(R[1/ϖ], K) = 0` of derived completeness (Stacks, Tags 091Q and 0999). -/
theorem derivedComplete_iff_rightOrthogonal
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    derivedComplete J I K ↔ (smulInvertible J ϖ).rightOrthogonal K :=
  ⟨rightOrthogonal_of_derivedComplete (mem_of_eq_span hI),
    derivedComplete_of_rightOrthogonal hϖ hI⟩

include hϖ hI in
lemma derivedComplete_eq_rightOrthogonal :
    derivedComplete J I = (smulInvertible J ϖ).rightOrthogonal :=
  funext fun K ↦ propext (derivedComplete_iff_rightOrthogonal hϖ hI K)

include hϖ hI in
/-- For `I = (ϖ)` with `ϖ` a nonzerodivisor, the derived complete objects of `D(J, R)` form a
triangulated subcategory. -/
lemma isTriangulated_derivedComplete : (derivedComplete J I).IsTriangulated := by
  rw [derivedComplete_eq_rightOrthogonal hϖ hI]
  infer_instance

end Main

end DerivedCategory
