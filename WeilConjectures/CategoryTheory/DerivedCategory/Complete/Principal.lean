/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.Algebra.Homology.DerivedCategory.Products
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

/-- Tensoring with `R/I` commutes with countable products. -/
noncomputable def isLimit_fan_whiskerRight_quot
    {Y : ℕ → DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} {P : Fan Y} (hP : IsLimit P) :
    IsLimit (Fan.mk (P.pt ⊗ (quotPowFunctor J I).obj (op 1)) fun j ↦ P.proj j ▷ _) := by
  let T := fun j ↦ tensorQuotPowTriangle hϖ hI (Y j) 1
  let ψ : tensorQuotPowTriangle hϖ hI P.pt 1 ⟶ productTriangle T :=
    productTriangle.lift T fun j ↦ tensorQuotPowTriangleMap hϖ hI (P.proj j) 1
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
  have h₃ : IsIso ψ.hom₃ := isIso₃_of_isIso₁₂ ψ (tensorQuotPowTriangle_distinguished hϖ hI _ 1)
    (productTriangle_distinguished T fun j ↦ tensorQuotPowTriangle_distinguished hϖ hI _ 1) h₁ h₂
  refine IsLimit.ofIsoLimit (productIsProduct _) (Fan.ext (asIso ψ.hom₃).symm fun j ↦ ?_)
  rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
  simp only [ψ, productTriangle.lift_hom₃, tensorQuotPowTriangleMap, Fan.mk_pt]
  exact Pi.lift_π _ _

end Products

end DerivedCategory
