/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Flat
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift

/-!
# Classes with supports: products and restriction

Let `i : Z ⟶ U` be a closed immersion. A *class with supports in `Z`*, with source `K` and
coefficients `L`, is a morphism `K ⟶ Ri_! Ri^! L` in `D(U_ét)`. The supported term is `Ri_!`, as
in the supported localization triangle `AlgebraicGeometry.Etale.supportedLocalizationTriangle`;
for a closed immersion it is `Ri_*`. For `K = Λ_U` and `L = M[n]` these are the classes of
`H^n_Z(U, M)`.

This file provides the two operations on classes with supports used to glue local cohomology
classes:

* the *cup product with supports*
  `H^a_{Z₁}(U, M) × H^b_{Z₂}(U, N) ⟶ H^{a+b}_{Z₁ ∩ Z₂}(U, M ⊗ N)`;
* the *restriction of supports* along a morphism `e : U ⟶ X`, from classes supported on
  `Z ⊆ X` to classes supported on the preimage `Z' = Z ×_X U`.

Both are lifts through the counit `Ri_! Ri^! L ⟶ L` of a morphism whose source `K` is supported
on `Z`, in the sense that `Lj^* K = 0` for the open complement `j` of `Z`. Such a lift exists
and is unique (`AlgebraicGeometry.Etale.existsUnique_comp_counit_of_isZero`).

## Main definitions

- `AlgebraicGeometry.Etale.liftCounitOfRangeEqUniv`: supports on everything.
- `AlgebraicGeometry.Etale.supportedProduct`:
  `Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)` for `Z = Z₁ ∩ Z₂`.
- `AlgebraicGeometry.Etale.cupWithSupports`: the cup product of classes with supports.
- `AlgebraicGeometry.Etale.supportedRestriction`,
  `AlgebraicGeometry.Etale.restrictSupportedClass`: restriction of supports.

## Main statements

- `AlgebraicGeometry.Etale.existsUnique_comp_counit_of_isZero`: lifts through the counit of
  morphisms out of an object supported on `Z`.
- `AlgebraicGeometry.Etale.existsUnique_comp_counit_of_range_eq_univ`
- `AlgebraicGeometry.Etale.existsUnique_supportedProduct`
- `AlgebraicGeometry.Etale.existsUnique_supportedRestriction`

## Implementation details

The two lifts, and the lift of a morphism along a surjective closed immersion, are *defined* as
`Classical.choose` of the corresponding unique existence statements; uniqueness is what makes
the choices canonical.

The cup product is stated for classes whose degree shift is carried by the coefficients,
`K ⟶ Ri_! Ri^! (M[a])`; a class `K ⟶ (Ri_! Ri^! M)[a]` of degree `a` is brought into this form
through the shift compatibility of `Ri_!` and `Ri^!`
(`AlgebraicGeometry.Etale.shiftSupportedClass`). A construction of the supported cup product
through `h_* Λ_{Z₁ ∩ Z₂} ≅ i₁_* Λ_{Z₁} ⊗ᴸ i₂_* Λ_{Z₂}` is
`AlgebraicGeometry.Etale.cupSupportCohomology`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Lift

variable {V W U X Z Z₁ Z₂ U₁ U₂ : Scheme.{u}}

/-- `Lh^* Ri_! B = 0` when `h` factors through an open immersion `j` whose range is disjoint
from the range of `i`. -/
lemma isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (i : Z ⟶ X)
    [HasCompactification i] (j : V ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i) (Set.range j)) (h : W ⟶ X) (hh : Set.range h ⊆ Set.range j)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsZero ((L((h)^*[A])).obj ((R(i)_![A]).obj B)) := by
  have hj : IsZero ((L((j)^*[A])).obj ((R(i)_![A]).obj B)) := by
    have h₀ := subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar A i j hij B
      ((L((j)^*[A])).obj ((R(i)_![A]).obj B)) 0
    rw [IsZero.iff_id_eq_zero]
    apply ((derivedUpperStarLowerStarAdjunction A j).homEquiv _ _).injective
    rw [← cancel_epi ((shiftFunctorZero _ ℤ).hom.app _)]
    exact @Subsingleton.elim _ h₀ _ _
  rw [← IsOpenImmersion.lift_fac j h hh]
  exact ((L((IsOpenImmersion.lift j h hh)^*[A])).map_isZero hj).of_iso
    ((leftDerivedUpperStarComp A _ j).app _)

/-- There are no nonzero morphisms `K ⟶ Rj_* C` when `Lj^* K = 0`. -/
lemma subsingleton_hom_rightDerivedLowerStar_of_isZero (j : U ⟶ X)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsZero ((L((j)^*[A])).obj K))
    (C : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    Subsingleton (K ⟶ (R((j)_*[A])).obj C) :=
  have : Subsingleton ((L((j)^*[A])).obj K ⟶ C) := ⟨hK.eq_of_src⟩
  ((derivedUpperStarLowerStarAdjunction A j).homEquiv _ _).symm.subsingleton

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- Every object of the derived category of étale sheaves on an empty scheme is zero. -/
lemma isZero_derivedCategory_of_isEmpty (E : Scheme.{u}) [IsEmpty E]
    (K : DerivedCategory (Sheaf E.smallEtaleTopology A)) : IsZero K :=
  DerivedCategory.isZero_of_forall_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty ·) K

/-- **Lifts through the counit.** Let `i : Z ⟶ X` be a closed immersion with open complement
`j : U ⟶ X`, and let `K` be supported on `Z`, i.e. `Lj^* K = 0`. Every `φ : K ⟶ L` factors
uniquely through the counit `ε : Ri_! Ri^! L ⟶ L`. -/
theorem existsUnique_comp_counit_of_isZero (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i]
    [IsOpenImmersion j] (hij : Set.range i = (Set.range j)ᶜ)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) (φ : K ⟶ L) :
    ∃! ψ : K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L),
      ψ ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app L = φ := by
  have hT := supportedLocalizationTriangle_mem_distTriang Λ i j hij L
  set T := supportedLocalizationTriangle Λ i j L (supportedLocalizationBoundary Λ i j hij L)
  have : Subsingleton (K ⟶ T.obj₃) :=
    subsingleton_hom_rightDerivedLowerStar_of_isZero (ModuleCat.{u + 1} Λ) j hK
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L)
  have : Subsingleton (K⟦(1 : ℤ)⟧ ⟶ T.obj₃) :=
    subsingleton_hom_rightDerivedLowerStar_of_isZero (ModuleCat.{u + 1} Λ) j
      (((shiftFunctor _ (1 : ℤ)).map_isZero hK).of_iso
        (((L((j)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).app K)) _
  obtain ⟨ψ, hψ⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ hT φ (Subsingleton.elim _ _)
  exact ⟨ψ, hψ.symm, fun ψ' hψ' ↦
    Pretriangulated.Triangle.cancel_mor₁_of_subsingleton hT (hψ'.trans hψ)⟩

/-- **Objects supported on disjoint closed subsets.** Let `c` and `d` be closed immersions into
`X` with disjoint ranges, and `a`, `b` the open immersions of their complements. An object `T`
with `La^* T = 0` and `Lb^* T = 0` is zero. -/
lemma isZero_of_isZero_leftDerivedUpperStar_of_disjoint
    (c : Z₁ ⟶ X) (d : Z₂ ⟶ X) (a : U₁ ⟶ X) (b : U₂ ⟶ X)
    [IsClosedImmersion c] [IsClosedImmersion d] [IsOpenImmersion a] [IsOpenImmersion b]
    (hca : Set.range c = (Set.range a)ᶜ) (hdb : Set.range d = (Set.range b)ᶜ)
    (hcd : Disjoint (Set.range c) (Set.range d))
    {T : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ha : IsZero ((L((a)^*[ModuleCat.{u + 1} Λ])).obj T)) (hb : IsZero ((L((b)^*[ModuleCat.{u + 1}
        Λ])).obj T)) : IsZero T := by
  have : IsIso ((rightDerivedUpperShriekAdjunction Λ c).counit.app T) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      (supportedLocalizationTriangle_mem_distTriang Λ c a hca T)).1
        ((R((a)_*[ModuleCat.{u + 1} Λ])).map_isZero ha)
  have : IsIso ((rightDerivedUpperShriekAdjunction Λ d).counit.app T) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      (supportedLocalizationTriangle_mem_distTriang Λ d b hdb T)).1
        ((R((b)_*[ModuleCat.{u + 1} Λ])).map_isZero hb)
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar (ModuleCat.{u + 1} Λ) c
  have hsub : Subsingleton ((R(d)_![ModuleCat.{u + 1} Λ]).obj ((R(d)^![Λ]).obj T) ⟶
      (R((c)_*[ModuleCat.{u + 1} Λ])).obj ((R(c)^![Λ]).obj T)) :=
    subsingleton_hom_rightDerivedLowerStar_of_isZero (ModuleCat.{u + 1} Λ) c
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) d b
        (by rw [hdb]; exact disjoint_compl_left) c
        (by simpa [hdb] using hcd.subset_compl_right) _) _
  have : Subsingleton (T ⟶ T) :=
    @Equiv.subsingleton _ _
      ((asIso ((rightDerivedUpperShriekAdjunction Λ d).counit.app T)).symm.homCongr
        ((asIso ((rightDerivedUpperShriekAdjunction Λ c).counit.app T)).symm ≪≫ e.app _)) hsub
  rw [IsZero.iff_id_eq_zero]
  exact Subsingleton.elim _ _

/-- Let `i₁ : Z₁ ⟶ X` be a closed immersion, `j : U ⟶ X` an open immersion and `a` the open
complement of `Z₁ ×_X U` in `U`. Then `L(a ≫ j)^* Ri₁_! M = 0`, the range of `a ≫ j` being
disjoint from `Z₁`. -/
lemma isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
    (i₁ : Z₁ ⟶ X) [IsClosedImmersion i₁] (j : U ⟶ X)
    (M : DerivedCategory (Sheaf Z₁.smallEtaleTopology A)) :
    IsZero ((L(((pullback.snd i₁ j).openComplement.ι ≫ j)^*[A])).obj
      ((R(i₁)_![A]).obj M)) := by
  refine isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint A i₁
    i₁.openComplement.ι
    (by rw [i₁.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_left)
    _ ?_ _
  rw [← compl_compl (Set.range i₁.openComplement.ι), ← i₁.range_eq_compl_range_openComplement_ι,
    Set.subset_compl_iff_disjoint_left, Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
  apply x.2
  rw [Scheme.Pullback.range_snd]
  exact ⟨z, hx.symm⟩

end Lift

section CupProduct

variable {U Z₁ Z₂ Z : Scheme.{u}}

/-- **Supports on everything.** For a surjective closed immersion `i : Z ⟶ U`, every morphism
`φ : K ⟶ L` factors uniquely through the counit `ε : Ri_! Ri^! L ⟶ L`. -/
theorem existsUnique_comp_counit_of_range_eq_univ (i : Z ⟶ U) [IsClosedImmersion i]
    (hi : Set.range i.base = Set.univ)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : K ⟶ L) :
    ∃! ψ : K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L),
      ψ ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app L = φ := by
  have : IsEmpty i.openComplement.toScheme := ⟨fun x ↦ x.2 (hi ▸ Set.mem_univ _)⟩
  exact existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι (isZero_derivedCategory_of_isEmpty (ModuleCat.{u + 1} Λ)
        _ _) φ

/-- The lift `K ⟶ Ri_! Ri^! L` of a morphism `φ : K ⟶ L` along a surjective closed immersion
`i`, through the counit of `Ri_! ⊣ Ri^!`. -/
noncomputable def liftCounitOfRangeEqUniv (i : Z ⟶ U) [IsClosedImmersion i]
    (hi : Set.range i.base = Set.univ)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : K ⟶ L) :
    K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L) :=
  (existsUnique_comp_counit_of_range_eq_univ Λ i hi φ).exists.choose

/-- **The product of supports.** Let `i₁ : Z₁ ⟶ U`, `i₂ : Z₂ ⟶ U` and `i : Z ⟶ U` be closed
immersions with `Z = Z₁ ∩ Z₂`. The tensor product `ε₁ ⊗ ε₂ : Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶
M ⊗ N` of the two counits factors uniquely through the counit `ε : Ri_! Ri^! (M ⊗ N) ⟶ M ⊗ N`
of `Ri_! ⊣ Ri^!`. -/
theorem existsUnique_supportedProduct (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃! ψ : ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i₁)^![Λ]).obj M))).obj
        ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj ((R(i₂)^![Λ]).obj N)) ⟶
          (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
              U).obj M).obj N)),
      ψ ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app (((derivedTensor (ModuleCat.{u + 1} Λ)
          U).obj M).obj N) =
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).map ((rightDerivedUpperShriekAdjunction Λ
            i₁).counit.app M)).app _ ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).map
            ((rightDerivedUpperShriekAdjunction Λ i₂).counit.app N) := by
  refine existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι ?_ _
  set j := i.openComplement.ι
  have hcd : Disjoint (Set.range (pullback.snd i₁ j)) (Set.range (pullback.snd i₂ j)) := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Set.disjoint_left]
    intro x hx₁ hx₂
    apply x.2
    rw [h]
    exact ⟨hx₁, hx₂⟩
  refine isZero_of_isZero_leftDerivedUpperStar_of_disjoint Λ (pullback.snd i₁ j)
    (pullback.snd i₂ j) _ _ (Scheme.Hom.range_eq_compl_range_openComplement_ι _)
    (Scheme.Hom.range_eq_compl_range_openComplement_ι _) hcd ?_ ?_
  · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
    exact (isZero_derivedTensor_obj_obj_of_isZero_left
      (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
        (ModuleCat.{u + 1} Λ) i₁ j _)
        _).of_iso (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)
  · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
    exact (isZero_derivedTensor_obj_obj_of_isZero_right _
      (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
        (ModuleCat.{u + 1} Λ) i₂ j _)).of_iso
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)

/-- The *product of supports* `Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)` for closed
immersions with `Z = Z₁ ∩ Z₂`: the unique factorisation of the tensor product of the counits
through the counit of `Ri_! ⊣ Ri^!`. -/
noncomputable def supportedProduct (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i₁)^![Λ]).obj M))).obj
        ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj ((R(i₂)^![Λ]).obj N)) ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
          U).obj M).obj N)) :=
  (existsUnique_supportedProduct Λ i₁ i₂ i h M N).exists.choose

/-- The *cup product with supports* of classes `α : K ⟶ Ri₁_! Ri₁^! M` supported on `Z₁` and
`β : K ⟶ Ri₂_! Ri₂^! N` supported on `Z₂`, a class supported on `Z = Z₁ ∩ Z₂`:

`α ∪ β : K ⟶ K ⊗ K ⟶ Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)`,

where `Δ : K ⟶ K ⊗ K` is a diagonal and the last map is
`AlgebraicGeometry.Etale.supportedProduct`. For cohomology classes `K` is the unit and `Δ` the
inverse of the unitor; a class of degree `a` is a class with coefficients `M[a]`. -/
noncomputable def cupWithSupports (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {K M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (Δ : K ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj K).obj K)
    (α : K ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj M))
    (β : K ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj ((R(i₂)^![Λ]).obj N)) :
    K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
        U).obj M).obj N)) :=
  Δ ≫ ((derivedTensor (ModuleCat.{u + 1} Λ) U).map α).app K ≫ ((derivedTensor (ModuleCat.{u + 1} Λ)
      U).obj _).map β ≫
    supportedProduct Λ i₁ i₂ i h M N

/-- A class `K ⟶ (Ri_! Ri^! L)[n]` of degree `n` with supports, read as a class with
coefficients `L[n]`, `K ⟶ Ri_! Ri^! (L[n])`, through the shift compatibility of `Ri_!` and
`Ri^!`. -/
noncomputable def shiftSupportedClass (i : Z ⟶ U) [IsClosedImmersion i]
 (n : ℤ)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (α : K ⟶ ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))⟦n⟧) :
    K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj (L⟦n⟧)) :=
  α ≫ ((R(i)_![ModuleCat.{u + 1} Λ]).commShiftIso n).inv.app _ ≫
    (R(i)_![ModuleCat.{u + 1} Λ]).map (((R(i)^![Λ]).commShiftIso n).inv.app L)

end CupProduct

section Restriction

variable {U X Z Z' : Scheme.{u}}

/-- **Restriction of supports.** Let `e : U ⟶ X` be a morphism, `i : Z ⟶ X` a closed immersion
and `i' : Z' ⟶ U` its base change along `e`. For `L ∈ D(X_ét)`, `L' ∈ D(U_ét)` and
`τ : Le^* L ≅ L'`, the composite `Le^* ε ≫ τ : Le^* (Ri_! Ri^! L) ⟶ L'` factors uniquely through
the counit `ε' : Ri'_! Ri'^! L' ⟶ L'`. -/
theorem existsUnique_supportedRestriction (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i']
 (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (τ :
        (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    ∃! ψ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj
        L)) ⟶
        (R(i')_![ModuleCat.{u + 1} Λ]).obj ((R(i')^![Λ]).obj L'),
      ψ ≫ (rightDerivedUpperShriekAdjunction Λ i').counit.app L' =
        (L((e)^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedUpperShriekAdjunction Λ i).counit.app L) ≫
            τ.hom := by
  refine existsUnique_comp_counit_of_isZero Λ i' i'.openComplement.ι
    i'.range_eq_compl_range_openComplement_ι ?_ _
  refine (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ)
      i
    i.openComplement.ι (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_left)
    (i'.openComplement.ι ≫ e) ?_ _).of_iso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) i'.openComplement.ι e).app _).symm
  rw [← compl_compl (Set.range i.openComplement.ι), ← i.range_eq_compl_range_openComplement_ι,
    Set.subset_compl_iff_disjoint_left, Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
  apply x.2
  rw [Scheme.range_snd_of_isPullback hg]
  exact ⟨z, hx.symm⟩

/-- The *restriction of supports* `Le^* (Ri_! Ri^! L) ⟶ Ri'_! Ri'^! L'` along `e : U ⟶ X`, for
the base change `i'` of a closed immersion `i` and an identification `τ : Le^* L ≅ L'`: the unique
factorisation of `Le^* (Ri_! Ri^! L) ⟶ Le^* L ≅ L'` through the counit of `Ri'_! ⊣ Ri'^!`. -/
noncomputable def supportedRestriction (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i']
 (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (τ :
        (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    (L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) ⟶
      (R(i')_![ModuleCat.{u + 1} Λ]).obj ((R(i')^![Λ]).obj L') :=
  (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).exists.choose

/-- The restriction of a class `γ : K ⟶ Ri_! Ri^! L` with supports along `e : U ⟶ X`, for a
comparison `σ : K' ⟶ Le^* K` of sources:
`K' ⟶ Le^* K ⟶ Le^* (Ri_! Ri^! L) ⟶ Ri'_! Ri'^! L'`, the last map being
`AlgebraicGeometry.Etale.supportedRestriction`. For cohomology classes `σ` is the
identification `Λ_U ≅ Le^* Λ_X` of the constant complexes. -/
noncomputable def restrictSupportedClass (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i']
 (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (σ : K' ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K) (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅
        L')
    (γ : K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    K' ⟶ (R(i')_![ModuleCat.{u + 1} Λ]).obj ((R(i')^![Λ]).obj L') :=
  σ ≫ (L((e)^*[ModuleCat.{u + 1} Λ])).map γ ≫ supportedRestriction Λ e i i' g hg L L' τ

end Restriction

end Etale

end AlgebraicGeometry
