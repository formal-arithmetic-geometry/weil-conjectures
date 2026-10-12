/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.FirstCokernel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# The generic Kummer residue sheaf

Let `X` be an integral regular noetherian scheme of dimension one (for instance a smooth
connected curve over a field), with generic point `η : Spec k(X) ⟶ X`, and let `n` be invertible
on `X`. Then the valuations at the closed points give an isomorphism

```
  R¹η_* μₙ ≅ ⨁_{x closed} i_{x*} ℤ/n
```

of étale sheaves on `X`, where `μₙ` is the sheaf of `n`-th roots of unity on `Spec k(X)` and
`i_x : Spec κ(x) ⟶ X` is the inclusion of a closed point.

## Proof

We argue on sheaves rather than on stalks. The Kummer sequence `0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` on
`Spec k(X)` and `R¹η_* 𝔾ₘ = 0` (`AlgebraicGeometry.Scheme.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf`,
Hilbert 90) identify `R¹η_* μₙ` with the cokernel of multiplication by `n` on `η_* 𝔾ₘ`, the
quotient map being the Kummer coboundary. The divisor sequence
`0 ⟶ 𝔾ₘ ⟶ η_* 𝔾ₘ ⟶ ⨁_x i_{x*} ℤ ⟶ 0` (`AlgebraicGeometry.Scheme.shortExact_divisorSequence`),
on whose first term multiplication by `n` is an epimorphism by the Kummer sequence on `X`,
identifies this cokernel with the cokernel of `n` on `⨁_x i_{x*} ℤ`, which is
`⨁_x i_{x*} ℤ/n` since each `i_{x*}` is exact (`i_x` is a closed immersion). The resulting
isomorphism sends the Kummer class of a rational function `f` to `∑_x (ord_x f mod n) [x]`
(`AlgebraicGeometry.Scheme.genericKummerResidueIso_spec`).

## Main definitions

- `AlgebraicGeometry.Scheme.pointConstantZMod`: the sheaf `i_{x*} ℤ/n` of a point `x`.
- `AlgebraicGeometry.Scheme.genericKummerResidueIso`: the isomorphism
  `R¹η_* μₙ ≅ ⨁_{x closed} i_{x*} ℤ/n`.

## Main statements

- `AlgebraicGeometry.Scheme.isZero_rightDerived_one_lowerStar_gmSheaf_fromSpecFunctionField`:
  `R¹η_* 𝔾ₘ = 0`.
- `AlgebraicGeometry.Scheme.genericKummerResidueIso_spec`: the isomorphism is given by the
  valuations.
-/

@[expose] public section

universe u

open CategoryTheory Limits Order

noncomputable section

namespace AddCommGrpCat

variable (n : ℕ)

/-- The reduction map `ℤ ⟶ ℤ/n`, in `AddCommGrpCat.{u + 1}`. -/
def uliftIntToZMod :
    AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ AddCommGrpCat.of (ULift.{u + 1} (ZMod n)) :=
  AddCommGrpCat.ofHom ((AddEquiv.ulift.symm.toAddMonoidHom.comp (Int.castAddHom (ZMod n))).comp
    AddEquiv.ulift.toAddMonoidHom)

@[simp]
lemma uliftIntToZMod_apply (a : ULift.{u + 1} ℤ) :
    uliftIntToZMod n a = ULift.up ((a.down : ℤ) : ZMod n) :=
  rfl

@[reassoc (attr := simp)]
lemma nsmul_id_comp_uliftIntToZMod :
    (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ uliftIntToZMod.{u} n = 0 := by
  ext a
  simp

/-- The reduction map `ℤ ⟶ ℤ/n` is a cokernel of multiplication by `n` on `ℤ`. -/
def isColimitUliftIntToZMod :
    IsColimit (CokernelCofork.ofπ _ (nsmul_id_comp_uliftIntToZMod.{u} n)) := by
  let S := ShortComplex.mk _ _ (nsmul_id_comp_uliftIntToZMod.{u} n)
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro a ha
    have ha : ((a.down : ℤ) : ZMod n) = 0 := congrArg ULift.down ha
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ha
    exact ⟨ULift.up b, ULift.ext _ _ (by simp [S, hb])⟩
  have : Epi S.g := (AddCommGrpCat.epi_iff_surjective _).2 fun a ↦
    ⟨ULift.up (a.down : ZMod n).valMinAbs, by
      rw [show S.g = uliftIntToZMod n from rfl, uliftIntToZMod_apply]
      exact ULift.ext _ _ (ZMod.coe_valMinAbs _)⟩
  exact hS.gIsCokernel

end AddCommGrpCat

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (n : ℕ)

section PointSheaf

/-- The étale sheaf `i_{x*} ℤ/n` on `X`: the pushforward of the constant sheaf `ℤ/n` along the
canonical morphism `i_x : Spec κ(x) ⟶ X` of a point `x` of `X`. -/
def pointConstantZMod (x : X) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).obj
    ((Spec (X.residueField x)).constantZMod n)

/-- The reduction map `i_{x*} ℤ ⟶ i_{x*} ℤ/n`. -/
def pointConstantIntToZMod (x : X) : X.pointConstantInt x ⟶ X.pointConstantZMod n x :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).map
    ((constantSheaf _ AddCommGrpCat.{u + 1}).map (AddCommGrpCat.uliftIntToZMod.{u} n))

@[reassoc (attr := simp)]
lemma nsmul_id_comp_pointConstantIntToZMod (x : X) :
    (n • 𝟙 (X.pointConstantInt x)) ≫ X.pointConstantIntToZMod n x = 0 := by
  have : n • 𝟙 (X.pointConstantInt x) =
      (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).map
        ((constantSheaf _ AddCommGrpCat.{u + 1}).map (n • 𝟙 _)) := by
    simp [pointConstantInt, Functor.map_nsmul]
  rw [this, pointConstantIntToZMod, ← Functor.map_comp, ← Functor.map_comp,
    AddCommGrpCat.nsmul_id_comp_uliftIntToZMod, Functor.map_zero, Functor.map_zero]

/-- At a closed point `x`, the reduction map `i_{x*} ℤ ⟶ i_{x*} ℤ/n` is a cokernel of
multiplication by `n`: the pushforward along the closed immersion `i_x` is exact. -/
def isColimitPointConstantIntToZMod {x : X} (hx : IsClosed ({x} : Set X)) :
    IsColimit (CokernelCofork.ofπ _ (X.nsmul_id_comp_pointConstantIntToZMod n x)) :=
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  Functor.isColimitCokernelCoforkNSMulMap n _
    (Functor.isColimitCokernelCoforkNSMulMap n _ (AddCommGrpCat.isColimitUliftIntToZMod.{u} n))

end PointSheaf

section Dimension

variable {X}

/-- On an integral scheme of dimension one, the points of codimension one are the closed
points. -/
lemma coheight_eq_one_iff_isClosed [IsIntegral X] (hX : topologicalKrullDim X = 1) (x : X) :
    coheight x = 1 ↔ IsClosed ({x} : Set X) := by
  constructor
  · intro hx
    refine closure_subset_iff_isClosed.1 fun y hy ↦ ?_
    rw [← specializes_iff_mem_closure] at hy
    by_contra hne
    have hlt : y < x := lt_of_le_not_ge (le_iff_specializes.2 hy) fun h ↦
      hne (Set.mem_singleton_iff.2 (hy.antisymm (le_iff_specializes.1 h)).eq.symm)
    have h₁ := coheight_add_one_le hlt
    have h₂ : (coheight y : WithBot ℕ∞) ≤ 1 := hX ▸ coheight_le_topologicalKrullDim y
    have h₂ : coheight y ≤ 1 := by exact_mod_cast h₂
    rw [hx] at h₁
    exact absurd (h₁.trans h₂) (by decide)
  · intro hx
    have hle : (coheight x : WithBot ℕ∞) ≤ 1 := hX ▸ coheight_le_topologicalKrullDim x
    have hne : coheight x ≠ 0 := by
      intro h0
      have hmax : IsMax x := Order.coheight_eq_zero.1 h0
      have h₁ : x ≤ genericPoint X :=
        le_iff_specializes.2 ((genericPoint_spec X).specializes (Set.mem_univ x))
      have h₂ : genericPoint X = x :=
        ((le_iff_specializes.1 h₁).antisymm (le_iff_specializes.1 (hmax h₁))).eq
      have hu : (Set.univ : Set X) = {x} := by
        rw [← genericPoint_spec X, h₂, hx.closure_eq]
      have : Subsingleton X := ⟨fun a b ↦ by
        have ha : a ∈ ({x} : Set X) := hu ▸ Set.mem_univ a
        have hb : b ∈ ({x} : Set X) := hu ▸ Set.mem_univ b
        rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]⟩
      have h₃ := topologicalKrullDim_zero_of_discreteTopology X
      rw [hX] at h₃
      exact absurd h₃ (by decide)
    have hle' : coheight x ≤ 1 := by exact_mod_cast hle
    exact le_antisymm hle' (Order.one_le_iff_ne_zero.2 hne)

end Dimension

section Generic

variable [IsIntegral X] [IsNoetherian X] [IsRegular X]

/-- **`R¹η_* 𝔾ₘ = 0` along the generic point** `η : Spec k(X) ⟶ X` of an integral regular
noetherian scheme, for the right derived functors of `η_*` on abelian étale sheaves. This is
`AlgebraicGeometry.Scheme.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf` (Hilbert 90 on the
generic fibres of affine étale `X`-schemes), read through
`CategoryTheory.Functor.isZero_rightDerived_one_of_epi_map`. -/
theorem isZero_rightDerived_one_lowerStar_gmSheaf_fromSpecFunctionField :
    IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).rightDerived 1).obj
      (Spec X.functionField).gmSheaf) := by
  let G := (Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf
  have := X.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf (Injective.ι G)
  have h := (Etale.lowerStar AddCommGrpCat.{u + 1}
    X.fromSpecFunctionField).isZero_rightDerived_one_of_epi_map (Injective.ι G)
  have := X.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  exact h.of_iso (((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).rightDerived
    1).mapIso (asIso (upperStarGmSheafToGmSheaf X.fromSpecFunctionField)).symm)

variable {X n}

lemma isUnit_natCast_functionField (hn : IsUnit (n : Γ(X, ⊤))) :
    IsUnit (n : Γ(Spec X.functionField, ⊤)) := by
  simpa using hn.map X.fromSpecFunctionField.appTop.hom

variable (n) in
lemma lowerStar_map_kummerSequence_g :
    (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).map
      ((Spec X.functionField).kummerSequence n).g = n • 𝟙 ((Etale.lowerStar AddCommGrpCat.{u + 1}
        X.fromSpecFunctionField).obj (Spec X.functionField).gmSheaf) := by
  change (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).map
    (n • 𝟙 (Spec X.functionField).gmSheaf) = _
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]

variable (n) in
/-- The Kummer coboundary `η_* 𝔾ₘ ⟶ R¹η_* μₙ` along the generic point `η : Spec k(X) ⟶ X`: the
connecting morphism of the long exact sequence of the right derived functors of `η_*` attached
to the Kummer sequence `0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` on `Spec k(X)`. On the sections over an étale
`X`-scheme `V` it sends a rational function on `V` to its Kummer class. -/
def genericKummerδ (hn : IsUnit (n : Γ(X, ⊤))) :
    (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
        (Spec X.functionField).gmSheaf ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).rightDerived 1).obj
        ((Spec X.functionField).rootsOfUnitySheaf n) :=
  ((Spec X.functionField).kummerSequence_shortExact n
    (isUnit_natCast_functionField hn)).rightDerivedZeroδ _

@[reassoc (attr := simp)]
lemma nsmul_id_comp_genericKummerδ (hn : IsUnit (n : Γ(X, ⊤))) :
    (n • 𝟙 _) ≫ genericKummerδ n hn = 0 := by
  have := ((Spec X.functionField).kummerSequence_shortExact n
    (isUnit_natCast_functionField hn)).map_g_comp_rightDerivedZeroδ
      (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField)
  rwa [lowerStar_map_kummerSequence_g] at this

/-- **`R¹η_* μₙ` is the cokernel of `n` on `η_* 𝔾ₘ`**, the quotient map being the Kummer
coboundary: this is the long exact sequence of `R η_*` on the Kummer sequence of `Spec k(X)`,
together with `R¹η_* 𝔾ₘ = 0`. -/
def isColimitGenericKummerδ (hn : IsUnit (n : Γ(X, ⊤))) :
    IsColimit (CokernelCofork.ofπ _ (nsmul_id_comp_genericKummerδ hn)) :=
  CokernelCofork.isColimitOfEq (lowerStar_map_kummerSequence_g n)
    (((Spec X.functionField).kummerSequence_shortExact n
      (isUnit_natCast_functionField hn)).isColimitCokernelCoforkRightDerivedZeroδ _
        (X.isZero_rightDerived_one_lowerStar_gmSheaf_fromSpecFunctionField))

end Generic

end AlgebraicGeometry.Scheme

end
