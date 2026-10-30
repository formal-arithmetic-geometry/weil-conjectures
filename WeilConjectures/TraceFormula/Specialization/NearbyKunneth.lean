/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethProper
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidal

/-!

# Gabber's Künneth formula for nearby cycles

Let `M` and `N` be models of finite type over the strictly henselian trait `S = Spec k'⟦t⟧`
(`k'` separably closed) and let `P` be their fibre product over `S`, with the projections
`φ₁ : P ⟶ M` and `φ₂ : P ⟶ N`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitProduct`).
**Gabber's Künneth formula** (Illusie, *Autour du théorème de monodromie locale*, Thm. 4.7;
blueprint `sk-prop-tf-nearby-external-kunneth`) says that the Künneth map of nearby cycles
```
Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)
```
(`NearbyCyclesModel.kunnethMap`) is an isomorphism for bounded constructible `A` and `B`
(`NearbyCyclesModel.isIso_kunnethMap`).

## Proof

By induction on the chart dimension, simultaneously for all separably closed fields `k'`
(`NearbyCyclesModel.kunnethFormula`), and after the reduction to proper models with compatible
geometric generic fibres (`NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula`), this is
`NearbyCyclesModel.isIso_kunnethMap_of_isProper`, whose inputs are supplied here: Deligne's
finiteness theorem for the nearby cycles
(`NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`,
`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`) and the monoidality of the
nearby cycles of the trait on the cohomology of the geometric generic fibres
(`NearbyCyclesModel.isIso_kunnethMap_traitGenericModel_of_shiftDecomposition`), the complexes
on the geometric generic point being finite direct sums of shifts of the unit, and Gabber's formula
in smaller chart dimension over the traits of the generic slices.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k']

section Product

variable {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left}

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Gabber's Künneth formula in every chart dimension** (Illusie, *Autour du théorème de
monodromie locale*, Thm. 4.7; blueprint `sk-prop-tf-nearby-external-kunneth`), by induction on the
chart dimension `n`, simultaneously for all separably closed fields `k'`
(`NearbyCyclesModel.KunnethFormula`). By the reduction to proper models
(`NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula`), this is
`NearbyCyclesModel.isIso_kunnethMap_of_isProper`, whose inputs are Deligne's finiteness theorem,
the monoidality of the nearby cycles of the trait on the cohomology of the geometric generic
fibres, and, for the generic slices, the Künneth formula in smaller chart dimension over the
trait `Spec K⟦t⟧`, `K = k'(x)^alg`. -/
theorem kunnethFormula (n : ℕ) :
    ∀ (k' : Type u) [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
      [Fact (ringChar k' ≠ ℓ)], KunnethFormula ℓ k' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k' _ _ _ _ X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂' φ₁ φ₂ qM gM qN gN hM hN hpb hP hgen m₁ m₂
    hle h₁ h₂ eM heM eN heN A B hA hB
  refine isIso_kunnethMap_of_properKunnethFormula (n := n)
    (fun {X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂'} φ₁ φ₂ {qM gM qN gN} hM hN hpb hP hgen hqM hqN
      {m₁ m₂} hle h₁ h₂ {eM} heM {eN} heN {A B} hA hB ↦ ?_) hM hN hpb hP hgen hle h₁ h₂ heM heN
    hA hB
  have hIH : 0 < m₁ + m₂ → KunnethFormula ℓ (traitSliceField k') (m₁ + m₂ - 1) := fun hpos ↦ by
    have : Fact (ringChar (traitSliceField k')).Prime :=
      ⟨by rw [ringChar_traitSliceField]; exact Fact.out⟩
    have : Fact (ringChar (traitSliceField k') ≠ ℓ) :=
      ⟨by rw [ringChar_traitSliceField]; exact Fact.out⟩
    have h := ih (m₁ + m₂ - 1) (by omega)
    exact @h (traitSliceField k') _ _ _ _
  have := hqM
  have := hqN
  have : LocallyOfFiniteType (Over.mk gM).hom := MorphismProperty.of_isPullback
    hM.isPullback_j hM.locallyOfFiniteType
  have : QuasiCompact (Over.mk gM).hom := MorphismProperty.of_isPullback hM.isPullback_j
    hM.quasiCompact
  have : IsSeparated (Over.mk gM).hom := MorphismProperty.of_isPullback hM.isPullback_j
    hM.isSeparated
  have : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of (traitGenericField k'))))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  have : QuasiCompact (Over.mk (𝟙 (Spec (.of (traitGenericField k'))))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 _))
  have : IsSeparated (Over.mk (𝟙 (Spec (.of (traitGenericField k'))))).hom :=
    inferInstanceAs (IsSeparated (𝟙 _))
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.quasiCompact
  have : IsSeparated Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.isSeparated
  have hΨA := preservesBoundedConstructible_of_isTraitModel M hM.isTraitModel ⟨eM, heM⟩ A hA
  have := hP.locallyOfFiniteType
  have := hP.quasiCompact
  have hΨB := preservesBoundedConstructible_of_isTraitModel N hN.isTraitModel ⟨eN, heN⟩ B hB
  have hpush := boundedConstructible_rightDerivedLowerStar_obj ℓ
    (Over.homMk (U := Over.mk gM) (V := Over.mk (𝟙 (Spec (.of (traitGenericField k'))))) gM
      (Category.comp_id _)) ⟨_, boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A hA⟩
  exact isIso_kunnethMap_of_isProper hM hN hpb hP hgen h₁ h₂ hIH heM heN hA hB hΨA hΨB
    (boundedConstructible_kunnethMap_source hΨA hΨB)
    (boundedConstructible_kunnethMap_target (φ₁ := φ₁) (φ₂ := φ₂) (φ₁.total ≫ qM)
      (fun C₀ hC₀ ↦ boundedConstructible_geometricNearbyCycles_obj P hP.isTraitModel hC₀)
      heM heN hA hB)
    (isIso_kunnethMap_traitGenericModel_of_shiftDecomposition _ k' _ _
      (nonempty_shiftDecomposition_of_boundedConstructible ℓ _ hpush))
    (fun S hS C hC hU hΓ ↦ isZero_of_isZero_upperStar_finsetComplOpens ℓ S hS C hC hU hΓ)


/-- **Gabber's Künneth formula for nearby cycles** (Illusie, *Autour du théorème de monodromie
locale*, Thm. 4.7; SGA 7 XIII; blueprint `sk-prop-tf-nearby-external-kunneth`): for the product
`P` over the strictly henselian trait `Spec k'⟦t⟧` of two models `M`, `N` of finite type and
bounded constructible `A`, `B`, the Künneth map of nearby cycles
`Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)` is an isomorphism. The blueprint node is stated for
finite `ℓ`-primary coefficients and `D^b_ctf`; the statement here, for bounded constructible
`ℚ̄_ℓ`-complexes, follows from it by passage to the limit (Bhatt–Scholze, §6.8). The total spaces
locally embed into affine spaces of some dimension
(`AlgebraicGeometry.Scheme.Hom.exists_locallyEmbedsInAffineSpace`), so this is
`NearbyCyclesModel.kunnethFormula`. -/
theorem isIso_kunnethMap {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'} (h : IsTraitProduct φ₁ φ₂)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B) := by
  obtain ⟨qM, gM, qN, gN, hM, hN, hpb, hP, hc⟩ := h.exists_isTraitModelOver
  obtain ⟨eM, heM⟩ := h.exists_comp_ε_left
  obtain ⟨eN, heN⟩ := h.exists_comp_ε_right
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hN.locallyOfFiniteType
  have := hN.quasiCompact
  obtain ⟨m₁, h₁⟩ := Scheme.Hom.exists_locallyEmbedsInAffineSpace qM
  obtain ⟨m₂, h₂⟩ := Scheme.Hom.exists_locallyEmbedsInAffineSpace qN
  exact kunnethFormula ℓ (m₁ + m₂) k' φ₁ φ₂ hM hN hpb hP hc le_rfl h₁ h₂ heM heN hA hB

end Product

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
