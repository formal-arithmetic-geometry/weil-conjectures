/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyPropertyWindow
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarUniformBound

/-!
# Proper direct image of unbounded complexes with ind-constructible cohomology

Let `Dic(X, Λ)` be the complexes of sheaves of `Λ_X`-modules with cohomology in
`IndCons(X, Λ)` (`DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _)`). Let
`p : Z ⟶ Y` be a proper morphism to a separated `k`-scheme of finite type and `d` a natural number
bounding the dimensions of all geometric fibres of `p`. For the coefficient rings `Λ = E`
(a finite extension of `ℚ_ℓ`) and `Λ = ℚ̄_ℓ` we prove blueprint
`lemma-proper-direct-image-unbounded-complexes`:

1. `Rp_*` maps `Dic(Z, Λ)` into `Dic(Y, Λ)`, with `Rp_* Dic^{≤ b}(Z) ⊆ Dic^{≤ b + 2d + 1}(Y)` and
   `Rp_* Dic^{≥ a}(Z) ⊆ Dic^{≥ a}(Y)`;
2. for `K ∈ Dic(Z, Λ)` and every `q`, the truncation maps
   `K ← τ_{≤ q} K → τ_{≥ q - 2d - 1} τ_{≤ q} K` induce isomorphisms
   `H^q(Rp_* K) ≃ H^q(Rp_* τ_{≥ q - 2d - 1} τ_{≤ q} K)` between objects of `IndCons(Y, Λ)`;
3. `Rp_* : Dic(Z, Λ) → Dic(Y, Λ)` preserves arbitrary direct sums.

The proofs combine the uniform bound on `IndCons(Z, Λ)`
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerStar_uniformBound_continuousMapRingObj`
and its `ℚ̄_ℓ` analogue), the ind-constructible heart (`IsIndConstructibleHeart`) and the abstract
results of `WeilConjectures.CategoryTheory.DerivedCategory.HomologyPropertyWindow` and
`WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty` (left
completeness, dévissage).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl DerivedCategory.TStructure

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℤ)
  (hn : ∀ M, IsIndConstructibleModuleObject (condensedRingObj Λ Z) M →
    (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE n)

include hn in
/-- If `Rp_*` sends `IndCons(Z, Λ)` into degrees `≤ n`, it sends `Dic^{≤ b}(Z, Λ)` into degrees
`≤ b + n + 1`. -/
lemma isLE_rightDerivedLowerStar_obj_of_homologyProperty
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _) K)
    (b : ℤ) [K.IsLE b] :
    (R((p)_*⟦Λ⟧).obj K).IsLE (b + n + 1) :=
  DerivedCategory.isLE_obj_add_one_of_homologyProperty _ _ n hn K hK b

include hn in
/-- If `Rp_*` sends `IndCons(Z, Λ)` into degrees `≤ n`, then for `K ∈ Dic(Z, Λ)` the truncation
maps `K ← τ_{≤ q} K → τ_{≥ q - n - 1} τ_{≤ q} K` induce isomorphisms on `H^q ∘ Rp_*`. -/
lemma isIso_homologyFunctor_map_rightDerivedLowerStar_truncation
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _) K) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (R((p)_*⟦Λ⟧).map ((t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (R((p)_*⟦Λ⟧).map ((t.truncGEπ (q - n - 1)).app ((t.truncLE q).obj K)))) :=
  ⟨DerivedCategory.isIso_homologyFunctor_map_truncLEι _
      (fun X a _ ↦ Functor.isGE_rightDerivedFunctor_obj _ X a) K q,
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_of_homologyProperty _ _ n hn K hK q⟩

include hn in
/-- If `Rp_*` sends `IndCons(Z, Λ)` into degrees `≤ n` and into `Dic(Y, Λ)`, and `IndCons(Y, Λ)`
is closed under kernels, cokernels and extensions, then `Rp_*` maps `Dic(Z, Λ)` into
`Dic(Y, Λ)`. -/
lemma homologyProperty_rightDerivedLowerStar_obj
    (hY : IsIndConstructibleHeart (condensedRingObj Λ Y))
    (hq : ∀ M, IsIndConstructibleModuleObject (condensedRingObj Λ Z) M → ∀ q : ℤ,
      IsIndConstructibleModuleObject (condensedRingObj Λ Y)
        ((DerivedCategory.homologyFunctor _ q).obj
          (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _) K) :
    DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _) (R((p)_*⟦Λ⟧).obj K) :=
  have := hY.isClosedUnderKernels
  have := hY.isClosedUnderCokernels
  have := hY.isClosedUnderExtensions
  DerivedCategory.homologyProperty_obj_of_homologyProperty _ _ n _ hn
    (fun X a _ ↦ Functor.isGE_rightDerivedFunctor_obj _ X a) hq K hK

include hn in
/-- If `Rp_*` sends `IndCons(Z, Λ)` into degrees `≤ n`, `p` is quasi-compact and
quasi-separated, `Λ_Z` is flat and `IndCons(Z, Λ)` is closed under kernels, cokernels,
extensions and direct sums, then `Rp_* : Dic(Z, Λ) → D(Y, Λ)` preserves direct sums. -/
lemma preservesColimitsOfShape_homologyProperty_rightDerivedLowerStar [QuasiCompact p]
    [QuasiSeparated p] [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ Z))]
    (hZ : IsIndConstructibleHeart (condensedRingObj Λ Z)) (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      ((DerivedCategory.homologyProperty
        (IsIndConstructibleModuleObject (condensedRingObj Λ Z))).ι ⋙ R((p)_*⟦Λ⟧)) := by
  have := hZ.isClosedUnderKernels
  have := hZ.isClosedUnderCokernels
  have := hZ.isClosedUnderExtensions
  have := hZ.isClosedUnderColimitsOfShape_discrete J
  have := hasColimitsOfShape_discrete_derivedCategory_mod (condensedRingObj Λ Z) J
  let L := DerivedCategory.homologyProperty
    (IsIndConstructibleModuleObject (condensedRingObj Λ Z))
  have : L.IsClosedUnderColimitsOfShape (Discrete J) :=
    ⟨fun _ ⟨h⟩ ↦ L.prop_of_iso
      (h.isColimit.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
        HasColimit.isoOfNatIso Discrete.natIsoFunctor).symm
      (DerivedCategory.homologyProperty_sigma _ _ fun j ↦ h.prop_diag_obj ⟨j⟩)⟩
  have (M : J → L.FullSubcategory) : PreservesColimit (Discrete.functor M) (L.ι ⋙ R((p)_*⟦Λ⟧)) := by
    have := DerivedCategory.isIso_sigmaComparison_of_homologyProperty R((p)_*⟦Λ⟧)
      (IsIndConstructibleModuleObject (condensedRingObj Λ Z)) n hn
      (fun X a _ ↦ Functor.isGE_rightDerivedFunctor_obj _ X a)
      (fun N _ ↦ isIso_sigmaComparison_rightDerivedLowerStar_singleFunctor Λ p J N)
      (fun j ↦ (M j).obj) fun j ↦ (M j).property
    have : PreservesColimit (Discrete.functor fun j ↦ (M j).obj) R((p)_*⟦Λ⟧) :=
      PreservesCoproduct.of_iso_comparison _ _
    have : PreservesColimit (Discrete.functor M ⋙ L.ι) R((p)_*⟦Λ⟧) :=
      preservesColimit_of_iso_diagram _ (Discrete.natIso (F := Discrete.functor fun j ↦ (M j).obj)
        (G := Discrete.functor M ⋙ L.ι) fun _ ↦ Iso.refl _)
    have : HasColimit (Discrete.functor M ⋙ L.ι) := HasColimitsOfShape.has_colimit _
    have : CreatesColimit (Discrete.functor M) L.ι :=
      createsColimitFullSubcategoryInclusionOfClosed _ L _
    have : PreservesColimit (Discrete.functor M) L.ι :=
      preservesColimit_of_createsColimit_and_hasColimit _ _
    exact comp_preservesColimit L.ι R((p)_*⟦Λ⟧)
  exact preservesColimitsOfShape_of_discrete _

end General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] (p : Z ⟶ Y) [IsProper p] (d : ℕ)
  (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
    topologicalKrullDim (pullback p s : Scheme.{u}) ≤ (d : WithBot ℕ∞))

/-! ### The coefficient ring `E` -/

section ContinuousMapRingObj

include aY hd in
/-- Blueprint `lemma-proper-direct-image-unbounded-complexes--1`, for the coefficient ring `E` of
a finite extension `E` of `ℚ_ℓ`: `Rp_*` maps `Dic(Z, E)` into `Dic(Y, E)`, with
`Rp_* Dic^{≤ b}(Z, E) ⊆ Dic^{≤ b + 2d + 1}(Y, E)` and `Rp_* Dic^{≥ a}(Z, E) ⊆ Dic^{≥ a}(Y, E)`. -/
theorem rightDerivedLowerStar_indConstructibleDerived_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)))
    (hK : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _) K) :
    DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _)
      (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).obj K) ∧
    (∀ b : ℤ, K.IsLE b →
      (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).obj K).IsLE (b + 2 * d + 1)) ∧
    ∀ a : ℤ, K.IsGE a → (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).obj K).IsGE a := by
  have hn := fun M (hM : IsIndConstructibleModuleObject _ M) ↦
    isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj_of_isIndConstructible ℓ aY p d
      hd E hM
  refine ⟨homologyProperty_rightDerivedLowerStar_obj _ p _ hn
    (isIndConstructibleHeart_continuousMapRingObj ℓ E aY)
    (fun M hM q ↦ isIndConstructible_homology_rightDerivedLowerStar_continuousMapRingObj ℓ aY p E
      hM q) K hK, fun b _ ↦ ?_, fun a _ ↦ Functor.isGE_rightDerivedFunctor_obj _ K a⟩
  have := isLE_rightDerivedLowerStar_obj_of_homologyProperty _ p _ hn K hK b
  exact this

include aY hd in
/-- Blueprint `lemma-proper-direct-image-unbounded-complexes--2`, for the coefficient ring `E` of
a finite extension `E` of `ℚ_ℓ`: for `K ∈ Dic(Z, E)` and every `q`, the truncation maps
`K ← τ_{≤ q} K → τ_{≥ q - 2d - 1} τ_{≤ q} K` induce isomorphisms
`H^q(Rp_* K) ≃ H^q(Rp_* τ_{≤ q} K) ≃ H^q(Rp_* τ_{≥ q - 2d - 1} τ_{≤ q} K)` between objects of
`IndCons(Y, E)`. -/
theorem isIso_homologyFunctor_map_rightDerivedLowerStar_truncation_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)))
    (hK : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _) K) (q : ℤ) :
    IsIndConstructibleModuleObject _ ((DerivedCategory.homologyFunctor _ q).obj
      (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).obj K)) ∧
    IsIndConstructibleModuleObject _ ((DerivedCategory.homologyFunctor _ q).obj
      (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).obj
        ((t.truncGE (q - 2 * d - 1)).obj ((t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).map ((t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).map
        ((t.truncGEπ (q - 2 * d - 1)).app ((t.truncLE q).obj K)))) := by
  have hn := fun M (hM : IsIndConstructibleModuleObject _ M) ↦
    isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj_of_isIndConstructible ℓ aY p d
      hd E hM
  have hW : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _)
      ((t.truncGE (q - 2 * d - 1)).obj ((t.truncLE q).obj K)) :=
    DerivedCategory.homologyProperty_truncGE (DerivedCategory.homologyProperty_truncLE hK q) _
  exact ⟨(rightDerivedLowerStar_indConstructibleDerived_continuousMapRingObj ℓ aY p d hd E K
      hK).1 q,
    (rightDerivedLowerStar_indConstructibleDerived_continuousMapRingObj ℓ aY p d hd E _ hW).1 q,
    isIso_homologyFunctor_map_rightDerivedLowerStar_truncation _ p _ hn K hK q⟩

include aY hd in
/-- Blueprint `lemma-proper-direct-image-unbounded-complexes--3`, for the coefficient ring `E` of
a finite extension `E` of `ℚ_ℓ`: `Rp_* : Dic(Z, E) → Dic(Y, E)` preserves arbitrary direct sums
(direct sums in `Dic` are computed in the derived category). -/
theorem preservesColimitsOfShape_indConstructibleDerived_rightDerivedLowerStar_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      ((DerivedCategory.homologyProperty (IsIndConstructibleModuleObject
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z))).ι ⋙
          R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧)) := by
  obtain ⟨E', e, _⟩ := Profinite.exists_continuousMapRingObj_iso.{u} ℓ E
  have : PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)) :=
    preservesFiniteLimits_of_natIso
      ((curriedTensor _).mapIso ((upperStarFromPoint Z).mapIso e.symm))
  exact preservesColimitsOfShape_homologyProperty_rightDerivedLowerStar _ p _
    (fun _ hM ↦ isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj_of_isIndConstructible
      ℓ aY p d hd E hM) (isIndConstructibleHeart_continuousMapRingObj ℓ E (p ≫ aY)) J

end ContinuousMapRingObj

/-! ### The coefficient ring `ℚ̄_ℓ` -/

include aY hd in
/-- Blueprint `lemma-proper-direct-image-unbounded-complexes--1`, for the coefficient ring `ℚ̄_ℓ`:
`Rp_*` maps `Dic(Z, ℚ̄_ℓ)` into `Dic(Y, ℚ̄_ℓ)`, with
`Rp_* Dic^{≤ b}(Z, ℚ̄_ℓ) ⊆ Dic^{≤ b + 2d + 1}(Y, ℚ̄_ℓ)` and
`Rp_* Dic^{≥ a}(Z, ℚ̄_ℓ) ⊆ Dic^{≥ a}(Y, ℚ̄_ℓ)`. -/
theorem rightDerivedLowerStar_indConstructibleDerived_padicAlgClRingObj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z)))
    (hK : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _) K) :
    DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _)
      (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).obj K) ∧
    (∀ b : ℤ, K.IsLE b →
      (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).obj K).IsLE (b + 2 * d + 1)) ∧
    ∀ a : ℤ, K.IsGE a → (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).obj K).IsGE a := by
  have hn := fun M (hM : IsIndConstructibleModuleObject _ M) ↦
    isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj_of_isIndConstructible ℓ aY p d
      hd hM
  refine ⟨homologyProperty_rightDerivedLowerStar_obj _ p _ hn
    (isIndConstructibleHeart_padicAlgClRingObj ℓ aY)
    (fun M hM q ↦ isIndConstructible_homology_rightDerivedLowerStar_padicAlgClRingObj ℓ aY p
      hM q) K hK, fun b _ ↦ ?_, fun a _ ↦ Functor.isGE_rightDerivedFunctor_obj _ K a⟩
  have := isLE_rightDerivedLowerStar_obj_of_homologyProperty _ p _ hn K hK b
  exact this

include aY hd in
/-- Blueprint `lemma-proper-direct-image-unbounded-complexes--2`, for the coefficient ring `ℚ̄_ℓ`:
for `K ∈ Dic(Z, ℚ̄_ℓ)` and every `q`, the truncation maps
`K ← τ_{≤ q} K → τ_{≥ q - 2d - 1} τ_{≤ q} K` induce isomorphisms
`H^q(Rp_* K) ≃ H^q(Rp_* τ_{≤ q} K) ≃ H^q(Rp_* τ_{≥ q - 2d - 1} τ_{≤ q} K)` between objects of
`IndCons(Y, ℚ̄_ℓ)`. -/
theorem isIso_homologyFunctor_map_rightDerivedLowerStar_truncation_padicAlgClRingObj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z)))
    (hK : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _) K) (q : ℤ) :
    IsIndConstructibleModuleObject _ ((DerivedCategory.homologyFunctor _ q).obj
      (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).obj K)) ∧
    IsIndConstructibleModuleObject _ ((DerivedCategory.homologyFunctor _ q).obj
      (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).obj
        ((t.truncGE (q - 2 * d - 1)).obj ((t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).map ((t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).map
        ((t.truncGEπ (q - 2 * d - 1)).app ((t.truncLE q).obj K)))) := by
  have hn := fun M (hM : IsIndConstructibleModuleObject _ M) ↦
    isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj_of_isIndConstructible ℓ aY p d
      hd hM
  have hW : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject _)
      ((t.truncGE (q - 2 * d - 1)).obj ((t.truncLE q).obj K)) :=
    DerivedCategory.homologyProperty_truncGE (DerivedCategory.homologyProperty_truncLE hK q) _
  exact ⟨(rightDerivedLowerStar_indConstructibleDerived_padicAlgClRingObj ℓ aY p d hd K hK).1 q,
    (rightDerivedLowerStar_indConstructibleDerived_padicAlgClRingObj ℓ aY p d hd _ hW).1 q,
    isIso_homologyFunctor_map_rightDerivedLowerStar_truncation _ p _ hn K hK q⟩

include aY hd in
/-- Blueprint `lemma-proper-direct-image-unbounded-complexes--3`, for the coefficient ring `ℚ̄_ℓ`:
`Rp_* : Dic(Z, ℚ̄_ℓ) → Dic(Y, ℚ̄_ℓ)` preserves arbitrary direct sums (direct sums in `Dic` are
computed in the derived category). -/
theorem preservesColimitsOfShape_indConstructibleDerived_rightDerivedLowerStar_padicAlgClRingObj
    (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      ((DerivedCategory.homologyProperty (IsIndConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z))).ι ⋙
          R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧)) :=
  preservesColimitsOfShape_homologyProperty_rightDerivedLowerStar _ p _
    (fun _ hM ↦ isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj_of_isIndConstructible
      ℓ aY p d hd hM) (isIndConstructibleHeart_padicAlgClRingObj ℓ (p ≫ aY)) J

end AlgebraicGeometry.ProEtale.CondensedRing
