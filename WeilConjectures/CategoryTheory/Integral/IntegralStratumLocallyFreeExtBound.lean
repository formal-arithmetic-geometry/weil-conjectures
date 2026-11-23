/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsHeartData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.AlgebraicGeometry.Open.LocallyClosedExtensionConstantModelConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import all WeilConjectures.CategoryTheory.Integral.IntegralDualTorsionHeartSections
import all WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsAssembly

/-!
# `Ext` out of a locally free integral module into a bounded torsion complex

Let `S` be a noetherian scheme with `cd_ℓ(S) ≤ s` and `L` a locally free module over the
continuous integral coefficient ring `𝒪_{E,S}`. For a complex `K` with classical, locally
`ℓ`-power torsion cohomology in degrees `[a, b]`,

`Hom(L[0], K[r]) = 0` for `r > b + s`

(`CategoryTheory.subsingleton_hom_singleFunctor_shift_of_isLocallyFree`).

## Implementation details

`L[0]` has the dual `L^∨[0]` with `L^∨` locally free, so `L^∨[0] ⊗ F[0] = (L^∨ ⊗ F)[0]` for every
module `F`. For a classical torsion module `F` this sheaf is classical and torsion
(`CategoryTheory.integralStratumFiniteCdReductions_heart_data`), so its cohomology vanishes above
`s`. Bounded-heart amplitude then bounds `RΓ(S, L^∨ ⊗ K)` above by `b + s`.

For an `L` with an arbitrary finite constant local model the dual has Tor amplitude `[0, 1]`, and
`CategoryTheory.integralStratumFiniteCdReductions_assembly` only gives the bound `b + s + 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace AlgebraicGeometry.ProEtale

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- The derived internal hom out of `L[0]`, for a locally free `L`, is tensoring with `L'[0]`,
where `L'` is a locally free dual of `L`. -/
lemma IsLocallyFree.exists_derivedHom_iso_tensorLeft {S : Scheme.{u}} {L : supportModules Λ S}
    (hL : IsLocallyFree (condensedRingObj Λ S) L) :
    ∃ L' : supportModules Λ S, IsLocallyFree (condensedRingObj Λ S) L' ∧
      Nonempty ((CondensedRing.derivedHom Λ S).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj L)) ≅
        tensorLeft ((DerivedCategory.singleFunctor _ 0).obj L')) := by
  obtain ⟨L', hL', ⟨p⟩⟩ := hL.exists_exactPairing_singleFunctor 0
  let P := (DerivedCategory.singleFunctor (supportModules Λ S) 0).obj L
  let P' := (DerivedCategory.singleFunctor (supportModules Λ S) 0).obj L'
  let : ExactPairing P' P := p
  let adj : (CondensedRing.derivedTensor Λ S).obj P ⊣ tensorLeft P' := tensorLeftAdjunction P' P
  exact ⟨L', hL', ⟨(CondensedRing.derivedTensorHomAdjunction Λ P).rightAdjointUniq adj⟩⟩

/-- For a locally free `L`, the derived dual `RHom(L[0], Λ_S)` tensored with a module placed in
degree `0` has no cohomology outside degree `0`. -/
lemma isZero_homology_stratumModuleDual_tensor_singleFunctor {S : Scheme.{u}}
    {L : supportModules Λ S} (hL : IsLocallyFree (condensedRingObj Λ S) L)
    (F : supportModules Λ S) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.derivedTensor Λ S).obj (stratumModuleDual Λ S L)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  obtain ⟨L', hL', ⟨eh⟩⟩ := hL.exists_derivedHom_iso_tensorLeft
  let eD : stratumModuleDual Λ S L ≅ (DerivedCategory.singleFunctor _ 0).obj L' :=
    eh.app _ ≪≫ ρ_ _
  let e := whiskerRightIso eD ((DerivedCategory.singleFunctor _ 0).obj F) ≪≫
    hL'.singleFunctorTensorObjIso F 0
  let Y := (DerivedCategory.singleFunctor _ 0).obj (L' ⊗ F)
  have hY : IsZero ((DerivedCategory.homologyFunctor _ q).obj Y) := by
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact Y.isZero_of_isGE 0 q hq
    · exact Y.isZero_of_isLE 0 q hq
  exact hY.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e)

end AlgebraicGeometry.ProEtale

namespace CategoryTheory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Let `L` be a locally free module over the continuous integral coefficient ring `𝒪_{E,S}`,
and `F` a classical locally `ℓ`-power torsion module. Then
`RΓ(S, RHom(L[0], 𝒪_{E,S}) ⊗ F[0])` is concentrated in degrees `[0, s]` when `cd_ℓ(S) ≤ s`. -/
theorem isZero_homology_stratumModuleDerivedSections_dual_tensor_of_isLocallyFree
    (S : Scheme.{u}) [IsNoetherian S]
    {L : supportModules (IntegralQuotient.integral l E) S}
    (hL : IsLocallyFree (condensedRingObj (IntegralQuotient.integral l E) S) L)
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (F : supportModules (IntegralQuotient.integral l E) S)
    (hF : IsClassicalAbelian F.X ∧ IsEllPowerTorsionLocal l (Fact.out : l.Prime) F.X)
    (i : ℤ) (hi : i < 0 ∨ (s : ℤ) < i) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
      ((stratumModuleDerivedSections (IntegralQuotient.integral l E) S).obj
        (((CondensedRing.derivedTensor (IntegralQuotient.integral l E) S).obj
          (stratumModuleDual (IntegralQuotient.integral l E) S L)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (hs.trans_lt (WithTop.coe_lt_top s)).ne
  have hts : t ≤ s := WithTop.coe_le_coe.mp (ht ▸ hs)
  obtain ⟨-, hcoh⟩ := integralStratumFiniteCdReductions_heart_data l E S L
    (IsLocallyFree.hasFiniteConstantLocalModel _ hL) F hF
  let G := stratumModuleDerivedSections (IntegralQuotient.integral l E) S
  let : G.CommShift ℤ := by dsimp only [G, stratumModuleDerivedSections]; infer_instance
  let : G.IsTriangulated := by dsimp only [G, stratumModuleDerivedSections]; infer_instance
  have h := amplitude_from_heart_images G 0 0 0 (t : ℤ) le_rfl (by omega) _
    (fun q hq ↦ isZero_homology_stratumModuleDual_tensor_singleFunctor hL F q (by omega))
    (fun q i hi ↦ module_sections_bound l (Fact.out : l.Prime) _ S t ht _ (hcoh q).1
      ((isEllPowerTorsion_iff_local l (Fact.out : l.Prime) _).mpr (hcoh q).2) i hi)
  exact h i (by omega)

/-- Let `S` be a noetherian scheme with `cd_ℓ(S) ≤ s`, and `L` a locally free module over the
continuous integral coefficient ring `𝒪_{E,S}`. For a complex
`K` with classical, locally `ℓ`-power torsion cohomology in degrees `[a, b]`, we have
`Hom(L[0], K[r]) = 0` for `r > b + s`. -/
theorem subsingleton_hom_singleFunctor_shift_of_isLocallyFree
    (S : Scheme.{u}) [IsNoetherian S]
    (L : supportModules (IntegralQuotient.integral l E) S)
    (hL : IsLocallyFree (condensedRingObj (IntegralQuotient.integral l E) S) L)
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (K : DerivedCategory (supportModules (IntegralQuotient.integral l E) S))
    (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X)
    (r : ℤ) (hr : b + (s : ℤ) < r) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj L ⟶ K⟦r⟧) := by
  let Λ := IntegralQuotient.integral l E
  let A := supportModules Λ S
  let D := stratumModuleDual Λ S L
  let G := stratumModuleDerivedSections Λ S
  let U := (CondensedRing.derivedTensor Λ S).obj D
  let T := U ⋙ G
  let : G.CommShift ℤ := by dsimp only [G, stratumModuleDerivedSections]; infer_instance
  let : G.IsTriangulated := by dsimp only [G, stratumModuleDerivedSections]; infer_instance
  let : U.CommShift ℤ := by dsimp only [U, CondensedRing.derivedTensor]; infer_instance
  let : U.IsTriangulated := by dsimp only [U, CondensedRing.derivedTensor]; infer_instance
  let : T.CommShift ℤ := Functor.CommShift.comp U G
  let : T.IsTriangulated := by infer_instance
  have hb := amplitude_from_heart_images T a b 0 (s : ℤ) hab (by omega) K hK
    (fun q i hi ↦ isZero_homology_stratumModuleDerivedSections_dual_tensor_of_isLocallyFree
      l E S hL s hs _ (hclass q) i hi)
  have hz : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj (T.obj (K⟦r⟧))) :=
    ((hb r (Or.inr (by omega))).of_iso
      (((DerivedCategory.homologyFunctor Ab.{u + 1} 0).shiftIso r 0 r (by omega)).app
        (T.obj K))).of_iso ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).mapIso
          ((T.commShiftIso r).app K))
  let P := (DerivedCategory.singleFunctor A 0).obj L
  let H := (CondensedRing.derivedHom Λ S).obj (op P)
  obtain ⟨L', -, ⟨eh⟩⟩ := hL.exists_derivedHom_iso_tensorLeft
  let eD : D ≅ (DerivedCategory.singleFunctor _ 0).obj L' := eh.app _ ≪≫ ρ_ _
  let e : H.obj (K⟦r⟧) ≅ U.obj (K⟦r⟧) := eh.app _ ≪≫ whiskerRightIso eD.symm _
  exact subsingleton_hom_of_internal_sections (Mod.regular (condensedRingObj Λ S))
    (DerivedCategory.singleFunctorObjUnitIso _) P (K⟦r⟧) H
    (CondensedRing.derivedTensorHomAdjunction Λ P)
    (hz.of_iso ((DerivedCategory.homologyFunctor _ 0).mapIso (G.mapIso e)))

end CategoryTheory
