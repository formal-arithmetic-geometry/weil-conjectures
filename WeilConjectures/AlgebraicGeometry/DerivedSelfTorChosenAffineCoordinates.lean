/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinates

import WeilConjectures.AlgebraicGeometry.QuotientResolutionTensorComparison

/-! # Intrinsic affine self-Tor for one chosen augmented lift

## References

* Stacks Project, Tags 08DX, 06YH, 01I9 and 00LS
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

private theorem quotient_section_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (U : Y.affineOpens) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    ∃ s : ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U) ≃ₗ[Γ(Y, U.1)]
        B.val.obj (op U.1),
      ∀ x : Γ(Y, U.1), s (Ideal.Quotient.mk _ x) = i.app U.1 x := by
  let φ := (i.app U.1).hom
  have hI : i.ker.ideal U = RingHom.ker φ := i.ker_apply U
  let q := Ideal.Quotient.lift (i.ker.ideal U) φ (by
    intro x hx
    have hx' : x ∈ RingHom.ker φ := by simpa only [hI] using hx
    exact hx')
  have hq : Function.Bijective q := by
    exact ⟨RingHom.lift_injective_of_ker_le_ideal _ _ (by rw [hI]),
      Ideal.Quotient.lift_surjective_of_surjective _ _ (i.app_surjective U.1 U.2)⟩
  let l : ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U) →ₗ[Γ(Y, U.1)]
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).val.obj (op U.1) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := by
        intro r x
        change q (Ideal.Quotient.mk _ r * x) = φ r * q x
        exact q.map_mul _ _ }
  exact ⟨LinearEquiv.ofBijective l hq, fun _ ↦ rfl⟩

set_option linter.unusedVariables false in
/-- Intrinsic self-Tor has affine resolution coordinates compatible with one augmented
lift of the canonical quotient restriction on each basic inclusion.
This theorem only constructs one compatible augmented lift on each basic inclusion;
compatibility with every supplied lift requires the separate homotopy argument
(Stacks, Tags 08DX, 06YH, 01I9 and 00LS). -/
theorem exists_derived_selfTor_chosen_affine_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (n : ℕ) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let D := DerivedCategory.Q.obj (S.obj B)
    let Q := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj (D ⊗ D)
    ∃ c : ∀ U : Y.affineOpens,
        ((((tensorRight (ModuleCat.of (Γ(Y, U.1) : Type u)
          ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).mapHomologicalComplex (.down ℕ)).obj
            (projectiveResolution (ModuleCat.of (Γ(Y, U.1) : Type u)
              ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).complex).homology n) ≃ₗ[Γ(Y, U.1)]
              Q.val.obj (op U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
          let A := (Γ(Y, U.1) : Type u)
          let C := (Γ(Y, V.1) : Type u)
          let I := i.ker.ideal U
          let J := i.ker.ideal V
          let φ := (Y.presheaf.map (homOfLE h).op).hom
          let P := projectiveResolution (ModuleCat.of A (A ⧸ I))
          let R := projectiveResolution (ModuleCat.of C (C ⧸ J))
          let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)
          let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex
            (.down ℕ)
          let ψ := Ideal.quotientMap J φ
            (fun x hx ↦ i.ker.ideal_le_comap_ideal h hx)
          ∃ (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj R.complex)
            (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) ∧
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) ∧
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  classical
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := Z.ringCatSheaf)
  have : B.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion i _
  let MA := fun U : Y.affineOpens ↦ ModuleCat.of (Γ(Y, U.1) : Type u)
    ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U)
  choose s hs using quotient_section_coordinates i
  let P := fun U : Y.affineOpens ↦ projectiveResolution (MA U)
  let M := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let := HasDerivedCategory.standard M
  let := SheafOfModules.monoidalCategory Y.sheaf
  let N := (CochainComplex.singleFunctor M 0).obj B
  -- Direct elimination keeps the conclusion fixed while introducing the resolution witnesses.
  refine (CochainComplex.exists_isKFlatResolution N).elim fun K hK' ↦
    hK'.elim fun q hK' ↦ ?_
  have hK := hK'.1
  have hq := hK'.2.2.1
  have : QuasiIso q := hq
  refine (kFlat_derivedTensor_comparison_natIso Y
    ((Functor.const (Discrete Unit)).obj K)
    ((Functor.const (Discrete Unit)).obj N) (fun _ ↦ hK)).elim fun comparison ↦ ?_
  let d := asIso (DerivedCategory.Q.map q)
  let H := DerivedCategory.homologyFunctor M (-(n : ℤ))
  let e := (H.mapIso ((tensorIso d (Iso.refl _)).symm ≪≫
    (comparison.app ⟨()⟩).app ⟨()⟩) ≪≫
      (DerivedCategory.homologyFunctorFactors M (-(n : ℤ))).app _).symm
  refine (exists_qcoh_ordinary_tensor_resolution_coordinates
    Y B B MA MA s s P K q hK hq n).elim fun c₀ hc ↦ ?_
  let c := fun U : Y.affineOpens ↦
    (c₀ U).trans (Scheme.Modules.appLinearEquivOfIso e U.1)
  refine ⟨c, ?_⟩
  intro V U h hbasic A C I J φ PU PV TA TC ψ
  have hI : ∀ x ∈ I, φ x ∈ J := fun x hx ↦ i.ker.ideal_le_comap_ideal h hx
  refine (exists_quotient_resolution_tensor_comparison A C I J φ hI PU PV).elim
    fun ψ₀ hψ₀ ↦ hψ₀.elim fun a ha ↦ ha.elim fun k hk' ↦ ?_
  have hψ₀ := hk'.1
  have ha := hk'.2.1
  have hk := hk'.2.2
  have hψeq : ψ₀ = ψ := by
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact hψ₀ x
  subst ψ₀
  let b : (A ⧸ I) →ₛₗ[φ] (C ⧸ J) :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := by
        intro r y
        change ψ (Ideal.Quotient.mk I r * y) = Ideal.Quotient.mk J (φ r) * ψ y
        exact ψ.map_mul _ _ }
  have hb : ∀ y : A ⧸ I,
      s V (b y) = B.val.map (homOfLE h).op (s U y) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    change s V (Ideal.Quotient.mk J (φ x)) =
      B.val.map (homOfLE h).op (s U (Ideal.Quotient.mk I x))
    rw [hs U, hs V]
    exact ConcreteCategory.congr_hom (i.naturality (homOfLE h).op) x
  refine ⟨a, k, ha, hk, ?_⟩
  have hn := hc V U h hbasic b a k (fun x ↦ by rw [ha]; exact hb _) hb hk
  intro es x
  have he := PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op (c₀ U x)
  change _ = e.hom.val.app (op V.1) _
  exact he.symm.trans (congrArg (e.hom.val.app (op V.1)) (hn x))

end AlgebraicGeometry
