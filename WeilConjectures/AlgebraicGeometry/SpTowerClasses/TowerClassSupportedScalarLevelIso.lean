/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassSupportedScalarSource
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.PowerSystemOrdinaryCokernel
public import Mathlib.Algebra.Homology.ShortComplex.Ab
/-! # Levelwise invertibility of the supported scalar comparison

The ordinary scalar adjunct of the supported quotient system is checked level by level.
At level `n` the reduced source is a cokernel of `l ^ (n + 1)`, and a basis of the finite
coefficient ring presents both sides as cokernels of `l ^ (n + 1)` on copies of the
supported integer sheaf.
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule

section BiproductCokernel


variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]

theorem nsmul_id_comp_biproduct_map {Z Q : C} (k : ℕ) (π : Z ⟶ Q) (hπ : (k • 𝟙 Z) ≫ π = 0)
    (d : ℕ) : (k • 𝟙 (⨁ fun _ : Fin d ↦ Z)) ≫ biproduct.map (fun _ ↦ π) = 0 := by
  have hπ' : k • π = 0 := by rwa [Preadditive.nsmul_comp, Category.id_comp] at hπ
  rw [Preadditive.nsmul_comp, Category.id_comp]
  apply biproduct.hom_ext'
  intro j
  rw [Preadditive.comp_nsmul, biproduct.ι_map, ← Preadditive.nsmul_comp, hπ', zero_comp,
    comp_zero]

theorem nsmul_id_comp_ι_comp {Z W : C} (k : ℕ) (d : ℕ) (e : (⨁ fun _ : Fin d ↦ Z) ⟶ W)
    (he : (k • 𝟙 (⨁ fun _ : Fin d ↦ Z)) ≫ e = 0) (i : Fin d) :
    (k • 𝟙 Z) ≫ biproduct.ι (fun _ : Fin d ↦ Z) i ≫ e = 0 := by
  rw [Preadditive.nsmul_comp, Category.id_comp, ← Preadditive.comp_nsmul, ← Category.id_comp e,
    ← Preadditive.nsmul_comp, he, comp_zero]

/-- A finite biproduct of copies of a cokernel of `k • 𝟙` is a cokernel of `k • 𝟙`. -/
def biproductCokernelNsmul {Z Q : C} (k : ℕ) (π : Z ⟶ Q) (hπ : (k • 𝟙 Z) ≫ π = 0)
    (h : IsColimit (CokernelCofork.ofπ π hπ)) (d : ℕ) :
    IsColimit (CokernelCofork.ofπ _ (nsmul_id_comp_biproduct_map k π hπ d)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {W} e he ↦ biproduct.desc fun i ↦ h.desc
      (CokernelCofork.ofπ (biproduct.ι (fun _ : Fin d ↦ Z) i ≫ e)
      (nsmul_id_comp_ι_comp k d e he i)))
    (fun {W} e he ↦ by
      ext i
      simp only [biproduct.ι_map_assoc, biproduct.ι_desc]
      exact h.fac _ WalkingParallelPair.one)
    (fun {W} e he m hm ↦ by
      ext i
      simp only [biproduct.ι_desc]
      apply Cofork.IsColimit.hom_ext h
      rw [Cofork.π_ofπ, ← biproduct.ι_map_assoc (fun _ : Fin d ↦ π) i m, hm]
      exact (h.fac (CokernelCofork.ofπ _ (nsmul_id_comp_ι_comp k d e he i))
        WalkingParallelPair.one).symm)

end BiproductCokernel

/-- Two cokernel descriptions and an epimorphic comparison force an isomorphism: if
`⨁ π` followed by an epimorphism `β` and a map `φ` is a cokernel of `k • 𝟙`, where
`π` is a cokernel of `k • 𝟙`, then `φ` is invertible. -/
theorem isIso_of_biproduct_cokernels {C : Type*} [Category C] [Abelian C]
    [HasFiniteBiproducts C] {Z Q P N : C} (k : ℕ) (f₀ : Z ⟶ Z) (hf₀ : f₀ = k • 𝟙 Z)
    (π : Z ⟶ Q) (hπ : f₀ ≫ π = 0) (h : IsColimit (CokernelCofork.ofπ π hπ)) (d : ℕ)
    (β : (⨁ fun _ : Fin d ↦ Q) ⟶ P) [Epi β] (φ : P ⟶ N)
    (Ψ : (⨁ fun _ : Fin d ↦ Z) ⟶ N) (hΨ : (k • 𝟙 (⨁ fun _ : Fin d ↦ Z)) ≫ Ψ = 0)
    (hΨc : IsColimit (CokernelCofork.ofπ Ψ hΨ))
    (hc : biproduct.map (fun _ ↦ π) ≫ β ≫ φ = Ψ) : IsIso φ := by
  subst hf₀
  let hb := biproductCokernelNsmul k π hπ h d
  have he : β ≫ φ = (IsColimit.coconePointUniqueUpToIso hb hΨc).hom := by
    apply Cofork.IsColimit.hom_ext hb
    have := IsColimit.comp_coconePointUniqueUpToIso_hom hb hΨc WalkingParallelPair.one
    rw [Cofork.π_ofπ, hc]
    simpa using this.symm
  have : IsIso (β ≫ φ) := by
    rw [he]
    infer_instance
  have : Mono β := mono_of_mono β φ
  have : IsIso β := isIso_of_mono_of_epi β
  exact IsIso.of_isIso_comp_left β φ

/-- Multiplication by a compatible family of ring sections, as an endomorphism of the
underlying abelian sheaf of a sheaf of modules. -/
def sectionSmul {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] (s : ∀ U, R.obj.obj U)
    (hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), R.obj.map f (s U) = s V) (M : SheafOfModules.{u + 1} R) :
    (SheafOfModules.toSheaf R).obj M ⟶ (SheafOfModules.toSheaf R).obj M :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (M.val.obj U) (s U))
     naturality := fun U V f ↦ by
       ext x
       exact ((M.val.map_smul f (s U) x).trans (congrArg (· • _) (hs f))).symm }⟩

theorem sectionSmul_naturality {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] (s : ∀ U, R.obj.obj U)
    (hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), R.obj.map f (s U) = s V)
    {M M' : SheafOfModules.{u + 1} R} (φ : M ⟶ M') :
    sectionSmul s hs M ≫ (SheafOfModules.toSheaf R).map φ =
      (SheafOfModules.toSheaf R).map φ ≫ sectionSmul s hs M' := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact (φ.val.app U).hom.map_smul (s U) x

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The constant section of an element of the finite coefficient ring. -/
def constSection (T : Scheme.{u}) (n : ℕ) (b : SpTowerShriek.R l E n) (U : T.ProEtᵒᵖ) :
    (WeilConjectures.SemilinearSections.ring (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T n)).obj.obj U :=
  (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))))).app U (ULift.up b)

theorem constSection_map (T : Scheme.{u}) (n : ℕ) (b : SpTowerShriek.R l E n)
    {U V : T.ProEtᵒᵖ} (f : U ⟶ V) :
    (WeilConjectures.SemilinearSections.ring (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T n)).obj.map f
      (constSection l E T n b U) = constSection l E T n b V :=
  (ConcreteCategory.congr_hom ((toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))))).naturality f) (ULift.up b)).symm

/-- Finite biproducts of abelian sheaves, through the shared abelian structure. -/
instance diagonalAbFiniteBiproducts (T : Scheme.{u}) : HasFiniteBiproducts (DiagonalAb T) :=
  Abelian.hasFiniteBiproducts

/-- Multiplication by the constant section of `b` on the level-`n` evaluation of a system. -/
abbrev levelSmul (T : Scheme.{u}) (n : ℕ) (b : SpTowerShriek.R l E n)
    (Y : Systems T (Arings l E T)) :=
  sectionSmul (constSection l E T n b) (constSection_map l E T n b)
    ((SpTowerShriek.ev l E T n).obj Y)

/-- A surjective additive map whose kernel consists of the `m`-multiples is a cokernel
of multiplication by `m`. -/
theorem addCommGrp_cokernel_of_surjective {A B : Type v} [AddCommGroup A] [AddCommGroup B]
    (m : ℕ) (f : A →+ B) (hf : Function.Surjective f) (hm : ∀ y, f (m • y) = 0)
    (hk : ∀ x, f x = 0 → ∃ y, m • y = x) :
    ∃ hz : (m • 𝟙 (AddCommGrpCat.of A)) ≫ AddCommGrpCat.ofHom f = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ hz)) := by
  have hz : (m • 𝟙 (AddCommGrpCat.of A)) ≫ AddCommGrpCat.ofHom f = 0 := by
    ext y
    simpa using hm y
  let S := ShortComplex.mk _ _ hz
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hk x hx
    exact ⟨y, by simp [S]⟩
  have : Epi S.g := (AddCommGrpCat.epi_iff_surjective _).2 hf
  exact ⟨hz, ⟨hS.gIsCokernel⟩⟩


/-- The integral basis combination `k ↦ Σ kᵢ eᵢ` of the finite coefficient ring. -/
def basisCombination (n d : ℕ)
    (e : letI := coefficientZModAlgebra l E n
      Module.Basis (Fin d) (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n)) :
    (Fin d → ULift.{u + 1} ℤ) →+ ULift.{u + 1} (SpTowerShriek.R l E n) where
  toFun k := ULift.up (∑ i, (k i).down • e i)
  map_zero' := by simp; rfl
  map_add' x y := by
    apply ULift.ext
    simp [add_smul, Finset.sum_add_distrib]

/-- The basis combination is a cokernel of multiplication by `l ^ (n + 1)`: it is onto, and
a combination vanishes exactly when every coefficient is divisible by `l ^ (n + 1)`. This
is the algebraic input of `supportedQuotient_level_cokernel`. -/
theorem basisCombination_cokernel (n d : ℕ)
    (e : letI := coefficientZModAlgebra l E n
      Module.Basis (Fin d) (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n)) :
    ∃ hz : (l ^ (n + 1) • 𝟙 (AddCommGrpCat.of (Fin d → ULift.{u + 1} ℤ))) ≫
        AddCommGrpCat.ofHom (basisCombination l E n d e) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ hz)) := by
  let := coefficientZModAlgebra l E n
  have hzs (z : ℤ) (x : SpTowerShriek.R l E n) : z • x = (z : ZMod (l ^ (n + 1))) • x :=
    (Int.cast_smul_eq_zsmul _ z x).symm
  apply addCommGrp_cokernel_of_surjective
  · intro r
    refine ⟨fun i ↦ ULift.up ((e.repr r.down i).val : ℤ), ?_⟩
    apply ULift.ext
    change ∑ i, ((e.repr r.down i).val : ℤ) • e i = r.down
    simp_rw [hzs, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact e.sum_repr r.down
  · intro y
    apply ULift.ext
    change ∑ i, ((l ^ (n + 1) • y i).down) • e i = 0
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [hzs]
    have : (((l ^ (n + 1) • y i).down : ℤ) : ZMod (l ^ (n + 1))) = 0 := by
      change (((l ^ (n + 1) • (y i).down : ℤ)) : ZMod (l ^ (n + 1))) = 0
      rw [nsmul_eq_mul]
      push_cast
      rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]
    rw [this, zero_smul]
  · intro x hx
    have hx' : ∑ i, (((x i).down : ℤ) : ZMod (l ^ (n + 1))) • e i = 0 := by
      simp_rw [← hzs]
      exact congrArg ULift.down hx
    have h0 := Fintype.linearIndependent_iff.1 e.linearIndependent _ hx'
    choose c hc using fun i ↦
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x i).down (l ^ (n + 1))).1 (h0 i)
    refine ⟨fun i ↦ ULift.up (c i), funext fun i ↦ ULift.ext _ _ ?_⟩
    change l ^ (n + 1) • c i = (x i).down
    rw [hc i, nsmul_eq_mul]


end AlgebraicGeometry.ProEtale.SpTowerClasses
