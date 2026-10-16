/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.Paper.ContinuousConstructibleIntegralGluing
import Sheaf.Paper.ContinuousLisseStratifiedLattices
import Mathlib.Algebra.Field.ULift

/-! # Integral models on a locally finitely presented stratum

Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-continuous-constructible-integral-stratum)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma constructible_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj T] (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (h : ProEtale.IsConstructibleModuleObject T M) :
    ProEtale.IsConstructibleModuleObject R ((Mod.comap φ).obj M) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun a ↦ ?_⟩
  let G := ProEtale.upperStar Ab.{u + 1} (S.immersion a)
  obtain ⟨C, hC⟩ := ProEtale.lfp_comap (G.map φ) (hS a)
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨n, m, f, ⟨e⟩⟩ := hC i
  exact ⟨n, m, f, ⟨(((ProEtale.upperStar Ab.{u + 1} (C.f i)).mapMod _).mapIso
    ((G.mapModComapIso φ).app M)) ≪≫ e⟩⟩

private noncomputable def scalarTransportIso {X : Scheme.{u}}
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj R'] [MonObj S']
    [IsCommMonObj R] [IsCommMonObj R']
    (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
    (a : R ⟶ R') [IsMonHom a] [IsIso a]
    (b : S ⟶ S') [IsMonHom b] [IsIso b]
    (w : a ≫ ψ = φ ≫ b) :
    Mod.comap a ⋙ Mod.extendScalars φ ≅ Mod.extendScalars ψ ⋙ Mod.comap b := by
  let ea : Mod _ R' ≌ Mod _ R :=
    CategoryTheory.Equivalence.mk (Mod.comap a) (Mod.comap (inv a))
      ((Mod.comapId R').symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv a) a)
      ((Mod.comapComp a (inv a)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId R)
  let eb : Mod _ S' ≌ Mod _ S :=
    CategoryTheory.Equivalence.mk (Mod.comap b) (Mod.comap (inv b))
      ((Mod.comapId S').symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv b) b)
      ((Mod.comapComp b (inv b)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId S)
  let t : Mod.comap φ ⋙ Mod.comap (inv a) ≅ Mod.comap (inv b) ⋙ Mod.comap ψ :=
    (Mod.comapComp (inv a) φ).symm ≪≫ Mod.comapCongr (by
      rw [← cancel_epi a, IsIso.hom_inv_id_assoc, ← Category.assoc, w,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id]) ≪≫ Mod.comapComp ψ (inv b)
  exact (ea.toAdjunction.comp (Mod.extendRestrictAdjunction φ)).leftAdjointUniq
    ((Mod.extendRestrictAdjunction ψ).comp eb.toAdjunction |>.ofNatIsoRight t.symm)

private lemma model_transport {X : Scheme.{u}}
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj R'] [MonObj S']
    [IsCommMonObj R] [IsCommMonObj R']
    (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
    (a : R ⟶ R') [IsMonHom a] [IsIso a]
    (b : S ⟶ S') [IsMonHom b] [IsIso b]
    (w : a ≫ ψ = φ ≫ b)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R')
    (hM : ProEtale.IsConstructibleModuleObject R' M)
    (e : (Mod.extendScalars ψ).obj M ≅ (Mod.comap (inv b)).obj F) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R,
      ProEtale.IsConstructibleModuleObject R N ∧
      Nonempty ((Mod.extendScalars φ).obj N ≅ F) := by
  refine ⟨(Mod.comap a).obj M, constructible_comap a hM, ⟨?_⟩⟩
  exact (scalarTransportIso φ ψ a b w).app M ≪≫ (Mod.comap b).mapIso e ≪≫
    ((Mod.comapComp b (inv b)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId S).app F

private noncomputable def liftCoefficientIso (E : Type) [NormedField E] :
    Profinite.continuousMapRingSheaf.{u} E ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} E) where
  hom := ⟨
    { app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ULift.ringEquiv (R := E)).symm.toRingHom.compLeftContinuous S.unop
            continuous_uliftUp).comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }⟩
  inv := ⟨
    { app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ULift.ringEquiv (R := E)).toRingHom.compLeftContinuous S.unop
            continuous_uliftDown).comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }⟩
  hom_inv_id := by ext S f; rfl
  inv_hom_id := by ext S f; rfl

private lemma smallField_finiteFree_cover
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : ProEtale.IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Mod.IsFree
        ((ProEtale.upperStar Ab.{u + 1} (C.f i)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f i)).mapMod
          (condensedRingObj (Profinite.continuousMapRingObj E) X)).obj P) := by
  let : NormedField (ULift.{u} E) :=
    { (inferInstance : Field (ULift.{u} E)), (inferInstance : NormedCommRing (ULift.{u} E)) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map _ (liftCoefficientIso E).hom
  let φ := (upperStarFromPoint X).map e.hom
  have : IsMonHom φ := inferInstance
  let Q := (Mod.comap (inv φ)).obj P
  have hQ := ProEtale.lfp_comap (inv φ) hP
  obtain ⟨C, hC⟩ := ProEtale.exists_finiteFree_cover_of_condensedField_lfp ℓ
    (ULift.{u} E) X Q hQ
  refine ⟨C, fun i ↦ ?_⟩
  let G := ProEtale.upperStar Ab.{u + 1} (C.f i)
  have h := ProEtale.free_comap (G.map φ) (hC i)
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, ⟨?_ ≪≫ e⟩⟩
  exact (G.mapMod _).mapIso
    (((Mod.comapComp φ (inv φ)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId _).app P).symm ≪≫
      (G.mapModComapIso φ).app Q

private structure PullbackCoefficientData
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (i : Y ⟶ X) where
  integral : (ProEtale.upperStar Ab.{u + 1} i).obj
      (condensedRingObj (integralCoeff ℓ E) X) ⟶ condensedRingObj (integralCoeff ℓ E) Y
  rational : (ProEtale.upperStar Ab.{u + 1} i).obj
      (condensedRingObj (Profinite.continuousMapRingObj E) X) ⟶
        condensedRingObj (Profinite.continuousMapRingObj E) Y
  integralMon : IsMonHom integral
  rationalMon : IsMonHom rational
  integralIso : IsIso integral
  rationalIso : IsIso rational
  square : integral ≫ coefficientMap (integralScalarMap ℓ E) Y =
    (ProEtale.upperStar Ab.{u + 1} i).map (coefficientMap (integralScalarMap ℓ E) X) ≫
      rational
  pullback : letI := rationalMon
    letI := rationalIso
    CondensedRing.upperStar (Profinite.continuousMapRingObj E) i ≅
    (ProEtale.upperStar Ab.{u + 1} i).mapMod _ ⋙ Mod.comap (inv rational)

private noncomputable def pullbackCoefficientData
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (i : Y ⟶ X) : PullbackCoefficientData ℓ E i where
  integral := condensedPullbackHom (integralCoeff ℓ E) i
  rational := condensedPullbackHom (Profinite.continuousMapRingObj E) i
  integralMon := ProEtale.isMonHom_condensedPullbackHom _ _
  rationalMon := ProEtale.isMonHom_condensedPullbackHom _ _
  integralIso := ProEtale.isIso_condensedPullbackHom _ _
  rationalIso := ProEtale.isIso_condensedPullbackHom _ _
  square := (map_coefficientMap_comp_condensedPullbackHom (integralScalarMap ℓ E) i).symm
  pullback := Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv _)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- A locally finitely presented rational module on one immersed stratum admits an
ordinary constructible integral model, with both coefficient rings pulled back from X.
Source: Hemo--Richarz--Scholbach, Example 3.1 (local triviality), and Bhatt--Scholze,
Lemma 6.8.13, with the coefficient restriction identification of Lemma 6.8.2.
(blueprint: lem-weil-pbc-continuous-constructible-integral-stratum)

Proof in words. An immersion identifies Y with a locally closed subspace of X, so Y
is topologically noetherian. Identify the two pulled-back coefficient rings and their
map with the continuous integral and rational coefficient rings on Y. A finite local
presentation over the rational ring is locally finite free: realize a presentation
matrix as continuous E-valued functions, refine by its locally constant rank, and use
an invertible maximal minor to identify its cokernel with a finite free module.
For this lisse module, the first paragraph of Lemma 6.8.13 gives lattices on a finite
refinement. More explicitly, Proposition 6.8.4(6) first gives lattices on an etale cover.
Take a finite affine subcover and stratify so its maps become finite etale. Etale
locally split each finite etale cover into sheets. View the finitely many supplied
lattices in the same rational module and take their sum; it is a finite free full
lattice over the valuation ring. The sum is invariant under permutations of the
sheets, and continuous transition maps preserve its locally constant lattice class,
so it descends. The resulting lisse integral module is locally finitely presented,
and the singleton identity stratification makes it constructible.
Apply the separate gluing theorem to these supplied models on the finite refinement,
and transport the result back across the coefficient identifications. For the zero
module and the empty stratum use zero. No derived comparison or bounded-complex
packaging is part of this statement. -/
theorem continuousConstructible_integral_stratum (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] {Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i]
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((ProEtale.upperStar Ab.{u + 1} i).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hF : ProEtale.IsLocallyFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} i).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) F) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)),
      ProEtale.IsConstructibleModuleObject
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)) N ∧
      Nonempty ((Mod.extendScalars
        ((ProEtale.upperStar Ab.{u + 1} i).map
          (coefficientMap (integralScalarMap ℓ E) X))).obj N ≅ F) := by
  let : TopologicalSpace.NoetherianSpace Y := i.isEmbedding.isInducing.noetherianSpace
  obtain ⟨D⟩ : Nonempty (PullbackCoefficientData ℓ E i) :=
    ⟨pullbackCoefficientData ℓ E i⟩
  obtain ⟨ai, bi, hai, hbi, iai, ibi, wi, _⟩ := D
  let : IsMonHom ai := hai
  let : IsMonHom bi := hbi
  let : IsIso ai := iai
  let : IsIso bi := ibi
  obtain ⟨P, hP, ⟨eP⟩⟩ : ∃ P : Mod _
      (condensedRingObj (Profinite.continuousMapRingObj E) Y),
      ProEtale.IsLocallyFinitelyPresented _ P ∧
        Nonempty (P ≅ (Mod.comap (inv bi)).obj F) :=
    ⟨(Mod.comap (inv bi)).obj F, ProEtale.lfp_comap (inv bi) hF, ⟨Iso.refl _⟩⟩
  obtain ⟨C, hC⟩ := smallField_finiteFree_cover ℓ E Y P hP
  obtain ⟨S, hS⟩ := continuousLisse_stratified_lattices ℓ E Y P ⟨C, hC⟩
  have hmodels : ∀ s : Fin S.n,
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).obj
            (condensedRingObj (integralCoeff ℓ E) Y)),
        ProEtale.IsConstructibleModuleObject
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).obj
            (condensedRingObj (integralCoeff ℓ E) Y)) M ∧
        Nonempty ((Mod.extendScalars
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).map
            (coefficientMap (integralScalarMap ℓ E) Y))).obj M ≅
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).mapMod _).obj P) := fun s ↦ by
    obtain ⟨M, hM, ⟨e⟩⟩ := hS s
    let j := S.immersion s
    obtain ⟨D⟩ : Nonempty (PullbackCoefficientData ℓ E j) :=
      ⟨pullbackCoefficientData ℓ E j⟩
    obtain ⟨a, b, ha, hb, ia, ib, w, t⟩ := D
    let : IsMonHom a := ha
    let : IsMonHom b := hb
    let : IsIso a := ia
    let : IsIso b := ib
    let G := ProEtale.upperStar Ab.{u + 1} j
    exact model_transport (G.map (coefficientMap (integralScalarMap ℓ E) Y))
      (coefficientMap (integralScalarMap ℓ E) (S.domain s))
      a b w
      ((G.mapMod _).obj P) M hM
      (e ≪≫ t.app P)
  obtain ⟨N, hN, ⟨e⟩⟩ := continuousConstructible_integral_gluing ℓ E Y P S hmodels
  exact model_transport
    ((ProEtale.upperStar Ab.{u + 1} i).map (coefficientMap (integralScalarMap ℓ E) X))
    (coefficientMap (integralScalarMap ℓ E) Y)
    ai bi wi F N hN (e ≪≫ eP)

end AlgebraicGeometry.ProEtale.CondensedRing
