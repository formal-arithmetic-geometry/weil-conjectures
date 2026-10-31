/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.LineProjFractionChartData
import WeilConjectures.TraceFormula.LineProjGenerationLocus
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Coefficient ring map of a homogeneous generating section -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem lineProj_component_injective {T : Scheme.{u}} (A : RelativeProjAlgebra T)
    (V : T.Opens) (n : ℕ) :
    Function.Injective ((Sigma.ι A.piece n ≫ A.decomposition.hom).app V) := by
  classical
  let π : (∐ A.piece) ⟶ A.piece n :=
    Sigma.desc (fun k ↦ if h : k = n then eqToHom (congrArg A.piece h) else 0)
  have hπ : Sigma.ι A.piece n ≫ A.decomposition.hom ≫
      A.decomposition.inv ≫ π = 𝟙 _ := by
    simp only [Iso.hom_inv_id_assoc, π, Sigma.ι_desc, eqToHom_refl, dite_true]
  intro a b hab
  have h := congrArg ((A.decomposition.inv ≫ π).app V) hab
  simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app,
    Category.assoc, hπ, Hom.id_app, ConcreteCategory.id_apply] using h

private noncomputable def lineProj_component_equiv {T : Scheme.{u}}
    (A : RelativeProjAlgebra T) (V : T.affineOpens) (n : ℕ) :
    Γ(A.piece n, V.1) ≃ₗ[Γ(T, V.1)] A.grade V n :=
  LinearEquiv.ofInjective ((Sigma.ι A.piece n ≫ A.decomposition.hom).val.app (op V.1)).hom
    (lineProj_component_injective A V.1 n)

private theorem lineProj_component_equiv_element {T : Scheme.{u}}
    (A : RelativeProjAlgebra T) (V : T.affineOpens) (n : ℕ)
    (a : Γ(A.piece n, V.1)) :
    lineProj_component_equiv A V n a = lineProjElement A V n a := rfl

/-- The image section is a free generator on its generator open.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_chart_generator {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1)) :
    IsFreeGenerator ((L.tensorPow d).presheaf.map (homOfLE
      (inf_le_left : lineProjGeneratorOpen f A L ψ V d a ≤ f ⁻¹ᵁ V.1)).op
        (lineProjImage f A L ψ V.1 d a)) := by
  apply lineProj_open_generator
  intro x hx
  exact (lineProj_mem_generator_open _ _ _ x).mp hx

/-- Tensor powers of a frame are free generators.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_frame_generator {X : Scheme.{u}} (L : X.Modules)
    (U : X.Opens) (e : Γ(L, U)) (he : IsFreeGenerator e) (n : ℕ) :
    IsFreeGenerator (lineProjFramePower L U e n) := by
  induction n with
  | zero => exact isFreeGenerator_one U
  | succ n ih => exact he.tmulSection ih

/-- Powers of a homogeneous generator are free generators.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_power_generator {X : Scheme.{u}} (L : X.Modules)
    (U : X.Opens) (d : ℕ) (s : Γ(L.tensorPow d, U)) (hs : IsFreeGenerator s) (m : ℕ) :
    IsFreeGenerator (lineProjPower L U d s m) := by
  apply IsFreeGenerator.app_hom
    (eqToIso (congrArg L.tensorPow (Nat.mul_comm d m)))
  exact (lineProj_frame_generator _ _ _ hs m).app_hom (L.tensorPowMulIso d m).symm

/-- Frame powers commute with restriction of sections.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_frame_restrict {X : Scheme.{u}} (L : X.Modules)
    {U C : X.Opens} (h : C ≤ U) (e : Γ(L, U)) (n : ℕ) :
    (L.tensorPow n).presheaf.map (homOfLE h).op (lineProjFramePower L U e n) =
      lineProjFramePower L C (L.presheaf.map (homOfLE h).op e) n := by
  induction n with
  | zero =>
    change _ = unitSectionsEquiv C 1
    exact (presheaf_map_unitSectionsEquiv _ _).trans (by rw [map_one])
  | succ n ih =>
    change (L ⊗ L.tensorPow n).presheaf.map (homOfLE h).op
      (tmulSection e (lineProjFramePower L U e n)) = _
    rw [tmulSection_map, ih]
    rfl

/-- Homogeneous powers commute with restriction of sections.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_power_restrict {X : Scheme.{u}} (L : X.Modules)
    {U C : X.Opens} (h : C ≤ U) (d : ℕ) (s : Γ(L.tensorPow d, U)) (m : ℕ) :
    (L.tensorPow (m • d)).presheaf.map (homOfLE h).op (lineProjPower L U d s m) =
      lineProjPower L C d ((L.tensorPow d).presheaf.map (homOfLE h).op s) m := by
  unfold lineProjPower
  exact (Hom.app_presheaf_map (eqToHom
    (congrArg L.tensorPow (Nat.mul_comm d m))) (homOfLE h) _).symm.trans
      ((congrArg ((eqToHom (congrArg L.tensorPow (Nat.mul_comm d m))).app C)
        (Hom.app_presheaf_map (L.tensorPowMulIso d m).inv (homOfLE h) _).symm).trans
          (congrArg (fun z ↦ (eqToHom
            (congrArg L.tensorPow (Nat.mul_comm d m))).app C
              ((L.tensorPowMulIso d m).inv.app C z))
            (lineProj_frame_restrict _ h _ m)))

private theorem lineProj_frame_transport {X : Scheme.{u}} (L : X.Modules)
    (U : X.Opens) (e : Γ(L, U)) {m n : ℕ} (h : m = n) :
    (eqToHom (congrArg L.tensorPow h)).app U (lineProjFramePower L U e m) =
      lineProjFramePower L U e n := by
  subst n
  rfl

private theorem lineProj_frame_mul {X : Scheme.{u}} (L : X.Modules)
    (U : X.Opens) (e : Γ(L, U)) (i j : ℕ) :
    (L.tensorPowAddIso i j).inv.app U
      (tmulSection (lineProjFramePower L U e i) (lineProjFramePower L U e j)) =
        lineProjFramePower L U e (i + j) := by
  induction i with
  | zero =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Hom.comp_app,
      ConcreteCategory.comp_apply]
    exact (congrArg _ ((leftUnitor_hom_app_tmulSection 1 _).trans (one_smul _ _))).trans
      (lineProj_frame_transport L U e (Nat.zero_add j).symm)
  | succ i ih =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    change (eqToHom (congrArg L.tensorPow (Nat.succ_add i j).symm)).app U
      ((Iso.refl L ⊗ᵢ L.tensorPowAddIso i j).inv.app U
      ((α_ L (L.tensorPow i) (L.tensorPow j)).hom.app U
        (tmulSection (tmulSection e (lineProjFramePower L U e i))
          (lineProjFramePower L U e j)))) = _
    rw [associator_hom_app_tmulSection]
    have h : (Iso.refl L ⊗ᵢ L.tensorPowAddIso i j).inv.app U
        (tmulSection e (tmulSection (lineProjFramePower L U e i)
          (lineProjFramePower L U e j))) = tmulSection e (lineProjFramePower L U e (i + j)) := by
      rw [tensorIso_inv, Iso.refl_inv, tensorHom_app_tmulSection, ih, Hom.id_app]
      rfl
    rw [h]
    exact lineProj_frame_transport L U e (Nat.succ_add i j).symm

private theorem lineProj_frame_smul {X : Scheme.{u}} (L : X.Modules)
    (U : X.Opens) (e : Γ(L, U)) (c : Γ(X, U)) (n : ℕ) :
    lineProjFramePower L U (c • e) n = c ^ n • lineProjFramePower L U e n := by
  induction n with
  | zero => simp only [lineProjFramePower, pow_zero, one_smul]
  | succ n ih =>
    change tmulSection (c • e) (lineProjFramePower L U (c • e) n) = _
    rw [ih, smul_tmulSection, tmulSection_smul, smul_smul, ← pow_succ']
    rfl

/-- Powers of a frame power agree with the total frame power.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_power_frame {X : Scheme.{u}} (L : X.Modules)
    (U : X.Opens) (e : Γ(L, U)) (d m : ℕ) :
    lineProjPower L U d (lineProjFramePower L U e d) m =
      lineProjFramePower L U e (m • d) := by
  have h (n : ℕ) : (L.tensorPowMulIso d n).inv.app U
      (lineProjFramePower (L.tensorPow d) U (lineProjFramePower L U e d) n) =
        lineProjFramePower L U e (d * n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [tensorPowMulIso, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
        Hom.comp_app, ConcreteCategory.comp_apply, eqToIso.inv]
      change (eqToHom (congrArg L.tensorPow
        (show d + d * n = d * (n + 1) by ring))).app U
        ((L.tensorPowAddIso d (d * n)).inv.app U
        ((𝟙 (L.tensorPow d) ⊗ₘ (L.tensorPowMulIso d n).inv).app U
          (tmulSection (lineProjFramePower L U e d)
            (lineProjFramePower (L.tensorPow d) U (lineProjFramePower L U e d) n)))) = _
      rw [tensorHom_app_tmulSection, Hom.id_app, ConcreteCategory.id_apply, ih,
        lineProj_frame_mul]
      exact lineProj_frame_transport L U e (by ring)
  unfold lineProjPower
  rw [h]
  exact lineProj_frame_transport L U e (Nat.mul_comm d m)

/-- Scaling a homogeneous section scales its m-th power by the m-th scalar power.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_power_smul {X : Scheme.{u}} (L : X.Modules)
    (U : X.Opens) (d : ℕ) (s : Γ(L.tensorPow d, U)) (c : Γ(X, U)) (m : ℕ) :
    lineProjPower L U d (c • s) m = c ^ m • lineProjPower L U d s m := by
  unfold lineProjPower
  rw [lineProj_frame_smul, Hom.app_smul, Hom.app_smul]

set_option backward.isDefEq.respectTransparency false in
/-- A local frame turns the homogeneous images into an ordinary ring homomorphism.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_local_coefficient_hom {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (V : T.affineOpens) (B : W.Opens) (hB : B ≤ f ⁻¹ᵁ V.1)
    (e : Γ(L, B)) (he : IsFreeGenerator e) :
    ∃ φ : A.sections V →+* Γ(W, B), ∀ (n : ℕ) (b : Γ(A.piece n, V.1)),
      φ (lineProjElement A V n b).val • lineProjFramePower L B e n =
        (L.tensorPow n).presheaf.map (homOfLE hB).op
          (lineProjImage f A L ψ V.1 n b) := by
  classical
  let E (n : ℕ) := lineProj_component_equiv A V n
  let F (n : ℕ) : Γ(A.piece n, V.1) →+ Γ(L.tensorPow n, B) :=
    (((L.tensorPow n).presheaf.map (homOfLE hB).op).hom.comp
      ((ψ n).app (f ⁻¹ᵁ V.1)).hom).comp
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
          (A.piece n)).app V.1).hom
  have hF (n : ℕ) (b : Γ(A.piece n, V.1)) : F n b =
      (L.tensorPow n).presheaf.map (homOfLE hB).op
        (lineProjImage f A L ψ V.1 n b) := by
    dsimp only [F, AddMonoidHom.comp_apply, lineProjImage]
    exact congrArg (fun z ↦ (L.tensorPow n).presheaf.map (homOfLE hB).op
      ((ψ n).app (f ⁻¹ᵁ V.1) z))
        (Classical.choose_spec (exists_tensorPullbackAdjunction f) (A.piece n) (op V.1) b)
  let c (n : ℕ) : A.grade V n →+ Γ(W, B) :=
    { toFun b := (lineProj_frame_generator L B e he n).coeff (F n ((E n).symm b))
      map_zero' := by rw [map_zero, map_zero, IsFreeGenerator.coeff_zero]
      map_add' b b' := by rw [map_add, map_add, IsFreeGenerator.coeff_add] }
  have hc (n : ℕ) (b : Γ(A.piece n, V.1)) :
      c n (lineProjElement A V n b) • lineProjFramePower L B e n = F n b := by
    change (lineProj_frame_generator L B e he n).coeff
      (F n ((E n).symm (E n b))) • _ = _
    rw [LinearEquiv.symm_apply_apply, IsFreeGenerator.coeff_smul]
  have h1 : c 0 ((1 : GradedMonoid (fun n ↦ A.grade V n)).snd) = 1 := by
    let b : Γ(A.piece 0, V.1) := A.graded.unit.val.app (op V.1) (unitSectionsEquiv V.1 1)
    have hb : lineProjElement A V 0 b = (1 : GradedMonoid (fun n ↦ A.grade V n)).snd := by
      apply Subtype.ext
      change (Sigma.ι A.piece 0 ≫ A.decomposition.hom).val.app (op V.1)
        (A.graded.unit.val.app (op V.1) (1 : Γ(T, V.1))) = (1 : A.sections V)
      exact (A.unit_eq V.1 1).trans (map_one (A.algebra.obj.hom.hom.app (op V.1)).hom)
    apply (lineProj_frame_generator L B e he 0).smul_left_injective
    change c 0 _ • lineProjFramePower L B e 0 = _
    rw [← hb, hc, hF, hunit]
    change (𝟙_ W.Modules).presheaf.map (homOfLE hB).op
      (unitSectionsEquiv (f ⁻¹ᵁ V.1) (f.app V.1 1)) =
        1 • unitSectionsEquiv B 1
    rw [presheaf_map_unitSectionsEquiv, map_one, map_one, one_smul]
  have hmul' {m n : ℕ} (b : A.grade V m) (b' : A.grade V n) :
      c (m + n) (GradedMonoid.GMul.mul (A := fun n ↦ A.grade V n) b b') = c m b * c n b' := by
    obtain ⟨b, rfl⟩ := (E m).surjective b
    obtain ⟨b', rfl⟩ := (E n).surjective b'
    have hh : GradedMonoid.GMul.mul (A := fun n ↦ A.grade V n) (E m b) (E n b') =
        lineProjElement A V (m + n) (A.graded.mul m n V.1 b b') := by
      apply Subtype.ext
      exact (A.mul_eq V.1 m n b b').symm
    apply (lineProj_frame_generator L B e he (m + n)).smul_left_injective
    change c (m + n) _ • lineProjFramePower L B e (m + n) = _
    rw [hh, hc, hF, hmul]
    rw [← Hom.app_presheaf_map, tmulSection_map, ← hF, ← hF, ← hc, ← hc,
      smul_tmulSection, tmulSection_smul, Hom.app_smul, Hom.app_smul,
      smul_smul, lineProj_frame_mul]
    rfl
  let Φ := DirectSum.liftRingHom
    ⟨fun {n} ↦ c n, h1, fun {m n} b b' ↦ hmul' b b'⟩
  let φ := Φ.comp (DirectSum.decomposeRingEquiv (A.grade V)).toRingHom
  refine ⟨φ, ?_⟩
  intro n b
  change Φ (DirectSum.decompose (A.grade V) (lineProjElement A V n b).val) • _ = _
  rw [DirectSum.decompose_coe]
  change DirectSum.toSemiring (fun n ↦ c n) h1 (fun {m n} b b' ↦ hmul' b b')
    (DirectSum.of _ n (lineProjElement A V n b)) • _ = _
  rw [DirectSum.toSemiring_of, hc, hF]

private theorem lineProj_local_fraction_hom {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (B : W.Opens) (hB : B ≤ lineProjGeneratorOpen f A L ψ V d a)
    (e : Γ(L, B)) (he : IsFreeGenerator e) :
    ∃ ρ : HomogeneousLocalization.Away (A.grade V) (lineProjElement A V d a).val →+*
        Γ(W, B), ∀ (m : ℕ) (b : Γ(A.piece (m • d), V.1)),
      ρ (HomogeneousLocalization.Away.mk (A.grade V)
        (lineProjElement A V d a).property m
        (lineProjElement A V (m • d) b).val
        (lineProjElement A V (m • d) b).property) •
        lineProjPower L B d ((L.tensorPow d).presheaf.map
          (homOfLE (hB.trans inf_le_left)).op (lineProjImage f A L ψ V.1 d a)) m =
        (L.tensorPow (m • d)).presheaf.map (homOfLE (hB.trans inf_le_left)).op
          (lineProjImage f A L ψ V.1 (m • d) b) := by
  classical
  obtain ⟨φ, hφ⟩ := lineProj_local_coefficient_hom f A L ψ hunit hmul
    V B (hB.trans inf_le_left) e he
  let ca := φ (lineProjElement A V d a).val
  have hca := hφ d a
  have hs : IsFreeGenerator (ca • lineProjFramePower L B e d) := by
    rw [hca]
    simpa only [presheaf_map_homOfLE_map_homOfLE] using
      (lineProj_chart_generator f A L ψ V d a).map hB
  obtain ⟨u, hu⟩ := (lineProj_frame_generator L B e he d).exists_unit_smul_eq hs
  have hcu : ca = u.val :=
    (lineProj_frame_generator L B e he d).smul_left_injective hu
  have hunitca : IsUnit ca := hcu ▸ u.isUnit
  let F := Localization.awayLift φ (lineProjElement A V d a).val hunitca
  let ρ := F.comp (algebraMap (HomogeneousLocalization.Away (A.grade V)
    (lineProjElement A V d a).val) (Localization.Away (lineProjElement A V d a).val))
  refine ⟨ρ, ?_⟩
  intro m b
  let z := HomogeneousLocalization.Away.mk (A.grade V)
    (lineProjElement A V d a).property m
    (lineProjElement A V (m • d) b).val (lineProjElement A V (m • d) b).property
  have hcoeff : ρ z * ca ^ m = φ (lineProjElement A V (m • d) b).val := by
    have h := IsLocalization.mk'_spec (S := Localization.Away (lineProjElement A V d a).val)
      (lineProjElement A V (m • d) b).val
      (⟨(lineProjElement A V d a).val ^ m, m, rfl⟩ :
        Submonoid.powers (lineProjElement A V d a).val)
    have hh := congrArg F h
    simpa only [ρ, z, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', map_mul, map_pow,
      IsLocalization.Away.lift_eq, ca, F, Localization.awayLift] using hh
  rw [← hca, lineProj_power_smul, lineProj_power_frame, smul_smul, hcoeff]
  exact hφ (m • d) b

private theorem lineProj_frame_ext {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible]
    (G : X.Opens) {a b : Γ(X, G)}
    (h : ∀ (B : X.Opens) (hB : B ≤ G) (e : Γ(L, B)), IsFreeGenerator e →
      X.presheaf.map (homOfLE hB).op a = X.presheaf.map (homOfLE hB).op b) : a = b := by
  let S : Sieve G := ⟨fun B _ ↦ ∃ e : Γ(L, B), IsFreeGenerator e, by
    intro B C i hi j
    obtain ⟨e, he⟩ := hi
    exact ⟨_, he.map j.le⟩⟩
  apply X.ext_of_mem (S := S)
  · intro x hx
    have : SheafOfModules.IsInvertible.{u, u, u} L :=
      IsInvertible.sheafOfModules_isInvertible L
    obtain ⟨B, hxB, hBG, e, he⟩ := exists_isFreeGenerator L hx
    exact ⟨B.1, homOfLE hBG, ⟨e, he⟩, hxB⟩
  · intro B i hi
    obtain ⟨e, he⟩ := hi
    exact h B i.le e he

/-- Unique division by a homogeneous generating section defines a ring homomorphism.

Source: Stacks Project, Constructions, Tag 01NK, existence proof, localization and
passage to degree zero; Tag 01O9, affine-base construction.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom).

Proof: The image s of a is a free generator on its generator open G, and all powers
s^m are free generators, including the tensor unit for m=0. Locally choose a frame e of
L. Unique coefficients of psi(b) in e^n give additive maps in each degree; the unit and
multiplication laws combine them by the graded direct-sum universal property into a
ring map phi:A(V) to O(B). The coefficient phi(a) is a unit because psi(a) is a basis.
Extend phi to the ordinary localization at a and restrict to its degree-zero subring.
The localization equation gives rho(b/a^m) phi(a)^m=phi(b), hence the required tensor
fraction formula. To globalize, represent each homogeneous fraction b/a^m and take the
unique coefficient of psi(b) in s^m. On any local frame open it equals the just-built
local ring map by cancellation. Thus it is independent of the representative, and its
ring laws follow locally by the sheaf condition. The affine-spectrum adjunction produces
the chart; all fractions have homogeneous representatives, so basis cancellation proves
uniqueness on every smaller source open. Restriction and the tensor-power identities
give the frame formula. The free-generator ratio is a unit exactly on the coefficient's
basic open, which proves the stated generator-open identity. No reducedness, finite
generation, or affineness of G is used. -/
theorem exists_lineProj_fraction_coefficient_hom {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (V : T.affineOpens) (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)) :
    ∃ ρ : HomogeneousLocalization.Away (A.grade V) (lineProjElement A V d a).val →+*
        Γ(W, lineProjGeneratorOpen f A L ψ V d a),
      ∀ (m : ℕ) (b : Γ(A.piece (m • d), V.1)),
        ρ (HomogeneousLocalization.Away.mk (A.grade V)
          (lineProjElement A V d a).property m
          (lineProjElement A V (m • d) b).val
          (lineProjElement A V (m • d) b).property) •
          lineProjPower L (lineProjGeneratorOpen f A L ψ V d a) d
            ((L.tensorPow d).presheaf.map (homOfLE inf_le_left).op
              (lineProjImage f A L ψ V.1 d a)) m =
          (L.tensorPow (m • d)).presheaf.map (homOfLE inf_le_left).op
            (lineProjImage f A L ψ V.1 (m • d) b) := by
  classical
  let G := lineProjGeneratorOpen f A L ψ V d a
  have hG : G ≤ f ⁻¹ᵁ V.1 := inf_le_left
  let s : Γ(L.tensorPow d, G) := (L.tensorPow d).presheaf.map
    (homOfLE hG).op (lineProjImage f A L ψ V.1 d a)
  have hs : IsFreeGenerator s := lineProj_chart_generator f A L ψ V d a
  have hp (m : ℕ) : IsFreeGenerator (lineProjPower L G d s m) :=
    lineProj_power_generator L G d s hs m
  let R := HomogeneousLocalization.Away (A.grade V) (lineProjElement A V d a).val
  have hrep (z : R) : ∃ (m : ℕ) (b : Γ(A.piece (m • d), V.1)),
      HomogeneousLocalization.Away.mk (A.grade V) (lineProjElement A V d a).property
        m (lineProjElement A V (m • d) b).val
          (lineProjElement A V (m • d) b).property = z := by
    obtain ⟨m, b, hb, hz⟩ := HomogeneousLocalization.Away.mk_surjective
      (A.grade V) (lineProjElement A V d a).property z
    obtain ⟨b', hb'⟩ := (lineProj_component_equiv A V (m • d)).surjective ⟨b, hb⟩
    refine ⟨m, b', ?_⟩
    exact (congrArg (fun b ↦ HomogeneousLocalization.Away.mk (A.grade V)
      (lineProjElement A V d a).property m b.val b.property) hb').trans hz
  choose m b hmb using hrep
  let c (z : R) : Γ(W, G) := (hp (m z)).coeff
    ((L.tensorPow (m z • d)).presheaf.map (homOfLE hG).op
      (lineProjImage f A L ψ V.1 (m z • d) (b z)))
  have hc (z : R) : c z • lineProjPower L G d s (m z) =
      (L.tensorPow (m z • d)).presheaf.map (homOfLE hG).op
        (lineProjImage f A L ψ V.1 (m z • d) (b z)) := (hp (m z)).coeff_smul _
  have hloc' (B : W.Opens) (hB : B ≤ G) (ρ : R →+* Γ(W, B))
      (hρ : ∀ (k : ℕ) (t : Γ(A.piece (k • d), V.1)),
        ρ (HomogeneousLocalization.Away.mk (A.grade V)
          (lineProjElement A V d a).property k (lineProjElement A V (k • d) t).val
            (lineProjElement A V (k • d) t).property) •
          lineProjPower L B d ((L.tensorPow d).presheaf.map
            (homOfLE (hB.trans hG)).op (lineProjImage f A L ψ V.1 d a)) k =
          (L.tensorPow (k • d)).presheaf.map (homOfLE (hB.trans hG)).op
            (lineProjImage f A L ψ V.1 (k • d) t)) (z : R) :
      W.presheaf.map (homOfLE hB).op (c z) = ρ z := by
    apply ((lineProj_power_generator L G d s hs (m z)).map hB).smul_left_injective
    have hh := congrArg ((L.tensorPow (m z • d)).presheaf.map (homOfLE hB).op) (hc z)
    erw [map_smul, presheaf_map_homOfLE_map_homOfLE] at hh
    erw [lineProj_power_restrict] at hh ⊢
    have hρz := hρ (m z) (b z)
    rw [hmb z] at hρz
    have hsr := presheaf_map_homOfLE_map_homOfLE hG hB
      (lineProjImage f A L ψ V.1 d a)
    change (L.tensorPow d).presheaf.map (homOfLE hB).op s = _ at hsr
    rw [hsr] at hh ⊢
    exact hh.trans hρz.symm
  have hloc (B : W.Opens) (hB : B ≤ G) (e : Γ(L, B)) (he : IsFreeGenerator e) :
      ∃ ρ : R →+* Γ(W, B), ∀ z : R,
        W.presheaf.map (homOfLE hB).op (c z) = ρ z := by
    obtain ⟨ρ, hρ⟩ := lineProj_local_fraction_hom f A L ψ hunit hmul V d a B hB e he
    exact ⟨ρ, hloc' B hB ρ hρ⟩
  have hzero : c 0 = 0 := by
    apply lineProj_frame_ext L G
    intro B hB e he
    obtain ⟨ρ, hρ⟩ := hloc B hB e he
    rw [hρ, map_zero, map_zero]
  have hone : c 1 = 1 := by
    apply lineProj_frame_ext L G
    intro B hB e he
    obtain ⟨ρ, hρ⟩ := hloc B hB e he
    rw [hρ, map_one, map_one]
  have hadd (z z' : R) : c (z + z') = c z + c z' := by
    apply lineProj_frame_ext L G
    intro B hB e he
    obtain ⟨ρ, hρ⟩ := hloc B hB e he
    rw [hρ, map_add, map_add, hρ, hρ]
  have hmul' (z z' : R) : c (z * z') = c z * c z' := by
    apply lineProj_frame_ext L G
    intro B hB e he
    obtain ⟨ρ, hρ⟩ := hloc B hB e he
    rw [hρ, map_mul, map_mul, hρ, hρ]
  let ρ : R →+* Γ(W, G) :=
    { toFun := c, map_zero' := hzero, map_one' := hone,
      map_add' := hadd, map_mul' := hmul' }
  refine ⟨ρ, fun k t ↦ ?_⟩
  have ht := (hp k).coeff_smul ((L.tensorPow (k • d)).presheaf.map
    (homOfLE hG).op (lineProjImage f A L ψ V.1 (k • d) t))
  have heq : ρ (HomogeneousLocalization.Away.mk (A.grade V)
      (lineProjElement A V d a).property k (lineProjElement A V (k • d) t).val
        (lineProjElement A V (k • d) t).property) =
      (hp k).coeff ((L.tensorPow (k • d)).presheaf.map (homOfLE hG).op
        (lineProjImage f A L ψ V.1 (k • d) t)) := by
    apply lineProj_frame_ext L G
    intro B hB e he
    obtain ⟨ρB, hρB⟩ := lineProj_local_fraction_hom f A L ψ hunit hmul V d a B hB e he
    change W.presheaf.map (homOfLE hB).op (c _) = _
    rw [hloc' B hB ρB hρB]
    apply ((hp k).map hB).smul_left_injective
    have ht' := congrArg ((L.tensorPow (k • d)).presheaf.map (homOfLE hB).op) ht
    erw [map_smul, presheaf_map_homOfLE_map_homOfLE, lineProj_power_restrict] at ht'
    erw [lineProj_power_restrict]
    have hsr := presheaf_map_homOfLE_map_homOfLE hG hB
      (lineProjImage f A L ψ V.1 d a)
    change (L.tensorPow d).presheaf.map (homOfLE hB).op s = _ at hsr
    rw [hsr] at ht' ⊢
    exact (hρB k t).trans ht'.symm
  rw [heq]
  exact ht


/-- The scalar map of a chart commutes with source restriction.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_scalar_restrict {W : Scheme.{u}} {U C : W.Opens}
    (h : C ≤ U) {R : CommRingCat.{u}} (q : U.toScheme ⟶ Spec R) :
    lineProjScalar C (W.homOfLE h ≫ q) =
      lineProjScalar U q ≫ W.presheaf.map (homOfLE h).op := by
  unfold lineProjScalar
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  congr 1
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom,
    ← Functor.map_comp, ← op_comp]
  rfl

private theorem lineProj_scalar_ext {W : Scheme.{u}} (U : W.Opens)
    {R : CommRingCat.{u}} {q r : U.toScheme ⟶ Spec R}
    (h : lineProjScalar U q = lineProjScalar U r) : q = r := by
  apply AlgebraicGeometry.ext_to_Spec
  exact (cancel_mono U.topIso.hom).mp h

/-- The homogeneous fraction equation persists on smaller source opens.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_fraction_restrict {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (U C : W.Opens) (hU : U ≤ f ⁻¹ᵁ V.1) (h : C ≤ U)
    (q : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grade V)
      (lineProjElement A V d a).val)))
    (hq : LineProjFractionFormula f A L ψ V d a U hU q) :
    LineProjFractionFormula f A L ψ V d a C (h.trans hU) (W.homOfLE h ≫ q) := by
  intro m b
  have hh := congrArg ((L.tensorPow (m • d)).presheaf.map (homOfLE h).op) (hq m b)
  erw [map_smul, lineProj_power_restrict, presheaf_map_homOfLE_map_homOfLE,
    presheaf_map_homOfLE_map_homOfLE] at hh
  rw [lineProj_scalar_restrict]
  exact hh

/-- The homogeneous fraction equation determines a chart uniquely.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_fraction_unique {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (C : W.Opens) (hC : C ≤ lineProjGeneratorOpen f A L ψ V d a)
    (q r : C.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grade V)
      (lineProjElement A V d a).val)))
    (hq : LineProjFractionFormula f A L ψ V d a C (hC.trans inf_le_left) q)
    (hr : LineProjFractionFormula f A L ψ V d a C (hC.trans inf_le_left) r) : q = r := by
  apply lineProj_scalar_ext
  ext z
  obtain ⟨m, b, hb, hz⟩ := HomogeneousLocalization.Away.mk_surjective
    (A.grade V) (lineProjElement A V d a).property z
  obtain ⟨t, ht⟩ := (lineProj_component_equiv A V (m • d)).surjective ⟨b, hb⟩
  have hzt : HomogeneousLocalization.Away.mk (A.grade V)
      (lineProjElement A V d a).property m (lineProjElement A V (m • d) t).val
        (lineProjElement A V (m • d) t).property = z := by
    exact (congrArg (fun b ↦ HomogeneousLocalization.Away.mk (A.grade V)
      (lineProjElement A V d a).property m b.val b.property) ht).trans hz
  rw [← hzt]
  have hs := (lineProj_chart_generator f A L ψ V d a).map hC
  have hp := lineProj_power_generator L C d _ hs m
  apply hp.smul_left_injective
  simpa only [presheaf_map_homOfLE_map_homOfLE] using (hq m t).trans (hr m t).symm

/-- There is a unique homogeneous fraction chart on each generator open.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_exists_chart {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (V : T.affineOpens) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1)) :
    ∃ q : LineProjChart f A L ψ V d a,
      ∀ (C : W.Opens) (hC : C ≤ lineProjGeneratorOpen f A L ψ V d a)
        (r : C.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grade V)
          (lineProjElement A V d a).val))),
        LineProjFractionFormula f A L ψ V d a C (hC.trans inf_le_left) r ↔
          r = W.homOfLE hC ≫ q := by
  obtain ⟨ρ, hρ⟩ := exists_lineProj_fraction_coefficient_hom f A L ψ hunit hmul V d hd a
  let G := lineProjGeneratorOpen f A L ψ V d a
  let φ : CommRingCat.of (HomogeneousLocalization.Away (A.grade V)
      (lineProjElement A V d a).val) ⟶ Γ(G.toScheme, ⊤) :=
    CommRingCat.ofHom ρ ≫ G.topIso.inv
  let q := ΓSpec.adjunction.homEquiv G.toScheme (op (.of _)) φ.op
  have hq : LineProjFractionFormula f A L ψ V d a G inf_le_left q := by
    have hscalar : lineProjScalar G q = CommRingCat.ofHom ρ := by
      unfold lineProjScalar q
      erw [← Category.assoc, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
      simp only [φ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    intro m b
    rw [hscalar]
    exact hρ m b
  refine ⟨q, fun C hC r ↦ ?_⟩
  have hres := lineProj_fraction_restrict f A L ψ V d a G C inf_le_left hC q hq
  exact ⟨fun hr ↦ lineProj_fraction_unique f A L ψ V d a C hC r _ hr hres,
    fun hr ↦ hr ▸ hres⟩

/-- In a local frame the generator open is the basic open of its coefficient.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_open_basic {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (B : W.Opens) (hB : B ≤ f ⁻¹ᵁ V.1)
    (e : Γ(L, B)) (he : IsFreeGenerator e) (α : Γ(W, B))
    (ha : (L.tensorPow d).presheaf.map (homOfLE hB).op
      (lineProjImage f A L ψ V.1 d a) = α • lineProjFramePower L B e d) :
    lineProjGeneratorOpen f A L ψ V d a ⊓ B = W.basicOpen α := by
  ext x
  constructor
  · rintro ⟨hxG, hxB⟩
    obtain ⟨C, hC, hxC, hc⟩ := (lineProj_mem_generator_open _ _ _ x).mp hxG
    let H := B ⊓ C
    have heH := (lineProj_frame_generator L B e he d).map
      (inf_le_left : H ≤ B)
    have hsH := hc.map (inf_le_right : H ≤ C)
    have hsH' : IsFreeGenerator
        (W.presheaf.map (homOfLE (inf_le_left : H ≤ B)).op α •
          (L.tensorPow d).presheaf.map (homOfLE (inf_le_left : H ≤ B)).op
            (lineProjFramePower L B e d)) := by
      rw [← map_smul, ← ha, presheaf_map_homOfLE_map_homOfLE]
      simpa only [presheaf_map_homOfLE_map_homOfLE] using hsH
    obtain ⟨u, hu⟩ := heH.exists_unit_smul_eq hsH'
    have hα := heH.smul_left_injective hu
    have hxH : x ∈ H := ⟨hxB, hxC⟩
    have hxD : x ∈ W.basicOpen
        (W.presheaf.map (homOfLE (inf_le_left : H ≤ B)).op α) := by
      rw [hα, W.basicOpen_of_isUnit u.isUnit]
      exact hxH
    rw [Scheme.basicOpen_res] at hxD
    exact hxD.2
  · intro hx
    have hD := W.basicOpen_le α
    refine ⟨(lineProj_mem_generator_open _ _ _ x).mpr
      ⟨W.basicOpen α, hD.trans hB, hx, ?_⟩, hD hx⟩
    have hu : IsUnit (W.presheaf.map (homOfLE hD).op α) :=
      W.toRingedSpace.isUnit_res_basicOpen α
    have hs : (L.tensorPow d).presheaf.map (homOfLE (hD.trans hB)).op
        (lineProjImage f A L ψ V.1 d a) = hu.unit.val •
          (L.tensorPow d).presheaf.map (homOfLE hD).op
            (lineProjFramePower L B e d) := by
      rw [← presheaf_map_homOfLE_map_homOfLE hB hD, ha, map_smul]
      rfl
    rw [hs]
    exact ((lineProj_frame_generator L B e he d).map hD).units_smul _

/-- The fraction equation gives the scalar formula in every local frame.
Source: Stacks, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-line-proj-fraction-coefficient-hom). -/
theorem lineProj_trivialization_formula {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (q : LineProjChart f A L ψ V d a)
    (hq : LineProjFractionFormula f A L ψ V d a
      (lineProjGeneratorOpen f A L ψ V d a) inf_le_left q) :
    LineProjTrivializationFormula f A L ψ V d a q := by
  intro B hB e he αa ha
  refine ⟨lineProj_open_basic f A L ψ V d a B.1 hB e he αa ha, ?_⟩
  intro m b αb hb
  let G := lineProjGeneratorOpen f A L ψ V d a
  let C := G ⊓ B.1
  have hCa : C ≤ G := inf_le_left
  have hCb : C ≤ B.1 := inf_le_right
  have hh := congrArg ((L.tensorPow (m • d)).presheaf.map (homOfLE hCa).op) (hq m b)
  erw [map_smul, lineProj_power_restrict, presheaf_map_homOfLE_map_homOfLE,
    presheaf_map_homOfLE_map_homOfLE] at hh
  have har : (L.tensorPow d).presheaf.map (homOfLE (hCa.trans inf_le_left)).op
      (lineProjImage f A L ψ V.1 d a) =
      W.presheaf.map (homOfLE hCb).op αa •
        lineProjFramePower L C (L.presheaf.map (homOfLE hCb).op e) d := by
    have h := congrArg ((L.tensorPow d).presheaf.map (homOfLE hCb).op) ha
    erw [map_smul, presheaf_map_homOfLE_map_homOfLE, lineProj_frame_restrict] at h
    exact h
  have hbr : (L.tensorPow (m • d)).presheaf.map
      (homOfLE (hCa.trans inf_le_left)).op
      (lineProjImage f A L ψ V.1 (m • d) b) =
      W.presheaf.map (homOfLE hCb).op αb •
        lineProjFramePower L C (L.presheaf.map (homOfLE hCb).op e) (m • d) := by
    have h := congrArg ((L.tensorPow (m • d)).presheaf.map (homOfLE hCb).op) hb
    erw [map_smul, presheaf_map_homOfLE_map_homOfLE, lineProj_frame_restrict] at h
    exact h
  rw [har, lineProj_power_smul, lineProj_power_frame, smul_smul, hbr] at hh
  exact (lineProj_frame_generator L C _ (he.map hCb) (m • d)).smul_left_injective hh

end AlgebraicGeometry.Scheme.Modules
