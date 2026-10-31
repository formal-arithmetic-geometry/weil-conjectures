/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TateTensorFiniteTransitionData
import all WeilConjectures.AlgebraicGeometry.FiniteTateLocalRootTensorsExt
import all WeilConjectures.AlgebraicGeometry.FiniteTateNormalizedCoherence

/-! The ordinary square between the root-power map and the integral quotient tower.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem coefficient_map_smul
    (ell n : ℕ) [Fact ell.Prime] {M N : Type*}
    [AddCommGroup M] [AddCommGroup N]
    [Module (coefficient.{u} ell (n + 1)) M]
    [Module (coefficient.{u} ell (n + 1)) N]
    (f : M →+ N) (c : coefficient.{u} ell (n + 1)) (x : M) :
    f (c • x) = c • f x := by
  have : NeZero (ell ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ell.Prime).ne_zero⟩
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective c.down.down
  have hc : (k : coefficient.{u} ell (n + 1)) = c := by
    apply ULift.ext
    apply ULift.ext
    exact hk
  rw [← hc, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

private def fixedTarget (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (α : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    (N : SheafOfModules.{u + 1} R) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A) := by
  let P := (PresheafOfModules.restrictScalars α).obj N.val
  let F : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} A :=
    { obj := P.obj
      map := fun f ↦ P.map f
      map_id := fun U ↦ by ext x; exact P.presheaf.map_id_apply U x
      map_comp := fun f g ↦ by ext x; exact P.map_comp_apply f g x }
  exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology T) F
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) N.isSheaf⟩

private def additiveCoefficientHom
    (T : Scheme.{u}) (ell n : ℕ) [Fact ell.Prime]
    (F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient ell (n + 1))))
    (φ : F.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1} ⟶
      G.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1}) : F ⟶ G where
  hom :=
    { app := fun W ↦ ModuleCat.ofHom
        { toFun := φ.app W
          map_add' := map_add _
          map_smul' := fun c x ↦
            coefficient_map_smul ell n
              (show F.obj.obj W →+ G.obj.obj W from (φ.app W).hom) c x }
      naturality := fun _ _ v ↦ by
        ext y
        exact ConcreteCategory.congr_hom (φ.naturality v) y }

private abbrev realizedGenerator
    (T : Scheme.{u}) (ell n d : ℕ) [Fact ell.Prime]
    (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (v : W.unop ⟶ (toProEt T).obj U.unop) (s : coefficient ell (n + 1))
    (z : Fin d → (T.rootsOfUnitySheaf (ell ^ (n + 1))).obj.obj U) :
    ((realization T ell n).obj (finiteSheaf T ell n d)).val.obj W :=
  (toSheafify (ProEt.topology T)
    ((finiteSheaf T ell n d).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
    ((finiteSheaf T ell n d).obj.map v.op
      (((ProEtale.comparisonAdjunction
        (ModuleCat.{u + 1} (coefficient ell (n + 1))) T).unit.app
          (finiteEtaleTateTwist T (ell ^ (n + 1)) (coefficient ell (n + 1))
            (CharP.cast_eq_zero _ _) d)).hom.app U
        (finiteTateEtalePowerGenerator T _ (ell ^ (n + 1))
          (CharP.cast_eq_zero _ _) U s d z)))

private theorem realized_root_hom_ext
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d b a : ℕ) (hab : a ≤ b)
    (f g : (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).obj
        ((realization T ell b).obj (finiteSheaf T ell b d)) ⟶
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).obj (quotientLine T ell a d))
    (h : ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
      (v : W.unop ⟶ (toProEt T).obj U.unop) (s : coefficient ell (b + 1))
      (z : Fin d → (T.rootsOfUnitySheaf (ell ^ (b + 1))).obj.obj U)
      (x : Fin d → (purTwistZlOne T ell).obj.obj W),
      (∀ i, finiteTateLimitRootValue ell T b W (x i) =
        Units.map v.left.appTop.hom.toMonoidHom
          (finiteTateEtaleRootValue T (ell ^ (b + 1)) U (z i))) →
      f.val.app W (realizedGenerator T ell b d U W v s z) =
        g.val.app W (realizedGenerator T ell b d U W v s z)) : f = g := by
  let R := (adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op a))
  let α := (Functor.const T.ProEtᵒᵖ).map
    (RingCat.ofHom (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))) ≫
      scalars T ell a
  let N := fixedTarget T (coefficient ell (b + 1)) R α (quotientLine T ell a d)
  let η := toSheafify (ProEt.topology T)
    ((finiteSheaf T ell b d).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})
  let F := SheafOfModules.toSheaf
    ((adicLisseForget T).obj (pbcAdicCompletion T (datum.{u} ell)))
  let f₀ := additiveCoefficientHom T ell b (finiteSheaf T ell b d) N
    (η ≫ (F.map f).hom)
  let g₀ := additiveCoefficientHom T ell b (finiteSheaf T ell b d) N
    (η ≫ (F.map g).hom)
  have he : f₀ = g₀ := by
    let adj := ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (coefficient ell (b + 1))) T
    apply (adj.homEquiv _ _).injective
    apply finite_tate_generators_hom_ext
    intro U s z
    obtain ⟨S, hS, hlift⟩ := finite_roots_lift_cover ell T hT b d U z
    let t := (adj.unit.app (finiteEtaleTateTwist T (ell ^ (b + 1))
      (coefficient ell (b + 1)) (CharP.cast_eq_zero _ _) d)).hom.app U
        (finiteTateEtalePowerGenerator T _ (ell ^ (b + 1))
          (CharP.cast_eq_zero _ _) U s d z)
    change f₀.hom.app (op ((toProEt T).obj U.unop)) t =
      g₀.hom.app (op ((toProEt T).obj U.unop)) t
    apply (((isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (ProEt.topology T)
        (CategoryTheory.forget (ModuleCat.{u + 1} (coefficient ell (b + 1))))).obj N).property
      ).isSeparated _ hS).ext
    intro W v hv
    obtain ⟨x, hx⟩ := hlift W v hv
    have hf := ConcreteCategory.congr_hom (f₀.hom.naturality v.op) t
    have hg := ConcreteCategory.congr_hom (g₀.hom.naturality v.op) t
    exact hf.symm.trans ((h U (op W) v s z x hx).trans hg)
  apply F.map_injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology T) _ _ (F.obj _).property
  ext W y
  exact congrArg (fun k ↦ k.hom.app W y) he

private theorem reduction_tensor_formula
    (T : Scheme.{u}) (B : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (R : ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (π : (Functor.const ℕᵒᵖ).obj B ⟶ R) (M : pbcModules T B)
    (b a : ℕ) (hab : a ≤ b) (W : T.ProEtᵒᵖ)
    (t : (R.obj (op b)).obj.obj W) (x : M.val.obj W) :
    (((localReductionModuleTower T B R π).obj M).map (homOfLE hab).op).val.app W
        (pbcTensorSection (π.app (op b)) M W t x) =
      pbcTensorSection (π.app (op a)) M W
        ((R.map (homOfLE hab).op).hom.app W t) x := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [homOfLE_refl, op_id]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  | succ b hab ih =>
    have he : (homOfLE (Nat.le_trans hab (Nat.le_succ b))).op =
        (homOfLE (Nat.le_succ b)).op ≫ (homOfLE hab).op := Subsingleton.elim _ _
    rw [he, Functor.map_comp]
    change (((localReductionModuleTower T B R π).obj M).map (homOfLE hab).op).val.app W
      ((((localReductionModuleTower T B R π).obj M).map
        (homOfLE (Nat.le_succ b)).op).val.app W _) = _
    have hs := (localReductionStep_exists T B R π b).exists.choose_spec M W t x
    change ((localReductionStep T B R π b).app M).val.app W _ = _ at hs
    have hstep : ((localReductionModuleTower T B R π).obj M).map
        (homOfLE (Nat.le_succ b)).op = (localReductionStep T B R π b).app M := by
      exact congrArg (fun z ↦ z.app M)
        (Functor.ofOpSequence_map_homOfLE_succ (fun n ↦ localReductionStep T B R π n) b)
    rw [hstep]
    exact (congrArg (fun y ↦
      (((localReductionModuleTower T B R π).obj M).map
        (homOfLE hab).op).val.app W y) hs).trans
          ((ih _).trans (by rw [Functor.map_comp]; rfl))

private theorem root_lift_reduction
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (v : W.unop ⟶ (toProEt T).obj U.unop)
    (z : (T.rootsOfUnitySheaf (ell ^ (b + 1))).obj.obj U)
    (x : (purTwistZlOne T ell).obj.obj W)
    (hx : finiteTateLimitRootValue ell T b W x =
      Units.map v.left.appTop.hom.toMonoidHom
        (finiteTateEtaleRootValue T (ell ^ (b + 1)) U z)) :
    finiteTateLimitRootValue ell T a W x =
      Units.map v.left.appTop.hom.toMonoidHom
        (finiteTateEtaleRootValue T (ell ^ (a + 1)) U (r.roots.hom.app U z)) := by
  have hp := etale_root_power_value T _ _ _ r.roots r.roots_power U z
  have hd : ell ^ (b + 1) / ell ^ (a + 1) = ell ^ (b - a) := by
    rw [← Nat.sub_add_cancel (Nat.add_le_add_right hab 1), pow_add,
      Nat.mul_div_cancel _ (pow_pos (Fact.out : ell.Prime).pos _)]
    congr 1
    omega
  rw [hp, hd, map_pow, limit_root_power ell T a b hab W x, hx]

/-- A map of ordinary finite root tensors with the root-power formula agrees with
the transition of the ordinary integral quotient tower after balanced identifications.
This is an identity of sheaf maps; no derived functor or adic tower appears.

Source: smooth-purity transport, normalized Tate tower, Step 4, ordinary quotient
balancing. (blueprint: lem-pur-tate-tensor-balanced-transition)

Proof: the adjacent strict quotient transition sends t tensor x to q(t) tensor x,
by localReductionStep_exists. Induct on b-a to obtain this formula for every
comparable pair, using the quotient cocycle, with the identity at equal indices.
Check the proposed square locally on scalar multiples of finite pure root tensors.
Lift their roots, after a pro-etale covering, to compatible integral root families;
such lifts exist since ell is invertible. The upper and lower projections of one
family are related by the power map, which is r.roots by roots_power and monicity
of the root inclusion. Apply ProjectionBalanced at b and a and the assumed formula
for f. Both composites send t times the finite tensor with scalar s to
q(t) times scalars_a(phi(s)) tensor the integral generator. The equality of scalars
is scalars_comp. Local tensor generation, the site comparison adjunction and the
associated-module sheafification unit show that these elements locally span the
source; hence the two sheaf maps agree. For d=0 this is coefficient multiplication,
and the proof also includes empty schemes and zero sections. -/
theorem tateTensor_balanced_transition
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (f : (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).obj
        ((realization T ell b).obj (finiteSheaf T ell b d)) ⟶
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).obj
        ((realization T ell a).obj (finiteSheaf T ell a d)))
    (hf : FiniteRootTransition T ell d b a hab r f)
    (cb : (realization T ell b).obj (finiteSheaf T ell b d) ≅ quotientLine T ell b d)
    (ca : (realization T ell a).obj (finiteSheaf T ell a d) ≅ quotientLine T ell a d)
    (hb : ProjectionBalanced T ell b d cb) (ha : ProjectionBalanced T ell a d ca) :
    f ≫ (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).map ca.hom =
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).map cb.hom ≫
        (strictTower T ell d).map (homOfLE hab).op := by
  apply realized_root_hom_ext T ell hT d b a hab
  intro U W v s z x hx
  have hx' (i : Fin d) := root_lift_reduction T ell b a hab r U W v (z i) (x i) (hx i)
  have hf' := hf U W v s 1 z
  have hb' := hb U W v s 1 z x hx
  have ha' := ha U W v
    (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1) s) 1
    (fun i ↦ r.roots.hom.app U (z i)) x hx'
  simp only [one_smul, map_one, one_mul] at hf' hb' ha'
  change ca.hom.val.app W (f.val.app W (realizedGenerator T ell b d U W v s z)) =
    ((strictTower T ell d).map (homOfLE hab).op).val.app W
      (cb.hom.val.app W (realizedGenerator T ell b d U W v s z))
  erw [hf', ha', hb']
  rw [show ((strictTower T ell d).map (homOfLE hab).op).val.app W
      (pbcTensorSection (pbcAdicProjection T (datum ell) b) (integralLine T ell d) W
        ((scalars T ell b).app W s) (integralGenerator T ell W d x)) =
      pbcTensorSection (pbcAdicProjection T (datum ell) a) (integralLine T ell d) W
        ((pbcAdicQuotient T (datum ell) b a hab).hom.app W
          ((scalars T ell b).app W s)) (integralGenerator T ell W d x) from
    reduction_tensor_formula T _ _ _ _ b a hab W _ _]
  congr 1
  exact (RingHom.congr_fun
    (congrArg RingCat.Hom.hom (NatTrans.congr_app (scalars_comp T ell b a hab) W)) s).symm

end AlgebraicGeometry.Scheme.PurityIntegralTower
