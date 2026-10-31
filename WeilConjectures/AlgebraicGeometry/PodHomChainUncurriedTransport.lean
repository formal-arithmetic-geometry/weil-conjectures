/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCtfPairingMaps

/-! # The uncurried four-arrow Hom transport

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction.proof.md, Step 1 read backwards
(blueprint: lem-pod-hom-chain-uncurried-transport).

The internal Hom and canonical projection are the shared declarations in
PodCtfPairingMaps. The restricted operations and their chosen closed
presentation are those of PodCtfAdjunctions, on the actual finite-Tor domains.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PodHomChain

variable {D : FiniteFieldDatum.{u}} {A : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic A.l) E]
  [FiniteDimensional (Padic A.l) E] {n : ℕ} {hn : 1 ≤ n}
  (six : SixFunctorOperationDatum D A E n hn) (s : PodCoefficientStage)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (R : PodCtfAdjunctionData (PodCoefficientStage.operations six s)
    (PodCoefficientStage.domain six s) (PodCoefficientStage.homPairs (S := six) s)
    (PodCoefficientStage.internalHom (S := six) s) (PodCoefficientStage.tensor six s) f c)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]

/-- The left-factor tensor on the actual source finite-Tor category.
Source: blueprint Step 1 (blueprint: lem-pod-hom-chain-uncurried-transport). -/
abbrev tensorX := @MonoidalCategory.curriedTensor _ _ R.closedX.closed.monoidal

/-- The left-factor tensor on the actual target finite-Tor category.
Source: blueprint Step 1 (blueprint: lem-pod-hom-chain-uncurried-transport). -/
abbrev tensorY := @MonoidalCategory.curriedTensor _ _ R.closedY.closed.monoidal

private theorem fixed_left_naturality
    {B : Type*} {B' : Type*} {V : Type*} {V' : Type*}
    [Category B] [Category B'] [Category V] [Category V']
    (F : B ⥤ B') (G : V' ⥤ V) (TX : B ⥤ V ⥤ B) (TY : B' ⥤ V' ⥤ B')
    (P : ∀ K L, (TY.obj (F.obj K)).obj L ⟶ F.obj ((TX.obj K).obj (G.obj L)))
    (K : B) {L L' : V'} (b : L ⟶ L')
    (h : ∀ a : K ⟶ K,
      (TY.map (F.map a)).app L ≫ (TY.obj (F.obj K)).map b ≫ P K L' =
        P K L ≫ F.map ((TX.map a).app (G.obj L) ≫ (TX.obj K).map (G.map b))) :
    (TY.obj (F.obj K)).map b ≫ P K L' =
      P K L ≫ F.map ((TX.obj K).map (G.map b)) := by
  have h' := h (𝟙 K)
  rw [F.map_id, TY.map_id, TX.map_id] at h'
  simpa only [NatTrans.id_app, Category.id_comp] using h'

private theorem rawProjection_naturality
    (M : (PodCoefficientStage.domain six s X).FullSubcategory)
    {T U : (PodCoefficientStage.domain six s Y).FullSubcategory} (t : T ⟶ U) :
    ((PodCoefficientStage.tensor six s Y).obj (R.support.obj M).obj).map t ≫
        PodCtfPairing.rawProjection six s f c R M U =
      PodCtfPairing.rawProjection six s f c R M T ≫
        ((PodCoefficientStage.operations six s).support f c).map
          (((PodCoefficientStage.tensor six s X).obj M.obj).map (R.pull.map t)) := by
  cases s with
  | finite =>
    have h := fixed_left_naturality
      (six.finite.support f c) (CompactSupportFiniteProjection.torPull
        six.toSixFunctorFiniteOperations f)
      (CompactSupportFiniteProjection.partialTensor six.toSixFunctorFiniteOperations X)
      (CompactSupportFiniteProjection.partialTensor six.toSixFunctorFiniteOperations Y)
      (CompactSupportFiniteProjection.component six.toSixFunctorFiniteOperations f c) M.obj
      (L := ⟨T.obj.obj, T.property⟩) (L' := ⟨U.obj.obj, U.property⟩)
      (ObjectProperty.homMk t.hom.hom)
      (fun a ↦ (compactSupportProjectionFormula six).1.naturality f c a _)
    exact h
  | integral =>
    have h := fixed_left_naturality (six.higher.integral.support f c)
      (six.higher.integral.pull f) (six.higher.integralTensor X)
      (six.higher.integralTensor Y)
      (compactSupportProjectionComponent six.higher.integralExchange f c) M.obj t.hom
      (fun a ↦ (compactSupportProjectionFormula six).2.1.naturality f c
        T.property U.property a t.hom)
    exact h
  | rational =>
    have h := fixed_left_naturality (six.higher.rational.support f c)
      (six.higher.rational.pull f) (six.higher.rationalTensor X)
      (six.higher.rationalTensor Y)
      (compactSupportProjectionComponent six.higher.rationalExchange f c) M.obj t.hom
      (fun a ↦ (compactSupportProjectionFormula six).2.2.1.naturality f c
        trivial trivial a t.hom)
    exact h
  | common =>
    have h := fixed_left_naturality (six.closure.commonStage.support f c)
      (six.closure.commonStage.pull f) (six.closure.commonStageTensor X)
      (six.closure.commonStageTensor Y)
      (compactSupportProjectionComponent six.closure.commonStageExchange f c) M.obj t.hom
      (fun a ↦ (compactSupportProjectionFormula six).2.2.2.1.naturality f c
        trivial trivial a t.hom)
    exact h

private theorem rawProjectionIso_hom
    (M : (PodCoefficientStage.domain six s X).FullSubcategory)
    (T : (PodCoefficientStage.domain six s Y).FullSubcategory) :
    (PodCtfPairing.rawProjectionIso six s f c R M T).hom =
      PodCtfPairing.rawProjection six s f c R M T := by
  cases s <;> rfl

private theorem projection_naturality
    (M : (PodCoefficientStage.domain six s X).FullSubcategory)
    {T U : (PodCoefficientStage.domain six s Y).FullSubcategory} (t : T ⟶ U) :
    PodCtfPairing.projection six s f c R M T ≫
        R.support.map (((tensorX six s f c R).obj M).map (R.pull.map t)) =
      ((tensorY six s f c R).obj (R.support.obj M)).map t ≫
        PodCtfPairing.projection six s f c R M U := by
  apply (PodCoefficientStage.domain six s Y).ι.map_injective
  simp only [Functor.map_comp, PodCtfPairing.projection, PodCtfPairing.projectionIso,
    Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    rawProjectionIso_hom]
  have hx := (R.tensorX M).inv.naturality (R.pull.map t)
  have hy := (R.tensorY (R.support.obj M)).hom.naturality t
  have hp := rawProjection_naturality six s f c R M t
  dsimp only [Functor.comp_map] at hx hy
  simp only [Category.assoc]
  change (R.tensorY (R.support.obj M)).hom.app T ≫
      PodCtfPairing.rawProjection six s f c R M T ≫
      ((PodCoefficientStage.operations six s).support f c).map
        ((R.tensorX M).inv.app (R.pull.obj T)) ≫
      ((PodCoefficientStage.operations six s).support f c).map
        ((PodCoefficientStage.domain six s X).ι.map
          (((tensorX six s f c R).obj M).map (R.pull.map t))) =
    (PodCoefficientStage.domain six s Y).ι.map
        (((tensorY six s f c R).obj (R.support.obj M)).map t) ≫
      (R.tensorY (R.support.obj M)).hom.app U ≫
      PodCtfPairing.rawProjection six s f c R M U ≫
      ((PodCoefficientStage.operations six s).support f c).map
        ((R.tensorX M).inv.app (R.pull.obj U))
  rw [← Functor.map_comp, ← hx, Functor.map_comp]
  calc
    _ = ((R.tensorY (R.support.obj M)).hom.app T ≫
        (PodCtfPairing.rawProjection six s f c R M T ≫
          ((PodCoefficientStage.operations six s).support f c).map
            (((PodCoefficientStage.tensor six s X).obj M.obj).map (R.pull.map t)))) ≫
        ((PodCoefficientStage.operations six s).support f c).map
          ((R.tensorX M).inv.app (R.pull.obj U)) := by simp only [Category.assoc]
    _ = _ := by
      rw [← hp, ← Category.assoc, ← hy]
      simp only [Category.assoc]


variable (M : (PodCoefficientStage.domain six s X).FullSubcategory)
  (N : (PodCoefficientStage.domain six s Y).FullSubcategory)

/-- L_N is the existing restricted internal Hom of M into f!N.
Source: blueprint Step 1 (blueprint: lem-pod-hom-chain-uncurried-transport). -/
abbrev internalHomObject := (PodCtfPairing.homX six s f c R M).obj (R.exceptional.obj N)

/-- A_N is the value of the existing ordinary-direct-image Hom functor.
Source: blueprint Step 1 (blueprint: lem-pod-hom-chain-uncurried-transport). -/
abbrev directHomObject := R.direct.obj (internalHomObject six s f c R M N)

variable (a : (tensorX six s f c R).obj M ⊣ PodCtfPairing.homX six s f c R M)

/-- q_N is tensor of the ordinary counit followed by the chosen evaluation counit.
Source: blueprint Step 1 (blueprint: lem-pod-hom-chain-uncurried-transport). -/
def q :
    ((tensorX six s f c R).obj M).obj
        (R.pull.obj (directHomObject six s f c R M N)) ⟶ R.exceptional.obj N :=
  ((tensorX six s f c R).obj M).map
      (R.ordinaryAdjunction.counit.app (internalHomObject six s f c R M N)) ≫
    a.counit.app (R.exceptional.obj N)

/-- p_N is the existing canonical projection, support pushforward of q_N,
and the exceptional counit, in that order. It retains the free chosen adjunction a.
Source: blueprint Step 1 (blueprint: lem-pod-hom-chain-uncurried-transport). -/
def p :
    ((tensorY six s f c R).obj (R.support.obj M)).obj
      (directHomObject six s f c R M N) ⟶ N :=
  PodCtfPairing.projection six s f c R M (directHomObject six s f c R M N) ≫
    R.support.map (q six s f c R M N a) ≫ R.exceptionalAdjunction.counit.app N

/-- Every successive inverse transpose has the displayed counit/evaluation formula,
and the last one factors through tensor of t by the specified projection square.
Source: blueprint main-20261015, fix-lem-tensor-adjunction.proof.md Step 1, read
in reverse (blueprint: lem-pod-hom-chain-uncurried-transport).

Proof:
1. Use the restricted adjunctions of det-thm-sf-ctf-stability-adjunctions on the
   finite-Tor domains of lem-pod-hom-chain-ctf-domains. Inverse ordinary adjunction
   sends t to pull.map t followed by its counit: expand homEquiv_symm_apply,
   using unit naturality and the triangle identity.
2. The inverse of the chosen left-factor tensor-Hom adjunction a is tensor(M,u)
   followed by its evaluation counit, by lem-pod-closed-uncurry-laws. Substituting
   step 1 and tensor functoriality factors this through q_N, without a braiding.
3. Inverse exceptional adjunction sends v to support.map v followed by its counit.
   The support and exceptional functors are the supplied finite-Tor restrictions.
4. Naturality in the test object of the specified projection from
   fix-prop-projection-formula gives the last displayed square at t. The shared
   projection transports the canonical compactification projection through the
   chosen tensor comparisons and the full inclusion.
5. Substitute step 2 into projection followed by step 3. Support functoriality,
   the square of step 4 and associativity give tensor(C,t) followed by p_N.
   The first four conjuncts retain every intermediate image separately. Integral
   operations are completed; field operations rationalize and use common stages.
-/
theorem uncurried_transport
    (T : (PodCoefficientStage.domain six s Y).FullSubcategory)
    (t : T ⟶ directHomObject six s f c R M N) :
    (R.ordinaryAdjunction.homEquiv T
        (internalHomObject six s f c R M N)).symm t =
      R.pull.map t ≫
        R.ordinaryAdjunction.counit.app (internalHomObject six s f c R M N) ∧
    (a.homEquiv (R.pull.obj T)
        (R.exceptional.obj N)).symm
        ((R.ordinaryAdjunction.homEquiv T
          (internalHomObject six s f c R M N)).symm t) =
      ((tensorX six s f c R).obj M).map
        ((R.ordinaryAdjunction.homEquiv T
          (internalHomObject six s f c R M N)).symm t) ≫
        a.counit.app (R.exceptional.obj N) ∧
    (a.homEquiv (R.pull.obj T)
        (R.exceptional.obj N)).symm
        ((R.ordinaryAdjunction.homEquiv T
          (internalHomObject six s f c R M N)).symm t) =
      ((tensorX six s f c R).obj M).map (R.pull.map t) ≫
        q six s f c R M N a ∧
    (R.exceptionalAdjunction.homEquiv
        (((tensorX six s f c R).obj M).obj (R.pull.obj T)) N).symm
        ((a.homEquiv (R.pull.obj T)
          (R.exceptional.obj N)).symm
          ((R.ordinaryAdjunction.homEquiv T
            (internalHomObject six s f c R M N)).symm t)) =
      R.support.map
        ((a.homEquiv (R.pull.obj T)
          (R.exceptional.obj N)).symm
          ((R.ordinaryAdjunction.homEquiv T
            (internalHomObject six s f c R M N)).symm t)) ≫
        R.exceptionalAdjunction.counit.app N ∧
    PodCtfPairing.projection six s f c R M T ≫
        (R.exceptionalAdjunction.homEquiv
          (((tensorX six s f c R).obj M).obj (R.pull.obj T)) N).symm
          ((a.homEquiv (R.pull.obj T)
            (R.exceptional.obj N)).symm
            ((R.ordinaryAdjunction.homEquiv T
              (internalHomObject six s f c R M N)).symm t)) =
      ((tensorY six s f c R).obj (R.support.obj M)).map t ≫
        p six s f c R M N a ∧
    PodCtfPairing.projection six s f c R M T ≫
        R.support.map
          (((tensorX six s f c R).obj M).map (R.pull.map t)) =
      ((tensorY six s f c R).obj (R.support.obj M)).map t ≫
        PodCtfPairing.projection six s f c R M (directHomObject six s f c R M N) := by
  have ho := R.ordinaryAdjunction.homEquiv_symm_apply T
    (internalHomObject six s f c R M N) t
  have ha := a.homEquiv_symm_apply (R.pull.obj T) (R.exceptional.obj N)
    ((R.ordinaryAdjunction.homEquiv T (internalHomObject six s f c R M N)).symm t)
  have hv : (a.homEquiv (R.pull.obj T) (R.exceptional.obj N)).symm
      ((R.ordinaryAdjunction.homEquiv T
        (internalHomObject six s f c R M N)).symm t) =
      ((tensorX six s f c R).obj M).map (R.pull.map t) ≫
        q six s f c R M N a := by
    rw [ha, ho, Functor.map_comp, Category.assoc]
    rfl
  have he := R.exceptionalAdjunction.homEquiv_symm_apply
    (((tensorX six s f c R).obj M).obj (R.pull.obj T)) N
    ((a.homEquiv (R.pull.obj T) (R.exceptional.obj N)).symm
      ((R.ordinaryAdjunction.homEquiv T
        (internalHomObject six s f c R M N)).symm t))
  have hp := projection_naturality six s f c R M t
  refine ⟨ho, ha, hv, he, ?_, hp⟩
  rw [he, hv, Functor.map_comp, ← Category.assoc, ← Category.assoc, hp]
  simp only [p, Category.assoc]


end WeilConjectures.PodHomChain
