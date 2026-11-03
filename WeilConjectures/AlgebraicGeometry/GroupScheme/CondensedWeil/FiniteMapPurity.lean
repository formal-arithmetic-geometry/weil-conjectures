/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.DeligneLaumon.CondensedFiniteEtale.CondensedFiniteEtaleStalkCycles
import WeilConjectures.SixFunctors.Finite.Stalk
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WeilConjectures.PointCount

/-! # Purity under finite etale pushforward

Source: latest blueprint,
part-weights-riemann-hypothesis/sec-deligne-laumon-a1/sec-arbitrary-curves/
sk-lem-wft-finite-map,
`lem-a1-finite-map-purity` (blueprint: lem-a1-finite-map-purity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.CondensedWeil

/-- The canonical Weil module obtained by finite etale direct image.
Source: the finite etale pushforward in the blueprint
(blueprint: lem-a1-finite-map-purity). -/
noncomputable def finiteEtaleLowerStar
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (g₀ : X₀ ⟶ Y₀) [IsFinite g₀.left]
    (M : NativeL2.WeilModule D l X₀) : NativeL2.WeilModule D l Y₀ :=
  Endofunctor.IsoAlgebra.mk
    (CondensedFiniteEtale.directImage D l g₀ M.carrier)
    (CondensedFiniteEtale.directImageWeil D l g₀
      (by
        let := Fintype.ofFinite D.k₀
        apply pullback.hom_ext
        · simp only [Category.assoc, CondensedFiniteEtale.geometricMap,
            Over.pullback_map_left, pullback.lift_fst]
          simp only [← Category.assoc, FiniteFieldDatum.geometricFrobenius]
          rw [(D.galoisMap_projections _ _).1]
          rw [Category.assoc, (D.galoisMap_projections _ _).1]
          simp only [pullback.lift_fst]
        · simp only [Category.assoc, CondensedFiniteEtale.geometricMap,
            Over.pullback_map_left, pullback.lift_snd]
          simp only [FiniteFieldDatum.geometricFrobenius]
          rw [(D.galoisMap_projections _ _).2]
          rw [(D.galoisMap_projections _ _).2]
          rw [← Category.assoc, pullback.lift_snd]) M.carrier M.str)

private theorem dependent_congr {A : Sort v} {B : A → Sort w}
    (f : ∀ a, B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

private theorem native_positivePower_eq {T : Scheme.{u}} (a : T ⟶ T) :
    NativeCondensedModule.localPositivePower a = localPositivePower a := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun f ↦ f ≫ a) ih

private theorem evaluateStep_eq {C : Type v} [Category.{w} C]
    (F G H : C ⥤ C) (c : H ≅ G ⋙ F) (M : C) (θ : G.obj M ≅ M) :
    NativeCondensedModule.evaluateStep F G H c M θ =
      CondensedModule.evaluateStep F G H c M θ := by
  rfl

private theorem evaluateInitial_eq {C : Type v} [Category.{w} C]
    (F G : C ⥤ C) (c : F ≅ G) (M : C) (θ : G.obj M ≅ M) :
    NativeCondensedModule.evaluateInitial F G c M θ =
      CondensedModule.evaluateInitial F G c M θ := by
  rfl

private theorem evaluateStep_heq {C : Type v} [Category.{w} C]
    {F F' H H' : C ⥤ C} (G : C ⥤ C) (hF : F = F') (hH : H = H')
    (c : H ≅ G ⋙ F) (c' : H' ≅ G ⋙ F') (hc : HEq c c')
    (M : C) (θ : G.obj M ≅ M) :
    HEq (CondensedModule.evaluateStep F G H c M θ)
      (CondensedModule.evaluateStep F' G H' c' M θ) := by
  cases hF
  cases hH
  cases eq_of_heq hc
  rfl

private theorem nativeStepOne (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} (a : T ⟶ T) (M : NativeCondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (n : ℕ) : NativeCondensedModule.iterateStep l a M θ n =
    CondensedModule.evaluateStep
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (NativeCondensedModule.localPositivePower a n))
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (NativeCondensedModule.localPositivePower a (n + 1)))
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
        (NativeCondensedModule.localPositivePower a n) a) M θ := by
  unfold NativeCondensedModule.iterateStep
  exact evaluateStep_eq _ _ _ _ _ _

private theorem sharedStepOne (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} (a : T ⟶ T) (M : NativeCondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (n : ℕ) : CondensedModule.iterateStep l a M θ n =
    CondensedModule.evaluateStep
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (localPositivePower a n))
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (localPositivePower a (n + 1)))
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
        (localPositivePower a n) a) M θ := by
  unfold CondensedModule.iterateStep
  rfl

private theorem native_step_heq (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} (a : T ⟶ T) (M : NativeCondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (n : ℕ) :
    HEq (NativeCondensedModule.iterateStep l a M θ n)
      (CondensedModule.iterateStep l a M θ n) := by
  let U (f : T ⟶ T) := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f
  have hF := congrArg U (congrFun (native_positivePower_eq a) n)
  have hH := congrArg U (congrFun (native_positivePower_eq a) (n + 1))
  have hc := dependent_congr
    (fun f : T ⟶ T ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f a)
    (congrFun (native_positivePower_eq a) n)
  have hn := heq_of_eq (nativeStepOne l a M θ n)
  have hs := heq_of_eq (sharedStepOne l a M θ n).symm
  have hm := evaluateStep_heq (U a) hF hH _ _ hc M θ
  exact hn.trans (hm.trans hs)

private theorem isoChain_eq {C : Type v} [Category.{w} C]
    (P : ℕ → C) (M : C) (i : P 0 ≅ M)
    (s : ∀ n, P (n + 1) ≅ P n) (n : ℕ) :
    NativeCondensedModule.isoChain P M i s n = CondensedModule.isoChain P M i s n := by
  rfl

private theorem nativeIterateOne (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} (a : T ⟶ T) (M : NativeCondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (n : ℕ) : NativeCondensedModule.iterate l a M θ n =
      CondensedModule.isoChain
        (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (NativeCondensedModule.localPositivePower a k)).obj M) M
        (NativeCondensedModule.evaluateInitial
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (NativeCondensedModule.localPositivePower a 0))
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
          (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l)
            (show NativeCondensedModule.localPositivePower a 0 = a from rfl)) M θ)
        (NativeCondensedModule.iterateStep l a M θ) n := by
  unfold NativeCondensedModule.iterate
  exact isoChain_eq _ _ _ _ _

private theorem sharedIterateOne (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} (a : T ⟶ T) (M : NativeCondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (n : ℕ) : CondensedModule.iterate l a M θ n =
      CondensedModule.isoChain
        (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (localPositivePower a k)).obj M) M
        (CondensedModule.evaluateInitial
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (localPositivePower a 0))
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
          (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l)
            (show localPositivePower a 0 = a from rfl)) M θ)
        (CondensedModule.iterateStep l a M θ) n := by
  unfold CondensedModule.iterate
  rfl

private theorem evaluateInitial_heq {C : Type v} [Category.{w} C]
    {F F' : C ⥤ C} (G : C ⥤ C) (hF : F = F')
    (c : F ≅ G) (c' : F' ≅ G) (hc : HEq c c')
    (M : C) (θ : G.obj M ≅ M) :
    HEq (CondensedModule.evaluateInitial F G c M θ)
      (CondensedModule.evaluateInitial F' G c' M θ) := by
  cases hF
  cases eq_of_heq hc
  rfl

private theorem dependent_congr_proof {A : Sort v} {P : A → Prop} {B : A → Sort w}
    (f : ∀ a, P a → B a) {a b : A} (h : a = b) (ha : P a) (hb : P b) :
    HEq (f a ha) (f b hb) := by
  cases h
  rfl

private theorem native_initial_heq (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} (a : T ⟶ T) (M : NativeCondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M) :
    HEq (NativeCondensedModule.evaluateInitial
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (NativeCondensedModule.localPositivePower a 0))
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
          (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l)
            (show NativeCondensedModule.localPositivePower a 0 = a from rfl)) M θ)
      (CondensedModule.evaluateInitial
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (localPositivePower a 0))
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
          (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l)
            (show localPositivePower a 0 = a from rfl)) M θ) := by
  let U (f : T ⟶ T) := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f
  have h := congrFun (native_positivePower_eq a) 0
  have hc := dependent_congr_proof
    (fun f : T ⟶ T ↦ fun hf : f = a ↦
      CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) hf)
    h (show NativeCondensedModule.localPositivePower a 0 = a from rfl)
    (show localPositivePower a 0 = a from rfl)
  have hn := heq_of_eq (evaluateInitial_eq
    (U (NativeCondensedModule.localPositivePower a 0)) (U a)
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l)
      (show NativeCondensedModule.localPositivePower a 0 = a from rfl)) M θ)
  have hm := evaluateInitial_heq (U a) (congrArg U h) _ _ hc M θ
  exact hn.trans hm

private theorem chain_heq_pointwise {C : Type v} [Category.{w} C]
    {P Q : ℕ → C} (M : C) (h : P = Q)
    (i : P 0 ≅ M) (j : Q 0 ≅ M) (hi : HEq i j)
    (s : ∀ n, P (n + 1) ≅ P n) (t : ∀ n, Q (n + 1) ≅ Q n)
    (hs : ∀ n, HEq (s n) (t n)) (n : ℕ) :
    HEq (CondensedModule.isoChain P M i s n)
      (CondensedModule.isoChain Q M j t n) := by
  cases h
  cases eq_of_heq hi
  have hst : s = t := funext (fun k ↦ eq_of_heq (hs k))
  cases hst
  rfl

private theorem native_iterate_heq (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} (a : T ⟶ T) (M : NativeCondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (n : ℕ) : HEq (NativeCondensedModule.iterate l a M θ n)
      (CondensedModule.iterate l a M θ n) := by
  let U {S S' : Scheme.{u}} (f : S ⟶ S') :=
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f
  have hp : (fun k ↦ (U (NativeCondensedModule.localPositivePower a k)).obj M) =
      (fun k ↦ (U (localPositivePower a k)).obj M) :=
    congrArg (fun p : ℕ → (T ⟶ T) ↦ fun k ↦ (U (p k)).obj M)
      (native_positivePower_eq a)
  have hn := heq_of_eq (nativeIterateOne l a M θ n)
  have hs := heq_of_eq (sharedIterateOne l a M θ n).symm
  have hm := chain_heq_pointwise M hp _ _ (native_initial_heq l a M θ) _ _
    (native_step_heq l a M θ) n
  exact hn.trans (hm.trans hs)

private theorem mapIso_heq {C : Type v} {E : Type w} [Category C] [Category E]
    (F : C ⥤ E) {A A' B : C} (h : A = A')
    (i : A ≅ B) (j : A' ≅ B) (hi : HEq i j) : HEq (F.mapIso i) (F.mapIso j) := by
  cases h
  cases eq_of_heq hi
  rfl

private theorem composeIso_eq {C : Type v} [Category C] {A B B' E : C}
    (h : B = B') (i : A ≅ B) (j : B ≅ E) (i' : A ≅ B') (j' : B' ≅ E)
    (hi : HEq i i') (hj : HEq j j') : i ≪≫ j = i' ≪≫ j' := by
  cases h
  cases eq_of_heq hi
  cases eq_of_heq hj
  rfl

private theorem dependent_congr₂ {A : Sort v} {B : Sort w}
    {P : A → B → Prop} {Q : A → B → Sort*}
    (f : ∀ a b, P a b → Q a b) {a a' : A} {b b' : B}
    (ha : a = a') (hb : b = b') (h : P a b) (h' : P a' b') :
    HEq (f a b h) (f a' b' h') := by
  cases ha
  cases hb
  rfl

private theorem native_pointSections_eq (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] :
    NativeCondensedModule.pointSections l k = CondensedRing.pointSections l k := by
  unfold NativeCondensedModule.pointSections CondensedRing.pointSections
  unfold NativeCondensedModule.Modules CondensedRing.PointMod
  rfl

private theorem mapIso_eigenvalue_congr {C : Type v} [Category C]
    {R : Type w} [Field R] {F G : C ⥤ ModuleCat.{u} R} (h : F = G)
    {A : C} (i j : A ≅ A) (hij : i = j) (α : R) :
    Module.End.HasEigenvalue ((F.mapIso i).hom).hom α ↔
      Module.End.HasEigenvalue ((G.mapIso j).hom).hom α := by
  cases h
  cases hij
  rfl

private theorem native_shared_eigenvalue
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : NativeCondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (hN : z ≫ NativeCondensedModule.localPositivePower a n =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom n ≫ z)
    (hS : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (α : ULift.{u + 1} (PadicAlgCl l)) :
    Module.End.HasEigenvalue (NativeCondensedModule.operator l D a M θ z n hN).hom α ↔
      Module.End.HasEigenvalue (CondensedModule.operator l D a M θ z n hS).hom α := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let U {S S' : Scheme.{u}} (f : S ⟶ S') :=
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f
  let Z := U z
  have ha : NativeCondensedModule.localPositivePower a n = localPositivePower a n :=
    congrFun (native_positivePower_eq a) n
  have hb : NativeCondensedModule.localPositivePower
      (NativeCondensedModule.frobeniusPointIso D).hom n =
      localPositivePower (frobeniusPointIso D).hom n := by
    change NativeCondensedModule.localPositivePower (frobeniusPointIso D).hom n = _
    exact congrFun (native_positivePower_eq _) n
  let c (p : T ⟶ T) (q : Spec (.of D.k) ⟶ Spec (.of D.k))
      (h : z ≫ p = q ≫ z) :=
    (CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) q)
      p h).app M
  have hc : HEq (c _ _ hN) (c _ _ hS) := dependent_congr₂ c ha hb hN hS
  have hm : HEq (Z.mapIso (NativeCondensedModule.iterate l a M θ n))
      (Z.mapIso (CondensedModule.iterate l a M θ n)) :=
    mapIso_heq Z (congrArg (fun p ↦ (U p).obj M) ha) _ _
      (native_iterate_heq l a M θ n)
  have hi := composeIso_eq (congrArg (fun p ↦ Z.obj ((U p).obj M)) ha)
    (c _ _ hN) (Z.mapIso (NativeCondensedModule.iterate l a M θ n))
    (c _ _ hS) (Z.mapIso (CondensedModule.iterate l a M θ n)) hc hm
  unfold NativeCondensedModule.operator NativeCondensedModule.transport
    CondensedModule.operator CondensedModule.transport
  exact mapIso_eigenvalue_congr (native_pointSections_eq l D.k) _ _ hi α

private theorem closedEigenvalue_iff_shared
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : NativeL2.WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l)) :
    Module.End.HasEigenvalue (NativeL2.closedOperator D l X₀ M x i hi).hom α ↔
      Module.End.HasEigenvalue
        (CondensedModule.operator l D (D.geometricFrobenius X₀).hom M.carrier M.str
          (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
          (localClosedPoint_return D X₀ x i hi)).hom α := by
  unfold NativeL2.closedOperator
  exact native_shared_eigenvalue l D _ _ _ _ _ _ _ α

private theorem end_pow_hom {R : Type v} [CommRing R]
    (V : ModuleCat.{u + 1} R) (F : End V) (n : ℕ) :
    (F ^ n).hom = F.hom ^ n :=
  (ModuleCat.endRingEquiv V).map_pow F n

private theorem geometricLift_is_closedPoint
    (D : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (hz : z ≫ pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = 𝟙 _)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (hx : (z ≫ pullback.fst X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = x.val) :
    ∃ (i : X₀.left.residueField x.val →+* D.k)
      (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
      z = localClosedPoint D X₀ x i hi := by
  let a := z ≫ pullback.fst X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let i : X₀.left.residueField x.val ⟶ CommRingCat.of D.k :=
    (X₀.left.residueFieldCongr hx.symm).hom ≫
      X₀.left.descResidueField (Scheme.stalkClosedPointTo a)
  have ha : Spec.map i ≫ X₀.left.fromSpecResidueField x.val = a := by
    dsimp only [i]
    rw [Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField D.k X₀.left a
  have hi : i.hom.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k := by
    have hs : Spec.map (CommRingCat.ofHom
        (i.hom.comp (X₀.hom.residueFieldAlgebraMap x.val))) =
        Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp,
        X₀.hom.specMap_residueFieldAlgebraMap, CommRingCat.ofHom_hom, ← Category.assoc, ha]
      dsimp only [a]
      rw [Category.assoc, pullback.condition, ← Category.assoc, hz, Category.id_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.mp hs)
  refine ⟨i.hom, hi, ?_⟩
  apply pullback.hom_ext
  · simpa only [localClosedPoint, pullback.lift_fst, a, CommRingCat.ofHom_hom] using ha.symm
  · simpa only [localClosedPoint, pullback.lift_snd] using hz

private theorem eigenvalue_at_equal_lift
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : NativeL2.WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (hz : z = localClosedPoint D X₀ x i hi)
    (h : z ≫ localPositivePower (D.geometricFrobenius X₀).hom
        (localClosedPointDegree D X₀ x - 1) =
      localPositivePower (frobeniusPointIso D).hom
        (localClosedPointDegree D X₀ x - 1) ≫ z)
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue
      (CondensedModule.operator l D (D.geometricFrobenius X₀).hom M.carrier M.str z
        (localClosedPointDegree D X₀ x - 1) h).hom α) :
    Module.End.HasEigenvalue
      (CondensedModule.operator l D (D.geometricFrobenius X₀).hom M.carrier M.str
        (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
        (localClosedPoint_return D X₀ x i hi)).hom α := by
  subst z
  exact hα

/-- A finite etale direct image preserves punctual purity of the source Weil module.
Source: latest blueprint,
part-weights-riemann-hypothesis/sec-deligne-laumon-a1/sec-arbitrary-curves/
sk-lem-wft-finite-map,
`lem-a1-finite-map-purity.proof.md` (blueprint: lem-a1-finite-map-purity).
Proof: fix a closed target point y and a geometric lift. The finite-stalk formula
(lemma-weil-pbc-finite-stalk-formula) supplies the finite-sum shape, and the condensed
refinement lem-a1-condensed-finite-etale-stalk-cycles identifies this stalk with the
sum of source stalks, grouped into Frobenius-stable blocks indexed by closed points x.
Each block has residue degree e >= 1 and its e-th return is the local operator at x.
For a nonzero eigenvector of eigenvalue lambda, choose a nonzero block component and
then a nonzero stalk component in that block. The return equation makes this component
an eigenvector of the source local operator with eigenvalue lambda^e. Source purity
(def-weil-punctual-weights) gives the norm of iota(lambda^e) as q_x^(w/2). The residue
cardinality relation q_x = q_y^e therefore gives
|iota(lambda)|^e = (q_y^(w/2))^e. Since q_y > 0 and e >= 1, injectivity of the e-th
power on nonnegative reals gives the required norm. This holds for every closed y,
every geometric lift and every eigenvalue. Empty fibres and zero stalks contribute
no eigenvalues; no diagonalizability is needed.
-/
theorem pure_finiteEtaleLowerStar
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (g₀ : X₀ ⟶ Y₀) [IsFinite g₀.left] [Etale g₀.left]
    (M : NativeL2.WeilModule D l X₀)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (hpure : NativeL2.Pure D l X₀ M iota w) :
    NativeL2.Pure D l Y₀ (finiteEtaleLowerStar D l hl g₀ M) iota w := by
  sorry

end WeilConjectures.CondensedWeil
