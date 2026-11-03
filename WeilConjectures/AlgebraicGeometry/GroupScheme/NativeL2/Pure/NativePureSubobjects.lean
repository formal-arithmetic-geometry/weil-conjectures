/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Purity of native condensed Weil subobjects

Source: latest blueprint, lem-a1-mixed-direct-summand, Subsheaves.
(blueprint: lem-zl-native-pure-subobjects)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

private theorem isoChain_naturality {C : Type*} [Category* C]
    (A B : ℕ → C) (M N : C) (f : M ⟶ N)
    (iA : A 0 ≅ M) (iB : B 0 ≅ N)
    (sA : ∀ n, A (n + 1) ≅ A n) (sB : ∀ n, B (n + 1) ≅ B n)
    (v : ∀ n, A n ⟶ B n) (hi : v 0 ≫ iB.hom = iA.hom ≫ f)
    (hs : ∀ n, v (n + 1) ≫ (sB n).hom = (sA n).hom ≫ v n) (n : ℕ) :
    v n ≫ (isoChain B N iB sB n).hom = (isoChain A M iA sA n).hom ≫ f := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    change v (n + 1) ≫ ((sB n).hom ≫ (isoChain B N iB sB n).hom) =
      ((sA n).hom ≫ (isoChain A M iA sA n).hom) ≫ f
    rw [← Category.assoc, hs, Category.assoc, ih, Category.assoc]


private theorem evaluateInitial_naturality {C : Type*} [Category* C]
    (F G : C ⥤ C) (c : F ≅ G) (M N : C)
    (θ : G.obj M ≅ M) (η : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ η.hom = θ.hom ≫ f) :
    F.map f ≫ (evaluateInitial F G c N η).hom =
      (evaluateInitial F G c M θ).hom ≫ f := by
  dsimp only [evaluateInitial, Iso.trans_hom, Iso.app_hom]
  rw [NatTrans.naturality_assoc, hf, Category.assoc]

private theorem evaluateStep_naturality {C : Type*} [Category* C]
    (F G H : C ⥤ C) (c : H ≅ G ⋙ F) (M N : C)
    (θ : G.obj M ≅ M) (η : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ η.hom = θ.hom ≫ f) :
    H.map f ≫ (evaluateStep F G H c N η).hom =
      (evaluateStep F G H c M θ).hom ≫ F.map f := by
  dsimp only [evaluateStep, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp, hf, Functor.map_comp, Category.assoc]

private theorem iterate_naturality (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (a : T ⟶ T) (M N : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (η : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ η.hom =
      θ.hom ≫ f) (n : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a n)).map f ≫ (iterate l a N η n).hom =
      (iterate l a M θ n).hom ≫ f := by
  unfold iterate
  refine isoChain_naturality
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).obj M)
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).obj N) M N f _ _ _ _
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).map f) ?_ ?_ n
  · exact evaluateInitial_naturality _ _ _ M N θ η f hf
  · intro k
    unfold iterateStep
    exact evaluateStep_naturality _ _ _ _ M N θ η f hf


private theorem pointComparison_naturality (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (a : T ⟶ T)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (M N : Modules l T) (f : M ⟶ N) :
    let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n)
    let L := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
    let c := CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (localPositivePower (frobeniusPointIso D).hom n)) (localPositivePower a n) h
    (c.app M).hom ≫ L.map (P.map f) = L.map f ≫ (c.app N).hom := by
  dsimp only
  simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
    Functor.id_map, Iso.app_hom] using
    ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (localPositivePower (frobeniusPointIso D).hom n))
      (localPositivePower a n) h).hom.naturality f).symm

private theorem operator_naturality (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (a : T ⟶ T) (M N : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (η : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ η.hom =
      θ.hom ≫ f) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    operator l D a M θ z n h ≫
        (NativeCondensedModule.pointSections l D.k).map
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) =
      (NativeCondensedModule.pointSections l D.k).map
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) ≫
        operator l D a N η z n h := by
  let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n)
  let L := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  let c := CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
    (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
      (localPositivePower (frobeniusPointIso D).hom n)) (localPositivePower a n) h
  have hc := pointComparison_naturality l D a z n h M N f
  have hi := iterate_naturality l a M N θ η f hf n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (x ≫ (c.app M).hom ≫ L.map (iterate l a M θ n).hom) ≫ L.map f =
    (x ≫ L.map f) ≫ (c.app N).hom ≫ L.map (iterate l a N η n).hom
  calc
    (x ≫ (c.app M).hom ≫ L.map (iterate l a M θ n).hom) ≫ L.map f =
        x ≫ (c.app M).hom ≫ L.map ((iterate l a M θ n).hom ≫ f) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = x ≫ (c.app M).hom ≫ L.map (P.map f ≫ (iterate l a N η n).hom) := by rw [hi]
    _ = (x ≫ ((c.app M).hom ≫ L.map (P.map f))) ≫ L.map (iterate l a N η n).hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (x ≫ (L.map f ≫ (c.app N).hom)) ≫ L.map (iterate l a N η n).hom := by rw [hc]
    _ = (x ≫ L.map f) ≫ (c.app N).hom ≫ L.map (iterate l a N η n).hom := by
      simp only [Category.assoc]


private theorem eigenvalue_of_injective_intertwiner
    {K V W : Type*} [Field K] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] (A : Module.End K V) (B : Module.End K W)
    (v : V →ₗ[K] W) (hv : Function.Injective v)
    (h : ∀ x, v (A x) = B (v x)) (α : K) (hα : A.HasEigenvalue α) :
    B.HasEigenvalue α := by
  obtain ⟨a, ha⟩ := hα.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v a)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · calc
      B (v a) = v (A a) := (h a).symm
      _ = v (α • a) := congrArg v ha.apply_eq_smul
      _ = α • v a := v.map_smul α a
  · exact fun hzero => ha.2 (hv (hzero.trans v.map_zero.symm))

private theorem operator_eigenvalue_of_mono (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (a : T ⟶ T) (M N : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (η : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N) [Mono f]
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ η.hom =
      θ.hom ≫ f) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue (operator l D a M θ z n h).hom α) :
    Module.End.HasEigenvalue (operator l D a N η z n h).hom α := by
  let L := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙ pointSections l D.k
  let v := L.map f
  have hz : Mono ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) :=
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map_mono f
  have hv : Function.Injective v := by
    intro x y he
    change x ≫ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f =
      y ≫ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f at he
    exact (cancel_mono _).mp he
  apply eigenvalue_of_injective_intertwiner
    (operator l D a M θ z n h).hom (operator l D a N η z n h).hom v.hom hv _ α hα
  intro x
  exact congrArg (fun k => k.hom x) (operator_naturality l D a M N θ η f hf z n h)

/-- An equivariant subobject of a punctually pure native Weil module has the same weight.
Source: latest blueprint, lem-a1-mixed-direct-summand, Subsheaves.
(blueprint: lem-zl-native-pure-subobjects)

Proof: the actual local Frobenius operator is natural in the Weil module, by induction
through its pullback-comparison chain. Pullback to a geometric point and sections from the
coefficient unit preserve monomorphisms. Send an eigenvector along this injective fibre map;
it remains nonzero and has the same eigenvalue. Apply purity of the target.
-/
theorem Pure.of_mono
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {M N : WeilModule D l X₀} (f : M ⟶ N) [Mono f]
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) (hN : Pure D l X₀ N iota w) :
    Pure D l X₀ M iota w := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  intro x i hi α hα
  apply hN x i hi α
  have : Mono ((Endofunctor.IsoAlgebra.forget _).map f) :=
    (Endofunctor.IsoAlgebra.forget _).map_mono f
  unfold closedOperator at hα ⊢
  exact operator_eigenvalue_of_mono l D _ M.carrier N.carrier M.str N.str
    ((Endofunctor.IsoAlgebra.forget _).map f) f.hom.h _ _ _ α hα

end WeilConjectures.NativeL2
