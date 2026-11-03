/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import Mathlib.Algebra.Field.ULift

/-!
# Isomorphism invariance of native punctual purity

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 5,
transport of the pure quotients in a finite Weil filtration.
(blueprint: lem-zl-native-pure-iso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeL2
open NativeCondensedModule

section Naturality

attribute [local irreducible] NativeCondensedModule.pointSections
  NativeCondensedModule.pointScalarsOp NativeCondensedModule.pointUnitEndRingHom
  CondensedRing.upperStar

-- These private naturality proofs are preserved from the source of L2Upper.
private theorem chain_naturality {C : Type v} [Category.{w} C]
    (G : C ⥤ C) (F : ℕ → C ⥤ C) (c₀ : F 0 ≅ G)
    (c : ∀ n, F (n + 1) ≅ G ⋙ F n)
    {A B : C} (θA : G.obj A ≅ A) (θB : G.obj B ≅ B)
    (f : A ⟶ B) (hf : G.map f ≫ θB.hom = θA.hom ≫ f) (n : ℕ) :
    (F n).map f ≫ (isoChain (fun n ↦ (F n).obj B) B
      (evaluateInitial (F 0) G c₀ B θB)
      (fun n ↦ evaluateStep (F n) G (F (n + 1)) (c n) B θB) n).hom =
    (isoChain (fun n ↦ (F n).obj A) A
      (evaluateInitial (F 0) G c₀ A θA)
      (fun n ↦ evaluateStep (F n) G (F (n + 1)) (c n) A θA) n).hom ≫ f := by
  induction n with
  | zero =>
    change (F 0).map f ≫ c₀.hom.app B ≫ θB.hom =
      (c₀.hom.app A ≫ θA.hom) ≫ f
    rw [← Category.assoc, c₀.hom.naturality, Category.assoc, hf, Category.assoc]
  | succ n ih =>
    have hs : (F (n + 1)).map f ≫
        (evaluateStep (F n) G (F (n + 1)) (c n) B θB).hom =
        (evaluateStep (F n) G (F (n + 1)) (c n) A θA).hom ≫ (F n).map f := by
      change (F (n + 1)).map f ≫ (c n).hom.app B ≫ (F n).map θB.hom =
        ((c n).hom.app A ≫ (F n).map θA.hom) ≫ (F n).map f
      rw [← Category.assoc, (c n).hom.naturality]
      simp only [Functor.comp_map, Category.assoc]
      rw [← (F n).map_comp, hf, (F n).map_comp]
    change (F (n + 1)).map f ≫
      (evaluateStep (F n) G (F (n + 1)) (c n) B θB).hom ≫ _ =
      ((evaluateStep (F n) G (F (n + 1)) (c n) A θA).hom ≫ _) ≫ f
    dsimp only [isoChain] at ih
    rw [← Category.assoc, hs, Category.assoc, ih, ← Category.assoc]

private theorem iterate_naturality
    (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (a : T ⟶ T)
    {A B : Modules l T}
    (θA : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj A ≅ A)
    (θB : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj B ≅ B)
    (f : A ⟶ B)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ θB.hom =
      θA.hom ≫ f) (n : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (NativeCondensedModule.localPositivePower a n)).map f ≫
      (iterate l a B θB n).hom = (iterate l a A θA n).hom ≫ f := by
  unfold iterate iterateStep
  exact chain_naturality _ _ _ _ θA θB f hf n



private theorem transport_naturality_abstract
    {C E H : Type*} [Category C] [Category E] [Category H]
    (Q : C ⥤ C) (Z : C ⥤ E) (P : E ⥤ H) (c : Z ⋙ 𝟭 E ≅ Q ⋙ Z)
    {A B : C} (θA : Q.obj A ≅ A) (θB : Q.obj B ≅ B) (f : A ⟶ B)
    (hf : Q.map f ≫ θB.hom = θA.hom ≫ f) :
    P.map (Z.map f) ≫ (P.mapIso (c.app B ≪≫ Z.mapIso θB)).hom =
      (P.mapIso (c.app A ≪≫ Z.mapIso θA)).hom ≫ P.map (Z.map f) := by
  change P.map (Z.map f) ≫ P.map (c.hom.app B ≫ Z.map θB.hom) =
    P.map (c.hom.app A ≫ Z.map θA.hom) ≫ P.map (Z.map f)
  rw [← P.map_comp, ← P.map_comp]
  apply congrArg P.map
  have hc : Z.map f ≫ c.hom.app B = c.hom.app A ≫ Z.map (Q.map f) := by
    simpa only [Functor.comp_map, Functor.id_map] using c.hom.naturality f
  rw [← Category.assoc, hc]
  simp only [Category.assoc]
  rw [← Z.map_comp, hf, Z.map_comp]

private def nativeFibreMap (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) {A B : Modules l T} (f : A ⟶ B) :
    fibre l D A z ⟶ fibre l D B z :=
  (pointSections l D.k).map
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f)

private theorem operator_eq_transport
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ NativeCondensedModule.localPositivePower a n =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom n ≫ z) :
    operator l D a M θ z n h = (transport l D a M θ z z n h).hom := rfl

private theorem transport_eq_mapIso
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ NativeCondensedModule.localPositivePower a n =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom n ≫ z) :
    transport l D a M θ z z n h =
      letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
      (pointSections l D.k).mapIso
        ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
          (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
            (NativeCondensedModule.localPositivePower
              (NativeCondensedModule.frobeniusPointIso D).hom n))
          (NativeCondensedModule.localPositivePower a n) h).app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso
            (iterate l a M θ n)) := rfl


private theorem operator_naturality
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) {A B : Modules l T}
    (θA : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj A ≅ A)
    (θB : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj B ≅ B)
    (f : A ⟶ B)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ θB.hom =
      θA.hom ≫ f)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ NativeCondensedModule.localPositivePower a n =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom n ≫ z) :
    nativeFibreMap l D z f ≫ operator l D a B θB z n h =
    operator l D a A θA z n h ≫
      nativeFibreMap l D z f := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let Z := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  let Q := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (NativeCondensedModule.localPositivePower a n)
  let c := CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
    (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
      (NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom n))
    (NativeCondensedModule.localPositivePower a n) h
  dsimp only [nativeFibreMap]
  rw [operator_eq_transport, operator_eq_transport,
    transport_eq_mapIso, transport_eq_mapIso]
  exact transport_naturality_abstract Q Z (pointSections l D.k) c
    (iterate l a A θA n) (iterate l a B θB n) f
    (iterate_naturality l a θA θB f hf n)


private def nativeWeilFibre (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    WeilModule D l X₀ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)) :=
  CategoryTheory.Endofunctor.IsoAlgebra.forget _ ⋙
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
      NativeCondensedModule.pointSections l D.k

set_option maxHeartbeats 1600000 in
-- The concrete fibre conversion checks pullback and module-category instances.
private theorem closedOperator_naturality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    {N N' : WeilModule D l X₀} (f : N ⟶ N') :
    (nativeWeilFibre D l X₀ (localClosedPoint D X₀ x i hi)).map f ≫
        closedOperator D l X₀ N' x i hi =
      closedOperator D l X₀ N x i hi ≫
        (nativeWeilFibre D l X₀ (localClosedPoint D X₀ x i hi)).map f := by
  unfold closedOperator
  exact operator_naturality l D (D.geometricFrobenius X₀).hom N.str N'.str f.hom.f
    f.hom.h (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
    (localClosedPoint_return D X₀ x i hi)



end Naturality

private theorem eigenvalue_transport {K V W : Type*} [Field K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (A : Module.End K V) (B : Module.End K W) (e : V ≃ₗ[K] W)
    (h : ∀ v, B (e v) = e (A v)) (α : K)
    (hα : A.HasEigenvalue α) : B.HasEigenvalue α := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := e v)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · rw [h, hv.apply_eq_smul, map_smul]
  · exact fun hz ↦ hv.2 (e.injective (hz.trans (map_zero e).symm))

set_option maxHeartbeats 400000 in
-- Pin the fibre objects before checking the local-operator comparison.
/-- Isomorphic native Weil objects have the same punctual pure weights.
Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 5
(blueprint: lem-zl-native-pure-iso).
Proof: evaluate the Weil isomorphism at any closed geometric lift. Naturality
of the local Frobenius operator makes this linear isomorphism intertwine the
operators. It carries a nonzero eigenvector to a nonzero eigenvector with the
same eigenvalue, and its inverse proves the converse. The residue field and
weight equation are unchanged. No finite-dimensionality or constructibility is
needed; zero fibres and empty schemes are included. -/
theorem pure_iso_iff (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {M N : WeilModule D l X₀} (e : M ≅ N) (iota : PadicAlgCl l →+* ℂ) (w : ℝ) :
    Pure D l X₀ M iota w ↔ Pure D l X₀ N iota w := by
  suffices h : ∀ {A B : WeilModule D l X₀}, (A ≅ B) →
      Pure D l X₀ B iota w → Pure D l X₀ A iota w from
    ⟨h e.symm, h e⟩
  intro A B e hB x i hi α hα
  let F := nativeWeilFibre D l X₀ (localClosedPoint D X₀ x i hi)
  let ef := (F.mapIso e).toLinearEquiv
  have hn := closedOperator_naturality D l X₀ x i hi e.hom
  have he (v : F.obj A) :
      (closedOperator D l X₀ B x i hi).hom (ef v) =
        ef ((closedOperator D l X₀ A x i hi).hom v) := by
    exact congrArg (fun f : F.obj A ⟶ F.obj B ↦ f.hom v) hn
  exact hB x i hi α (eigenvalue_transport
    (closedOperator D l X₀ A x i hi).hom (closedOperator D l X₀ B x i hi).hom
    ef he α hα)

end WeilConjectures.NativeL2
