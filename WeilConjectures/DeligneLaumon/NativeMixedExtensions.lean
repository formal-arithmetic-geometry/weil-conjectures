/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.Algebra.Field.ULift

/-! # Finite extensions of native mixed Weil modules

Source: latest blueprint, lem-zl-composition-weight-bound.proof.md, paragraph 2,
finite abutment filtration (blueprint: lem-zl-native-mixed-extensions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.DeligneLaumon

namespace NativeLocal

open NativeCondensedModule

private instance algebraicallyClosed (D : FiniteFieldDatum.{u}) : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

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
    (D : FiniteFieldDatum.{u}) {T : Scheme.{u}} (a : T ⟶ T)
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

set_option maxHeartbeats 2000000 in
-- The concrete module categories need more reduction for this naturality square.
private theorem operator_naturality (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M N : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (η : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ η.hom =
      θ.hom ≫ f) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    operator l D a M θ z n h ≫
        (pointSections l D.k).map
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) =
      (pointSections l D.k).map
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


private theorem eigenvalue_of_mono
    {K : Type*} [Field K] {M N : ModuleCat K}
    (A : M ⟶ M) (B : N ⟶ N) (f : M ⟶ N) [Mono f]
    (hn : A ≫ f = f ≫ B) {α : K} (hα : Module.End.HasEigenvalue A.hom α) :
    Module.End.HasEigenvalue B.hom α := by
  have ht : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).mp inferInstance
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hv
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := f.hom v)
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, (map_ne_zero_iff _ ht).mpr hv.2⟩
  have hnv := congrArg (fun k ↦ k.hom v) hn
  change f.hom (A.hom v) = B.hom (f.hom v) at hnv
  exact hnv.symm.trans ((congrArg f.hom hv.1).trans (map_smul _ _ _))

private theorem closedOperator_eq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (F : NativeL2.WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    NativeL2.closedOperator D l X₀ F x i hi =
      operator l D (D.geometricFrobenius X₀).hom F.carrier F.str
        (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
        (localClosedPoint_return D X₀ x i hi) := by
  unfold NativeL2.closedOperator
  rfl

private theorem fibre_map_mono
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} {M N : Modules l T} (f : M ⟶ N) [Mono f]
    (z : Spec (.of D.k) ⟶ T) :
    Mono ((pointSections l D.k).map
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f)) := by
  have : (pointSections l D.k).PreservesMonomorphisms := by
    unfold pointSections
    infer_instance
  exact Functor.map_mono _ _

private theorem native_map_mono
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {F G : NativeL2.WeilModule D l X₀} (f : F ⟶ G) [Mono f] : Mono f.hom.f :=
  (CategoryTheory.Endofunctor.IsoAlgebra.forget _).map_mono f

private theorem operator_eigenvalue_of_mono (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) {T : Scheme.{u}} (a : T ⟶ T) (M N : Modules l T)
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
  let t := (pointSections l D.k).map
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f)
  have : Mono t := fibre_map_mono D l f z
  exact eigenvalue_of_mono _ _ t (operator_naturality l D a M N θ η f hf z n h) hα

private theorem pure_of_mono
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {F G : NativeL2.WeilModule D l X₀} (f : F ⟶ G) [Mono f]
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hG : NativeL2.Pure D l X₀ G iota w) :
    NativeL2.Pure D l X₀ F iota w := by
  intro x i hi α hα
  rw [closedOperator_eq] at hα
  apply hG x i hi α
  rw [closedOperator_eq]
  have : Mono f.hom.f := native_map_mono D l X₀ f
  exact operator_eigenvalue_of_mono l D (D.geometricFrobenius X₀).hom
    F.carrier G.carrier F.str G.str f.hom.f f.hom.h _ _ _ α hα

end NativeLocal

private theorem native_constructible_closure
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    let R : ObjectProperty (NativeL2.WeilModule D l X₀) := fun M ↦
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left M.carrier
    R.ContainsZero ∧ R.IsClosedUnderIsomorphisms ∧ R.IsClosedUnderKernels ∧
      R.IsClosedUnderCokernels ∧ R.IsClosedUnderExtensions := by
  let X := (D.geometricFiber X₀).left
  have : LocallyOfFiniteType (D.geometricFiber X₀).hom := by
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom _))
  have : QuasiCompact (D.geometricFiber X₀).hom := by
    exact inferInstanceAs (QuasiCompact (pullback.snd X₀.hom _))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (D.geometricFiber X₀).hom
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (D.geometricFiber X₀).hom
  have : IsNoetherian X := ⟨⟩
  let P : ObjectProperty (NativeCondensedModule.Modules l X) :=
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X
  let U := CategoryTheory.Endofunctor.IsoAlgebra.forget
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
  let R : ObjectProperty (NativeL2.WeilModule D l X₀) := P.inverseImage U
  obtain ⟨hk, hc, he, ha, _⟩ :=
    (coefficientHeart_closure l (Profinite.padicAlgClCondensedRing l) (Or.inr rfl)).2 X
  have : P.IsClosedUnderKernels := hk
  have : P.IsClosedUnderCokernels := hc
  have : P.IsClosedUnderExtensions := he
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined (Profinite.padicAlgClRingObj l) X).1
  have : Abelian P.FullSubcategory := ha.some
  obtain ⟨Z, hz⟩ := Limits.HasZeroObject.zero (C := P.FullSubcategory)
  have : P.ContainsZero := ⟨⟨Z.obj, P.ι.map_isZero hz, Z.property⟩⟩
  have : R.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, c, h, hf⟩
    exact P.prop_of_iso (U.mapIso ((kernelIsKernel f).conePointUniqueUpToIso h))
      (P.prop_of_iso (PreservesKernel.iso U f).symm
        (P.prop_kernel (U.map f) hf.1 hf.2))⟩
  have : R.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, c, h, hf⟩
    exact P.prop_of_iso (U.mapIso ((cokernelIsCokernel f).coconePointUniqueUpToIso h))
      (P.prop_of_iso (PreservesCokernel.iso U f).symm
        (P.prop_cokernel (U.map f) hf.1 hf.2))⟩
  change R.ContainsZero ∧ R.IsClosedUnderIsomorphisms ∧ R.IsClosedUnderKernels ∧
    R.IsClosedUnderCokernels ∧ R.IsClosedUnderExtensions
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem filtration_with_constructible
    {C : Type*} [Category* C] [Abelian C] (P Q : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderExtensions] [Q.IsClosedUnderIsomorphisms] (M : C) :
    (P ⊓ Q).filtrationClosure M ↔
      ∃ (n : ℕ) (G : Fin (n + 1) → C)
        (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
        (∀ i, P (G i)) ∧ IsZero (G 0) ∧ Nonempty (G (Fin.last n) ≅ M) ∧
          (∀ i, Mono (φ i)) ∧ ∀ i, Q (cokernel (φ i)) := by
  constructor
  · intro h
    obtain ⟨n, G, φ, hz, he, hm, hp⟩ := ObjectProperty.filtrationClosure_iff.mp h
    have hG : ∀ (j : ℕ) (hj : j < n + 1), P (G ⟨j, hj⟩) := by
      intro j
      induction j with
      | zero => exact fun _ ↦ P.prop_of_isZero hz
      | succ j ih =>
        intro hj
        let k : Fin n := ⟨j, by omega⟩
        let : Mono (φ k) := hm k
        exact P.prop_X₂_of_shortExact (show (ShortComplex.mk (φ k)
            (cokernel.π (φ k)) (cokernel.condition _)).ShortExact from
              ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)⟩)
          (ih (by omega)) (hp k).1
    exact ⟨n, G, φ, fun i ↦ hG i i.isLt, hz, he, hm, fun i ↦ (hp i).2⟩
  · rintro ⟨n, G, φ, hc, hz, he, hm, hp⟩
    exact ObjectProperty.filtrationClosure_iff.mpr
      ⟨n, G, φ, hz, he, hm, fun i ↦
        ⟨P.prop_cokernel (φ i) (hc _) (hc _), hp i⟩⟩

/-- Zero and finite extensions preserve the upper bound for native mixed Weil modules.
Source: latest blueprint, lem-zl-composition-weight-bound.proof.md, paragraph 2,
and lem-a1-mixed-direct-summand.proof.md, extension argument.
(blueprint: lem-zl-native-mixed-extensions).

Proof: Exact forgetting sends a short exact Weil sequence to a short exact sequence
of ordinary modules. The constant-model constructible coefficient heart is closed
under extensions and cokernels. Purity is invariant under Weil isomorphisms: the
canonical local Frobenius operator is natural, and an injective equivariant fibre
map sends a nonzero eigenvector to a nonzero eigenvector. Let P be constructibility
and Q the existence of a pure weight at most w. Native mixedness is exactly the
finite filtration closure of P and Q. In one direction all filtration terms are
constructible by induction on their short exact cokernel sequences; in the other
direction the cokernels are constructible. The general finite filtration closure
is closed under extensions, by pulling back a filtration of the quotient and
splicing with a filtration of the subobject. The length-zero filtration handles
zero, including the empty scheme. -/
theorem nativeMixedExtensions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) :
    (∀ M : NativeL2.WeilModule D l X₀, IsZero M → NativeL2.Mixed D l X₀ M iota w) ∧
      ObjectProperty.IsClosedUnderExtensions
        (fun M : NativeL2.WeilModule D l X₀ ↦ NativeL2.Mixed D l X₀ M iota w) := by
  let R : ObjectProperty (NativeL2.WeilModule D l X₀) := fun M ↦
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier
  let Q : ObjectProperty (NativeL2.WeilModule D l X₀) := fun M ↦
    ∃ v : ℝ, v ≤ w ∧ NativeL2.Pure D l X₀ M iota v
  obtain ⟨hz, hi, hk, hc, he⟩ := native_constructible_closure D l X₀
  have : R.ContainsZero := hz
  have : R.IsClosedUnderIsomorphisms := hi
  have : R.IsClosedUnderKernels := hk
  have : R.IsClosedUnderCokernels := hc
  have : R.IsClosedUnderExtensions := he
  have : Q.IsClosedUnderIsomorphisms := ⟨by
    intro M N e h
    obtain ⟨v, hv, hp⟩ := h
    exact ⟨v, hv, NativeLocal.pure_of_mono D l X₀ e.inv iota v hp⟩⟩
  have hm (M : NativeL2.WeilModule D l X₀) :
      (R ⊓ Q).filtrationClosure M ↔ NativeL2.Mixed D l X₀ M iota w :=
    filtration_with_constructible R Q M
  constructor
  · intro M hz
    exact (hm M).mp (.of_isZero hz)
  · refine ⟨fun {S} hS h₁ h₃ ↦ ?_⟩
    exact (hm S.X₂).mp ((R ⊓ Q).filtrationClosure.prop_X₂_of_shortExact
      hS ((hm _).mpr h₁) ((hm _).mpr h₃))

end WeilConjectures.DeligneLaumon
