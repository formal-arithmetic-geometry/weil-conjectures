/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointSectionsFiniteReductionData
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits

/-! # Ordinary finite quotient sections and flatness

Source: Stacks Tags 093J, 03EK and 00HD; steps 2--3 of
`lem-trf-point-sections-finite-reduction`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

private theorem constantSection_bijective (k A : Type u) [Field k] [IsAlgClosed k]
    [CommRing A] : Function.Bijective (pointConstantSectionMap k A) := by
  exact AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso (Iso.refl _)
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} A)))

private theorem sections_flat (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (M : pointFiniteReductionSheaves k l E n)
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pointFiniteReductionRingSheaf k l E n) M) :
    Module.Flat (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
      ((pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj M) := by
  let e := RingEquiv.ofBijective (pointConstantSectionMap k
    (Padic.coefficientExtensionRing l E n))
    (constantSection_bijective k (Padic.coefficientExtensionRing l E n))
  apply Module.Flat.iff_forall_isTrivialRelation.2
  intro m a x hx
  obtain ⟨S, hS, h⟩ :=
    SheafOfModules.local_equationalCriterion_of_isFlatOnSite.{u + 1, u, u + 1, u + 1}
    (pointFiniteReductionRingSheaf k l E n) M hM (ProEt.mk (𝟙 (Spec (.of k)))) m
    (fun i ↦ e (a i)) x hx
  obtain ⟨q, b, t, hxt, hab⟩ := h _ (𝟙 _) (ProEt.id_mem_of_mem_topology_of_iso
    (Iso.refl (Spec (.of k))) hS)
  refine ⟨q, fun i j ↦ e.symm (b i j), t, ?_, ?_⟩
  · intro i
    have hh := hxt i
    simp only [op_id, PresheafOfModules.map_id] at hh
    change x i = ∑ q, b i q • t q at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro q hq
    change e (e.symm (b i q)) • t q = b i q • t q
    rw [e.apply_symm_apply]
  · intro j
    apply e.injective
    have hh := hab j
    simp only [op_id] at hh
    rw [(pointFiniteReductionRingSheaf k l E n).obj.map_id] at hh
    simpa only [map_sum, map_mul, RingEquiv.apply_symm_apply, map_zero,
      CommRingCat.id_apply] using hh

private def tensorSquareIso {A B R S : Type (u + 1)}
    [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    (f : A →+* B) (g : R →+* S) (en : A ≃+* R) (ej : B ≃+* S)
    (hs : ∀ a, ej (f a) = g (en a)) (M : ModuleCat.{u + 1} R) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj
        ((ModuleCat.restrictScalars (en : A →+* R)).obj M) ≅
      (ModuleCat.restrictScalars (ej : B →+* S)).obj
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} g).obj M) := by
  letI := g.toAlgebra
  letI := RingHomInvPair.of_ringEquiv en
  letI := RingHomInvPair.symm (en : A →+* R) (en.symm : R →+* A)
  let e₁ : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) ≃ₛₗ[(en : A →+* R)]
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of S S)) :=
    { ej.toAddEquiv with
      map_smul' := fun a b ↦ by
        change ej (f a * (show B from b)) = g (en a) * ej (show B from b)
        rw [map_mul, hs] }
  let e₂ : ((ModuleCat.restrictScalars (en : A →+* R)).obj M) ≃ₛₗ[(en : A →+* R)] M :=
    { AddEquiv.refl _ with map_smul' := fun _ _ ↦ rfl }
  let et := TensorProduct.congr e₁ e₂
  let X := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj
    ((ModuleCat.restrictScalars (en : A →+* R)).obj M)
  let Y := (ModuleCat.restrictScalars (ej : B →+* S)).obj
    ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} g).obj M)
  suffices e : X ≃ₗ[B] Y from e.toModuleIso
  refine
    { toFun := fun x ↦ et x
      invFun := fun x ↦ et.symm x
      left_inv := et.left_inv
      right_inv := et.right_inv
      map_add' := fun x y ↦ et.map_add x y
      map_smul' := ?_ }
  intro b x
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul c m =>
    change ej (b * (show B from c)) ⊗ₜ[R, g] m =
      ej b • (ej (show B from c) ⊗ₜ[R, g] m)
    rw [map_mul, TensorProduct.smul_tmul']
    rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private def constantSectionEquiv (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A] :=
  RingEquiv.ofBijective (pointConstantSectionMap k A) (constantSection_bijective k A)

private def sheafificationFinalIso (k : Type u) [Field k] [IsAlgClosed k]
    (R : Sheaf (ProEt.topology (Spec (.of k))) RingCat.{u + 1})
    (P : PresheafOfModules.{u + 1} R.obj) :
    P.obj (op (ProEt.mk (𝟙 (Spec (.of k))))) ≅
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).val.obj
        (op (ProEt.mk (𝟙 (Spec (.of k))))) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P
  let φ : P.obj U ⟶ ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).val.obj U :=
    ModuleCat.ofHom (X := P.obj U)
      (Y := ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).val.obj U)
      { toFun := fun x ↦ η.app U x
        map_add' := fun x y ↦ (η.app U).hom.map_add x y
        map_smul' := fun a x ↦ (η.app U).hom.map_smul a x }
  have hφ : Function.Bijective φ :=
    AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso (Iso.refl _) P.presheaf
  exact (LinearEquiv.ofBijective φ.hom hφ).toModuleIso

private theorem constantSection_natural (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n j : ℕ) (h : j ≤ n)
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) :
    pointConstantSectionMap k (Padic.coefficientExtensionRing l E j)
        (pointFiniteReductionRingMap l E n j h a) =
      ((pointFiniteReductionSheafMap k l E n j h).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom
          (pointConstantSectionMap k (Padic.coefficientExtensionRing l E n) a) := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (ProEt.topology (Spec (.of k)))
      ((Functor.const _).map (CommRingCat.ofHom
        (pointFiniteReductionRingMap l E n j h)))) _) a

attribute [local irreducible] pointFiniteReductionSheafExistence pointFiniteReductionSheafModel

private def ordinaryComponent (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n j : ℕ) (h : j ≤ n)
    (M : pointFiniteReductionSheaves k l E n) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointFiniteReductionRingMap l E n j h)).obj
        ((pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj M) ≅
      (pointFiniteSections k (Padic.coefficientExtensionRing l E j)).obj
        ((pointFiniteReductionSheafExtension k l E n j h).obj M) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let φ := pointFiniteReductionSheafMap k l E n j h
  let en := constantSectionEquiv k (Padic.coefficientExtensionRing l E n)
  let ej := constantSectionEquiv k (Padic.coefficientExtensionRing l E j)
  let e₁ := tensorSquareIso.{u} (pointFiniteReductionRingMap l E n j h)
    (φ.hom.app U).hom en ej (constantSection_natural k l E n j h) (M.val.obj U)
  let R := SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
    (ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E j)
  let e₂ := (ModuleCat.restrictScalars
    (pointConstantSectionMap k (Padic.coefficientExtensionRing l E j))).mapIso
    (sheafificationFinalIso k R (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M))
  let e₃ := (pointFiniteSections k (Padic.coefficientExtensionRing l E j)).mapIso
    (eqToIso ((pointFiniteReductionSheafModel k l E n j h).objEq M)).symm
  exact e₁ ≪≫ e₂ ≪≫ e₃

private theorem ordinaryComponent_tmul (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n j : ℕ) (h : j ≤ n)
    (M : pointFiniteReductionSheaves k l E n)
    (b : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
    (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj M) :
    (ordinaryComponent k l E n j h M).hom
        (b ⊗ₜ[_, pointFiniteReductionRingMap l E n j h] x) =
      b • pointFiniteReductionSectionGenerator k l E n j h M x := by
  dsimp only [ordinaryComponent, Iso.trans_hom, Functor.mapIso_hom,
    ModuleCat.comp_apply]
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let φ := pointFiniteReductionSheafMap k l E n j h
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
      (ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E j)).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)
  let T := (eqToHom
    ((pointFiniteReductionSheafModel k l E n j h).objEq M).symm).val.app U
  let β := pointConstantSectionMap k (Padic.coefficientExtensionRing l E j) b
  change T (η.app U (β ⊗ₜ[_, (φ.hom.app U).hom] x)) =
    β • T (η.app U ((1 : (pointFiniteReductionRingSheaf k l E j).obj.obj U) ⊗ₜ x))
  let t : (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).obj U :=
    (1 : (pointFiniteReductionRingSheaf k l E j).obj.obj U) ⊗ₜ x
  have he : (β ⊗ₜ[_, (φ.hom.app U).hom] x :
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).obj U) = β • t := by
    let c : (pointFiniteReductionRingSheaf k l E j).obj.obj U :=
      (show (pointFiniteReductionRingSheaf k l E j).obj.obj U from β) *
        (1 : (pointFiniteReductionRingSheaf k l E j).obj.obj U)
    change _ = (c ⊗ₜ[_, (φ.hom.app U).hom] x :
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).obj U)
    have hc : c = (show (pointFiniteReductionRingSheaf k l E j).obj.obj U from β) :=
      mul_one _
    rw [hc]
  exact (congrArg (fun z ↦ T (η.app U z)) he).trans
    ((congrArg T ((η.app U).hom.map_smul β t)).trans
      (T.hom.map_smul β (η.app U t)))

private theorem ordinaryComponent_naturality (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n j : ℕ) (h : j ≤ n)
    {M N : pointFiniteReductionSheaves k l E n} (a : M ⟶ N) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointFiniteReductionRingMap l E n j h)).map
        ((pointFiniteSections k (Padic.coefficientExtensionRing l E n)).map a) ≫
        (ordinaryComponent k l E n j h N).hom =
      (ordinaryComponent k l E n j h M).hom ≫
        (pointFiniteSections k (Padic.coefficientExtensionRing l E j)).map
          ((pointFiniteReductionSheafExtension k l E n j h).map a) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let φ := pointFiniteReductionSheafMap k l E n j h
  let R := SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
    (ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E j)
  let V := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U
  let eM := V.mapIso (eqToIso
    ((pointFiniteReductionSheafModel k l E n j h).objEq M))
  let eN := V.mapIso (eqToIso
    ((pointFiniteReductionSheafModel k l E n j h).objEq N))
  have hmap : (pointFiniteReductionSheafExtension k l E n j h).map a ≫
      eqToHom ((pointFiniteReductionSheafModel k l E n j h).objEq N) =
    eqToHom ((pointFiniteReductionSheafModel k l E n j h).objEq M) ≫
      SheafOfModules.changeOfRingsHom φ M a := by
    apply (Iso.eq_comp_inv (eqToIso
      ((pointFiniteReductionSheafModel k l E n j h).objEq N))).1
    exact (pointFiniteReductionSheafModel k l E n j h).mapEq a
  have hmapV := congrArg V.map hmap
  simp only [Functor.map_comp] at hmapV
  let p : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ N :=
    { app := fun W ↦
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (φ.hom.app W).hom).map (a.val.app W)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M a }
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have hη := adj.unit.naturality p
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  simp only [ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul,
    ordinaryComponent_tmul, one_smul]
  rw [ordinaryComponent_tmul k l E n j h N 1
    ((pointFiniteSections k (Padic.coefficientExtensionRing l E n)).map a x), one_smul]
  apply (ConcreteCategory.bijective_of_isIso eN.hom).injective
  let t : (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).obj U :=
    (1 : (pointFiniteReductionRingSheaf k l E j).obj.obj U) ⊗ₜ
      (show M.val.obj U from x)
  have hηx := congrArg (fun f ↦ f.app U t) hη
  have ht := ConcreteCategory.congr_hom hmapV
  let tN : (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ N).obj U :=
    (1 : (pointFiniteReductionRingSheaf k l E j).obj.obj U) ⊗ₜ
      (a.val.app U (show M.val.obj U from x))
  let yM := ((adj.unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U) t
  let yN := ((adj.unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ N)).app U) tN
  have hxy : yN = (V.map (SheafOfModules.changeOfRingsHom φ M a)) yM := by
    change (adj.unit.app _).app U ((p.app U) t) =
      (((PresheafOfModules.sheafification (𝟙 R.obj)).map p).val.app U) yM at hηx
    have hp : (p.app U) t = tN := by rfl
    rw [hp] at hηx
    exact hηx
  have hcM : eM.hom (eM.inv yM) = yM :=
    ConcreteCategory.congr_hom eM.inv_hom_id yM
  have hcN : eN.hom (eN.inv yN) = yN :=
    ConcreteCategory.congr_hom eN.inv_hom_id yN
  change eN.hom (eN.inv yN) =
    eN.hom ((V.map ((pointFiniteReductionSheafExtension k l E n j h).map a)) (eM.inv yM))
  calc
    _ = yN := hcN
    _ = (V.map (SheafOfModules.changeOfRingsHom φ M a)) yM := hxy
    _ = (V.map (SheafOfModules.changeOfRingsHom φ M a)) (eM.hom (eM.inv yM)) :=
      congrArg _ hcM.symm
    _ = _ := (ht (eM.inv yM)).symm

/-- Exact point sections preserve flatness over finite coefficient rings and commute with
ordinary quotient extension by the actual quotient-section map.
Source: Stacks Tags 093J, 03EK and 00HD, blueprint steps 2--3
(blueprint: lem-trf-point-finite-reduction-section-algebra).

Proof: every covering sieve of the final pro-etale object of Spec k contains its
identity. Hence sheafification is bijective on final sections, including ring
sheafification; the constant section map is a ring equivalence. The local
equational criterion for a flat module sheaf therefore supplies its witnesses
on the identity itself. Transporting their coefficients through the ring
equivalence proves the module equational criterion for its sections. For ordinary
extension, transport the tensor product through the source and target constant
section equivalences. Final sections of the sheafification of the resulting
presheaf tensor equal its unsheafified final value. Compose these identifications
with the chosen extension functor's object equations. Naturality of sheafification
and its unit proves naturality; on b tensor x the map is b times the actual
sheafification-unit section of x. The argument includes n=j, the zero quotient
at j=0, and arbitrary (not necessarily finitely generated) modules.
-/
theorem pointFiniteReductionSectionAlgebra (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    (∀ (n : ℕ) (M : pointFiniteReductionSheaves k l E n),
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := pointFiniteReductionRingSheaf k l E n) M →
      Module.Flat (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        ((pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj M)) ∧
    ∀ (n j : ℕ) (h : j ≤ n),
      ∃ e : pointFiniteSections k (Padic.coefficientExtensionRing l E n) ⋙
          ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointFiniteReductionRingMap l E n j h) ≅
        pointFiniteReductionSheafExtension k l E n j h ⋙
          pointFiniteSections k (Padic.coefficientExtensionRing l E j),
        ∀ (M : pointFiniteReductionSheaves k l E n)
          (b : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
          (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj M),
          e.hom.app M (b ⊗ₜ[_, pointFiniteReductionRingMap l E n j h] x) =
            b • pointFiniteReductionSectionGenerator k l E n j h M x := by
  refine ⟨sections_flat k l E, ?_⟩
  intro n j h
  refine ⟨NatIso.ofComponents (ordinaryComponent k l E n j h)
    (ordinaryComponent_naturality k l E n j h), ?_⟩
  exact ordinaryComponent_tmul k l E n j h

end WeilConjectures
