/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import WeilConjectures.RingTheory.StrictHenselizationPresentationProperties
import Mathlib.Algebra.Ring.ULift
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered

/-!
# Strict henselization after a local base change

Source: Stacks Project, Algebra, Tag 08HV
(blueprint: lem-dl-a1-smooth-local-branch-strict-base-change).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

open CategoryTheory CategoryTheory.Limits

-- Rebase without changing any underlying ring; this also handles unequal universes.
private def rebase {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : CommAlgCat.{w} A ⥤ CommAlgCat.{w} B where
  obj X := @CommAlgCat.of B _ X _
    (((algebraMap A X).comp e.symm.toRingHom).toAlgebra)
  map {X Y} f := by
    let : Algebra B X := ((algebraMap A X).comp e.symm.toRingHom).toAlgebra
    let : Algebra B Y := ((algebraMap A Y).comp e.symm.toRingHom).toAlgebra
    exact CommAlgCat.ofHom
      { __ := f.hom.toRingHom
        commutes' := fun b ↦ f.hom.commutes (e.symm b) }

private noncomputable def rebaseEquivalence {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] (e : A ≃+* B) :
    CommAlgCat.{w} A ≌ CommAlgCat.{w} B where
  functor := rebase e
  inverse := rebase e.symm
  unitIso := NatIso.ofComponents
    (fun X ↦ @CommAlgCat.isoMk A _ X
      ((rebase.{w} e ⋙ rebase.{w} e.symm).obj X) _ _
      X.algebra ((rebase.{w} e ⋙ rebase.{w} e.symm).obj X).algebra
      { __ := RingEquiv.refl X
        commutes' := fun a ↦ by simp [rebase, RingHom.algebraMap_toAlgebra] })
    (by intros; ext x; rfl)
  counitIso := NatIso.ofComponents
    (fun X ↦ @CommAlgCat.isoMk B _
      ((rebase.{w} e.symm ⋙ rebase.{w} e).obj X) X _ _
      ((rebase.{w} e.symm ⋙ rebase.{w} e).obj X).algebra X.algebra
      { __ := RingEquiv.refl X
        commutes' := fun b ↦ by simp [rebase, RingHom.algebraMap_toAlgebra] })
    (by intros; ext x; rfl)

private abbrev Pointed (A : Type*) (K : Type w)
    [CommRing A] [CommRing K] [Algebra A K] :=
  ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of A K) ↦ Etale A X.left)

private def pointedRebase {A : Type*} {B : Type*} {K : Type w}
    [CommRing A] [CommRing B] [CommRing K] [Algebra A K] [Algebra B K]
    (e : A ≃+* B) (he : ∀ a, algebraMap B K (e a) = algebraMap A K a) :
    Pointed A K ⥤ Pointed B K where
  obj X := by
    let Y := (rebase e).obj X.obj.left
    let f : Y →ₐ[B] K :=
      { __ := X.obj.hom.hom.toRingHom
        commutes' := fun b ↦ (X.obj.hom.hom.commutes (e.symm b)).trans
          (by simpa using (he (e.symm b)).symm) }
    refine ⟨Over.mk (CommAlgCat.ofHom f), ?_⟩
    let : Algebra A B := e.toRingHom.toAlgebra
    let : Algebra A Y := X.obj.left.algebra
    have : IsScalarTower A B Y := IsScalarTower.of_algebraMap_eq' (by
      ext a
      simp [Y, rebase, RingHom.algebraMap_toAlgebra])
    have : Etale A B := Etale.of_equiv
      { __ := e
        commutes' := fun _ ↦ rfl }
    have : Etale A Y := X.property
    exact Etale.of_restrictScalars A B Y
  map f := ObjectProperty.homMk (Over.homMk ((rebase e).map f.hom.left) (by
    ext x
    exact congrArg (fun g ↦ g.hom x) (Over.w f.hom)))

private noncomputable def pointedRebaseEquivalence
    {A : Type*} {B : Type*} {K : Type w}
    [CommRing A] [CommRing B] [CommRing K] [Algebra A K] [Algebra B K]
    (e : A ≃+* B) (he : ∀ a, algebraMap B K (e a) = algebraMap A K a) :
    Pointed A K ≌ Pointed B K where
  functor := pointedRebase e he
  inverse := pointedRebase e.symm (fun b ↦ by simpa using (he (e.symm b)).symm)
  unitIso := NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ (Over.isoMk
      ((rebaseEquivalence e).unitIso.app X.obj.left) (by ext x; rfl)))
    (by intros; apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext; ext x; rfl)
  counitIso := NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ (Over.isoMk
      ((rebaseEquivalence e).counitIso.app X.obj.left) (by ext x; rfl)))
    (by intros; apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext; ext x; rfl)

private theorem ringHom_comp_apply {A B C : Type*}
    [NonAssocSemiring A] [NonAssocSemiring B] [NonAssocSemiring C]
    {f : B →+* C} {g : A →+* B} {h : A →+* C} (e : f.comp g = h) (x : A) :
    f (g x) = h x := DFunLike.congr_fun e x

private theorem presentationResidue_base
    {A : Type u} {K H : Type (max u v)} [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H] (P : StrictHenselizationPresentationIn A K H) (a : A) :
    P.residueMap (algebraMap A H a) = algebraMap A K a :=
  (P.identification.inv ≫
    P.isColimit.desc (strictHenselizationPointingCoconeIn A K)).hom.commutes a

private theorem presentationRebase
    {A : Type u} {B K H : Type (max u v)}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [Algebra (IsLocalRing.ResidueField B) K]
    [IsSepClosure (IsLocalRing.ResidueField B) K]
    [Algebra B K] [IsScalarTower B (IsLocalRing.ResidueField B) K]
    [CommRing H] [Algebra A H] [Algebra B H]
    (e : A ≃+* B)
    (eK : ∀ a, algebraMap B K (e a) = algebraMap A K a)
    (eH : ∀ a, algebraMap B H (e a) = algebraMap A H a)
    (P : StrictHenselizationPresentationIn.{u, v} A K H) :
    ∃ P' : StrictHenselizationPresentation B K H, P'.residueMap = P.residueMap := by
  let E := pointedRebaseEquivalence e eK
  let F := rebase e
  let c := F.mapCocone (P.cocone.whisker E.inverse)
  let d : E.inverse ⋙ strictHenselizationPointedDiagramIn A K ⋙ F ≅
      strictHenselizationPointedDiagram B K :=
    NatIso.ofComponents (fun X ↦ @CommAlgCat.isoMk B _
      ((E.inverse ⋙ strictHenselizationPointedDiagramIn A K ⋙ F).obj X)
      ((strictHenselizationPointedDiagram B K).obj X) _ _
      ((E.inverse ⋙ strictHenselizationPointedDiagramIn A K ⋙ F).obj X).algebra
      ((strictHenselizationPointedDiagram B K).obj X).algebra
      { __ := RingEquiv.refl X.obj.left
        commutes' := fun b ↦ by
          change algebraMap B X.obj.left (e (e.symm b)) = algebraMap B X.obj.left b
          rw [e.apply_symm_apply] })
      (by intros; ext x; rfl)
  let c' := (Cocone.precompose d.inv).obj c
  have : F.IsEquivalence := (rebaseEquivalence e).isEquivalence_functor
  have hc : IsColimit c := isColimitOfPreserves F (P.isColimit.whiskerEquivalence E.symm)
  have hc' : IsColimit c' := (IsColimit.precomposeHomEquiv d.symm c).symm hc
  let i : F.obj (CommAlgCat.of A H) ≅ CommAlgCat.of B H :=
    @CommAlgCat.isoMk B _ (F.obj (CommAlgCat.of A H)) (CommAlgCat.of B H) _ _
      (F.obj (CommAlgCat.of A H)).algebra (CommAlgCat.of B H).algebra
    { __ := RingEquiv.refl H
      commutes' := fun b ↦ by simpa [F, rebase, RingHom.algebraMap_toAlgebra]
        using (eH (e.symm b)).symm }
  let P' : StrictHenselizationPresentation B K H :=
    ⟨c', hc', F.mapIso P.identification ≪≫ i⟩
  let f₀ : P.cocone.pt ⟶ CommAlgCat.of A K :=
    P.isColimit.desc (strictHenselizationPointingCoconeIn A K)
  let f : c'.pt ⟶ CommAlgCat.of B K :=
    @CommAlgCat.ofHom B _ c'.pt K _ c'.pt.algebra _ _
    { __ := f₀.hom.toRingHom
      commutes' := fun b ↦ (f₀.hom.commutes (e.symm b)).trans
        (by simpa using (eK (e.symm b)).symm) }
  have hf : hc'.desc (strictHenselizationPointingCocone B K) = f := by
    apply hc'.hom_ext
    intro X
    rw [hc'.fac]
    ext x
    exact (congrArg (fun g ↦ g.hom x)
      (P.isColimit.fac (strictHenselizationPointingCoconeIn A K) (E.inverse.obj X))).symm
  refine ⟨P', ?_⟩
  change ((F.mapIso P.identification ≪≫ i).inv ≫
    hc'.desc (strictHenselizationPointingCocone B K)).hom.toRingHom = _
  rw [hf]
  rfl

private theorem presentationLocalProperties
    (A : Type u) (K H : Type (max u v)) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H] (P : StrictHenselizationPresentationIn.{u, v} A K H) :
    ∃ _ : IsStrictlyHenselianLocalRing H,
      Function.Surjective P.residueMap ∧
      RingHom.ker P.residueMap = IsLocalRing.maximalIdeal H := by
  let B := ULift.{v} A
  let e : B ≃+* A := ULift.ringEquiv
  let : IsLocalRing B := e.symm.isLocalRing
  let er := IsLocalRing.ResidueField.mapEquiv e
  let : Algebra B K := ((algebraMap A K).comp e.toRingHom).toAlgebra
  let : Algebra B H := ((algebraMap A H).comp e.toRingHom).toAlgebra
  let : Algebra (IsLocalRing.ResidueField B) K :=
    ((algebraMap (IsLocalRing.ResidueField A) K).comp er.toRingHom).toAlgebra
  let : IsSepClosure (IsLocalRing.ResidueField B) K :=
    ⟨IsSepClosure.sep_closed (IsLocalRing.ResidueField A),
      Algebra.IsSeparable.of_equiv_equiv er.symm (RingEquiv.refl K) (by
        ext x
        simp [RingHom.algebraMap_toAlgebra])⟩
  let : SMul B (IsLocalRing.ResidueField B) :=
    (inferInstance : Algebra B (IsLocalRing.ResidueField B)).toSMul
  let : SMul B K := (inferInstance : Algebra B K).toSMul
  let : IsScalarTower B (IsLocalRing.ResidueField B) K :=
    IsScalarTower.of_algebraMap_eq' (R := B) (S := IsLocalRing.ResidueField B) (A := K) (by
      ext b
      symm
      change algebraMap (IsLocalRing.ResidueField A) K
        (er (IsLocalRing.residue B b)) = algebraMap A K (e b)
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      exact (IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) K (e b)).symm)
  obtain ⟨P', hP'⟩ := presentationRebase e.symm (fun _ ↦ rfl) (fun _ ↦ rfl) P
  obtain ⟨hl, hs, hk⟩ := P'.local_properties B K H
  exact ⟨hl, hP' ▸ hs, hP' ▸ hk⟩

private theorem pointedSmall
    (A : Type u) (K : Type (max u v)) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K] :
    EssentiallySmall.{max u v} (Pointed A K) ∧ IsFiltered (Pointed A K) := by
  let B := ULift.{v} A
  let e : B ≃+* A := ULift.ringEquiv
  let : IsLocalRing B := e.symm.isLocalRing
  let er := IsLocalRing.ResidueField.mapEquiv e
  let : Algebra B K := ((algebraMap A K).comp e.toRingHom).toAlgebra
  let : Algebra (IsLocalRing.ResidueField B) K :=
    ((algebraMap (IsLocalRing.ResidueField A) K).comp er.toRingHom).toAlgebra
  let : IsSepClosure (IsLocalRing.ResidueField B) K :=
    ⟨IsSepClosure.sep_closed (IsLocalRing.ResidueField A),
      Algebra.IsSeparable.of_equiv_equiv er.symm (RingEquiv.refl K) (by
        ext x
        simp [RingHom.algebraMap_toAlgebra])⟩
  let : SMul B (IsLocalRing.ResidueField B) :=
    (inferInstance : Algebra B (IsLocalRing.ResidueField B)).toSMul
  let : SMul B K := (inferInstance : Algebra B K).toSMul
  let : IsScalarTower B (IsLocalRing.ResidueField B) K :=
    IsScalarTower.of_algebraMap_eq' (R := B) (S := IsLocalRing.ResidueField B) (A := K) (by
      ext b
      symm
      change algebraMap (IsLocalRing.ResidueField A) K
        (er (IsLocalRing.residue B b)) = algebraMap A K (e b)
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      exact (IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) K (e b)).symm)
  let E := pointedRebaseEquivalence e.symm (K := K) (fun _ ↦ rfl)
  obtain ⟨hs, hf⟩ := pointedEtale_small_filtered B K
  let := hf
  exact ⟨(essentiallySmall_congr E).mpr hs, IsFiltered.of_equivalence E.symm⟩

private noncomputable def residueFactor
    {D F : Type*} [CommRing D] [Field F] (ρ : D →+* F)
    (I : Ideal D) [I.IsPrime] (hI : I = RingHom.ker ρ) : I.ResidueField →+* F :=
  Ideal.ResidueField.lift I ρ hI.le (by
    intro x hx
    change IsUnit (ρ x)
    rw [isUnit_iff_ne_zero]
    intro h
    exact hx (by simpa [hI, RingHom.mem_ker] using h))

private theorem residueFactor_base
    {D F : Type*} [CommRing D] [Field F] (ρ : D →+* F)
    (I : Ideal D) [I.IsPrime] (hI : I = RingHom.ker ρ) (d : D) :
    residueFactor ρ I hI (algebraMap D I.ResidueField d) = ρ d :=
  Ideal.ResidueField.lift_algebraMap ..

-- A residue-map formulation of the existing ind-etale mapping theorem.
private theorem presentationLift
    (A : Type u) (K H T L : Type (max u v)) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H] (P : StrictHenselizationPresentationIn.{u, v} A K H)
    [CommRing T] [HenselianLocalRing T] [Algebra A T] [Field L]
    (ρ : T →+* L) (hs : Function.Surjective ρ)
    (hk : RingHom.ker ρ = IsLocalRing.maximalIdeal T)
    (φ : K →+* L)
    (hbase : ρ.comp (algebraMap A T) = φ.comp (algebraMap A K)) :
    ∃! f : H →ₐ[A] T, ρ.comp f.toRingHom = φ.comp P.residueMap := by
  classical
  obtain ⟨hsmall, hfilt⟩ := pointedSmall A K
  let := hsmall
  let := hfilt
  let E := equivSmallModel.{max u v} (Pointed A K)
  let D := E.inverse ⋙ strictHenselizationPointedDiagramIn.{u, v} A K
  let c := (P.cocone.extend P.identification.hom).whisker E.inverse
  have hc : IsColimit c :=
    (P.isColimit.ofIsoColimit (P.cocone.extendIso P.identification)).whiskerEquivalence E.symm
  let : IsFiltered (SmallModel.{max u v} (Pointed A K)) := IsFiltered.of_equivalence E
  let : HasColimit D := ⟨⟨c, hc⟩⟩
  let χ := φ.comp P.residueMap
  let q := RingHom.ker χ
  have : q.IsPrime := RingHom.ker_isPrime χ
  let p := q.comap (algebraMap A H)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have hm : p = (IsLocalRing.maximalIdeal T).comap (algebraMap A T) := by
    ext a
    change χ (algebraMap A H a) = 0 ↔ algebraMap A T a ∈ IsLocalRing.maximalIdeal T
    rw [← hk]
    change φ (P.residueMap (algebraMap A H a)) = 0 ↔ ρ (algebraMap A T a) = 0
    rw [presentationResidue_base]
    exact congrArg (fun f : A →+* L ↦ f a = 0) hbase.symm |>.to_iff
  let m := IsLocalRing.maximalIdeal T
  let er := residueFactor ρ m hk.symm
  have her : Function.Bijective er := ⟨RingHom.injective er, fun l ↦ by
    obtain ⟨t, rfl⟩ := hs l
    exact ⟨algebraMap T m.ResidueField t, residueFactor_base ρ m hk.symm t⟩⟩
  let e := RingEquiv.ofBijective er her
  let τ := e.symm.toRingHom.comp (residueFactor χ q rfl)
  have hτ : τ.comp (Ideal.ResidueField.map p q (algebraMap A H) rfl) =
      Ideal.ResidueField.map p m (algebraMap A T) hm := by
    apply Ideal.ResidueField.ringHom_ext
    ext a
    apply e.injective
    change e (τ (Ideal.ResidueField.map p q (algebraMap A H) rfl
      (algebraMap A p.ResidueField a))) = _
    simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    change e (e.symm (residueFactor χ q rfl (algebraMap H q.ResidueField
      (algebraMap A H a)))) = er (algebraMap T m.ResidueField (algebraMap A T a))
    rw [e.apply_symm_apply, residueFactor_base, residueFactor_base]
    change φ (P.residueMap (algebraMap A H a)) = ρ (algebraMap A T a)
    rw [presentationResidue_base]
    exact (DFunLike.congr_fun hbase a).symm
  have spec (f : H →ₐ[A] T) :
      (∃ hf : q = m.comap f.toRingHom,
        Ideal.ResidueField.map q m f.toRingHom hf = τ) ↔ ρ.comp f.toRingHom = χ := by
    constructor
    · rintro ⟨hf, hres⟩
      ext x
      have hx := DFunLike.congr_fun hres (algebraMap H q.ResidueField x)
      have hx' := congrArg e hx
      rw [Ideal.ResidueField.map_algebraMap] at hx'
      change er (algebraMap T m.ResidueField (f x)) =
        e (e.symm (residueFactor χ q rfl (algebraMap H q.ResidueField x))) at hx'
      change residueFactor ρ m hk.symm (algebraMap T m.ResidueField (f x)) = _ at hx'
      simpa only [e.apply_symm_apply, residueFactor_base, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hx'
    · intro hred
      have hf : q = m.comap f.toRingHom := by
        ext x
        change χ x = 0 ↔ f x ∈ IsLocalRing.maximalIdeal T
        rw [← hk]
        exact congrArg (fun z : H →+* L ↦ z x = 0) hred.symm |>.to_iff
      refine ⟨hf, Ideal.ResidueField.ringHom_ext ?_⟩
      ext x
      apply e.injective
      simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
      change er (algebraMap T m.ResidueField (f x)) =
        e (e.symm (residueFactor χ q rfl (algebraMap H q.ResidueField x)))
      rw [e.apply_symm_apply, residueFactor_base, residueFactor_base]
      exact DFunLike.congr_fun hred x
  obtain ⟨f, hf, hu⟩ := map_into_henselian_colimit A T H _ D
    ⟨(colimit.isColimit D).coconePointUniqueUpToIso hc⟩
    (fun i ↦ (E.inverse.obj i).property) q p rfl hm τ hτ
  exact ⟨f, (spec f).mp hf, fun g hg ↦ hu g ((spec g).mpr hg)⟩

/-- Strict henselization of the localization of the base-changed strict henselization.
Source: Stacks Project, Algebra, Tag 08HV
(blueprint: lem-dl-a1-smooth-local-branch-strict-base-change).

Proof: define `α(r ⊗ s) = h(r)s` and take `Q` to be the preimage of the maximal ideal
of `Ssh`. Locality of `h` gives its contraction to `Rsh`; locality of the strict
henselization map gives its contraction to `S`. Elements outside `Q` map to units,
so `α` factors through the local map `β` from the localization `T` at `Q`. The induced
embedding of the residue field of `T` into `K2` makes `K2` its separable closure.
Transport the pointed diagrams along `ULift A ≃ A` to apply the existing local-properties
and small-filtered-category theorems in the containing universe. Reindex a presentation
by its small model and apply the map-into-henselian-colimit theorem to obtain the unique
lift of a specified residue-field map. Construct `Tsh` as the actual colimit of pointed
etale `T`-algebras, and use this lifting property over `T` and `S_q` to obtain maps
`f : Tsh → Ssh` and `g : Ssh → Tsh` inducing the identity of `K2`. Apply uniqueness
over `R_p` to show that `g ∘ h` agrees with the structural map from `Rsh`; hence `g`
is `T`-linear. Uniqueness over `T` and `S_q` then makes `f` and `g` inverse. Transport
the pointed colimit presentation along this residue-compatible `T`-algebra isomorphism.

Universes: `R` and `S` are in `Type u`; the separable closures, the strict henselizations
and their pointed-étale diagrams are in `Type (max u v)`, as in
`StrictHenselizationPresentationIn.{u, v}`. The tensor product and its localization at `Q`
are then in `Type (max u v)`, and the output presentation is taken there.
-/
theorem exists_strictHenselization_tensor_localization
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S))
    (K1 K2 Rsh Ssh : Type (max u v)) [Field K1] [Field K2]
    [CommRing Rsh] [CommRing Ssh] [IsLocalRing Rsh] [IsLocalRing Ssh]
    [Algebra p.ResidueField K1] [IsSepClosure p.ResidueField K1]
    [Algebra (Localization.AtPrime p) K1]
    [IsScalarTower (Localization.AtPrime p) p.ResidueField K1]
    [Algebra q.ResidueField K2] [IsSepClosure q.ResidueField K2]
    [Algebra (Localization.AtPrime q) K2]
    [IsScalarTower (Localization.AtPrime q) q.ResidueField K2]
    [Algebra (Localization.AtPrime p) Rsh] [Algebra R Rsh]
    [IsScalarTower R (Localization.AtPrime p) Rsh]
    [Algebra (Localization.AtPrime q) Ssh] [Algebra S Ssh]
    [IsScalarTower S (Localization.AtPrime q) Ssh]
    [Algebra R Ssh] [IsScalarTower R S Ssh]
    (P1 : StrictHenselizationPresentationIn.{u, v} (Localization.AtPrime p) K1 Rsh)
    (P2 : StrictHenselizationPresentationIn.{u, v} (Localization.AtPrime q) K2 Ssh)
    (φ : K1 →+* K2)
    (hφ : φ.comp (algebraMap p.ResidueField K1) =
      (algebraMap q.ResidueField K2).comp
        (Ideal.ResidueField.map p q (algebraMap R S) hpq))
    (h : Rsh →ₐ[R] Ssh) [IsLocalHom h]
    (hres : P2.residueMap.comp h.toRingHom = φ.comp P1.residueMap) :
    ∃ (Q : Ideal (Rsh ⊗[R] S)) (_ : Q.IsPrime),
      Q.comap (TensorProduct.includeRight : S →ₐ[R] Rsh ⊗[R] S).toRingHom = q ∧
      Q.comap (TensorProduct.includeLeft : Rsh →ₐ[R] Rsh ⊗[R] S).toRingHom =
        IsLocalRing.maximalIdeal Rsh ∧
      ∃ (α : Rsh ⊗[R] S →+* Ssh) (β : Localization.AtPrime Q →+* Ssh),
        (∀ (r : Rsh) (s : S), α (r ⊗ₜ[R] s) = h r * algebraMap S Ssh s) ∧
        β.comp (algebraMap (Rsh ⊗[R] S) (Localization.AtPrime Q)) = α ∧
        ∃ (a : Algebra (Localization.AtPrime Q) Ssh)
          (k : Algebra Q.ResidueField K2) (sep : IsSepClosure Q.ResidueField K2)
          (b : Algebra (Localization.AtPrime Q) K2)
          (t : IsScalarTower (Localization.AtPrime Q) Q.ResidueField K2),
          @algebraMap (Localization.AtPrime Q) Ssh _ _ a = β ∧
          ∃ P : @StrictHenselizationPresentationIn.{max u v, v}
            (Localization.AtPrime Q) K2 Ssh _ _ _ k sep b t _ a,
            P.residueMap = P2.residueMap  := by
  classical
  have _ := hφ
  obtain ⟨hS, hsS, hkS⟩ := presentationLocalProperties _ _ _ P2
  let αa : Rsh ⊗[R] S →ₐ[R] Ssh :=
    TensorProduct.lift h (IsScalarTower.toAlgHom R S Ssh) (fun _ _ ↦ Commute.all _ _)
  let α := αa.toRingHom
  let Q : Ideal (Rsh ⊗[R] S) := (IsLocalRing.maximalIdeal Ssh).comap α
  have hQ : Q.IsPrime := Ideal.comap_isPrime α _
  have hright : Q.comap TensorProduct.includeRight.toRingHom = q := by
    ext s
    change α (1 ⊗ₜ[R] s) ∈ IsLocalRing.maximalIdeal Ssh ↔ s ∈ q
    rw [← hkS]
    change P2.residueMap (α (1 ⊗ₜ[R] s)) = 0 ↔ s ∈ q
    have heval : α (1 ⊗ₜ[R] s) = algebraMap S Ssh s := by simp [α, αa]
    rw [heval, IsScalarTower.algebraMap_apply S (Localization.AtPrime q) Ssh,
      presentationResidue_base]
    rw [IsScalarTower.algebraMap_apply (Localization.AtPrime q) q.ResidueField K2,
      ← IsScalarTower.algebraMap_apply S (Localization.AtPrime q) q.ResidueField,
      map_eq_zero]
    exact Ideal.algebraMap_residueField_eq_zero
  have hleft : Q.comap (TensorProduct.includeLeft : Rsh →ₐ[R] Rsh ⊗[R] S).toRingHom =
      IsLocalRing.maximalIdeal Rsh := by
    have he : α.comp (TensorProduct.includeLeft : Rsh →ₐ[R] Rsh ⊗[R] S).toRingHom =
        h.toRingHom := by
      ext r
      simp [α, αa]
    change ((IsLocalRing.maximalIdeal Ssh).comap α).comap _ = _
    rw [Ideal.comap_comap, he]
    let : IsLocalHom h.toRingHom :=
      ⟨IsLocalHom.map_nonunit (f := h)⟩
    exact IsLocalRing.maximalIdeal_comap h.toRingHom
  have units (z : Q.primeCompl) : IsUnit (α z) := by
    by_contra hunit
    exact z.property hunit
  let T := Localization.AtPrime Q
  let loc : Rsh ⊗[R] S →+* T := algebraMap _ _
  let β : T →+* Ssh := IsLocalization.lift units
  have hβ : β.comp loc = α := IsLocalization.lift_comp units
  have hβlocal : IsLocalHom β := ⟨fun x hx ↦ by
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq Q.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    have hu : IsUnit (α r) := by
      have he := (IsLocalization.lift_mk'_spec units r
        (β (IsLocalization.mk' T r s)) s).mp rfl
      exact he ▸ ((units s).mul hx)
    exact fun hr ↦ hr hu⟩
  let a : Algebra T Ssh := β.toAlgebra
  let := a
  let ρ : T →+* K2 := P2.residueMap.comp β
  have hkρ : RingHom.ker ρ = IsLocalRing.maximalIdeal T := by
    change (RingHom.ker P2.residueMap).comap β = _
    rw [hkS]
    exact IsLocalRing.maximalIdeal_comap β
  have hker : Q = RingHom.ker (P2.residueMap.comp α) := by
    change (IsLocalRing.maximalIdeal Ssh).comap α = _
    rw [← hkS]
    rfl
  let k : Algebra Q.ResidueField K2 :=
    (residueFactor (P2.residueMap.comp α) Q hker).toAlgebra
  let := k
  let b : Algebra T K2 := ρ.toAlgebra
  let := b
  have hresbase : (algebraMap Q.ResidueField K2).comp
      (algebraMap T Q.ResidueField) = ρ := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    apply RingHom.ext
    intro x
    change residueFactor (P2.residueMap.comp α) Q hker
      (algebraMap (Rsh ⊗[R] S) Q.ResidueField x) = P2.residueMap (β (loc x))
    rw [residueFactor_base]
    exact congrArg P2.residueMap (DFunLike.congr_fun hβ x).symm
  let t : IsScalarTower T Q.ResidueField K2 :=
    IsScalarTower.of_algebraMap_eq' hresbase.symm
  let := t
  let qr : q.ResidueField →+* Q.ResidueField :=
    Ideal.ResidueField.map q Q TensorProduct.includeRight.toRingHom hright.symm
  let : Algebra q.ResidueField Q.ResidueField := qr.toAlgebra
  have hqr : (algebraMap Q.ResidueField K2).comp qr = algebraMap q.ResidueField K2 := by
    apply Ideal.ResidueField.ringHom_ext
    ext s
    change algebraMap Q.ResidueField K2
      (Ideal.ResidueField.map q Q TensorProduct.includeRight.toRingHom hright.symm
        (algebraMap S q.ResidueField s)) = algebraMap q.ResidueField K2
          (algebraMap S q.ResidueField s)
    rw [Ideal.ResidueField.map_algebraMap]
    change residueFactor (P2.residueMap.comp α) Q hker
      (algebraMap (Rsh ⊗[R] S) Q.ResidueField (1 ⊗ₜ[R] s)) = _
    rw [residueFactor_base]
    change P2.residueMap (α (1 ⊗ₜ[R] s)) = _
    have heval : α (1 ⊗ₜ[R] s) = algebraMap S Ssh s := by simp [α, αa]
    rw [heval, IsScalarTower.algebraMap_apply S (Localization.AtPrime q) Ssh,
      presentationResidue_base,
      IsScalarTower.algebraMap_apply (Localization.AtPrime q) q.ResidueField K2,
      ← IsScalarTower.algebraMap_apply S (Localization.AtPrime q) q.ResidueField]
  have : IsScalarTower q.ResidueField Q.ResidueField K2 :=
    IsScalarTower.of_algebraMap_eq' hqr.symm
  let sep : IsSepClosure Q.ResidueField K2 :=
    ⟨IsSepClosure.sep_closed q.ResidueField,
      Algebra.isSeparable_tower_top_of_isSeparable q.ResidueField Q.ResidueField K2⟩
  let := sep
  refine ⟨Q, hQ, hright, hleft, α, β, ?_, hβ, a, k, sep, b, t, rfl, ?_⟩
  · intro r s
    simp [α, αa]
  let : HenselianLocalRing Ssh := hS.toHenselianLocalRing
  let : HasColimitsOfShape (Pointed T K2) (CommAlgCat.{max u v} T) := by
    let := (pointedEtale_small_filtered T K2).1
    exact HasColimitsOfShape.of_essentiallySmall _ _
  -- Construct the comparison object as the actual pointed-etale colimit.
  let D := strictHenselizationPointedDiagramIn.{max u v, v} T K2
  let C := colimit D
  let P : StrictHenselizationPresentationIn.{max u v, v} T K2 C :=
    ⟨colimit.cocone D, colimit.isColimit D, Iso.refl _⟩
  obtain ⟨hC, hsC, hkC⟩ := presentationLocalProperties T K2 C P
  let := hC
  let ι : T →+* C := algebraMap T C
  let δ : Localization.AtPrime q →+* T :=
    Localization.localRingHom q Q TensorProduct.includeRight.toRingHom hright.symm
  have hβδ : β.comp δ = algebraMap (Localization.AtPrime q) Ssh := by
    apply IsLocalization.ringHom_ext q.primeCompl
    ext s
    change β (δ (algebraMap S (Localization.AtPrime q) s)) = _
    rw [Localization.localRingHom_to_map]
    change β (loc (1 ⊗ₜ[R] s)) = _
    rw [ringHom_comp_apply hβ]
    simp [α, αa, IsScalarTower.algebraMap_apply S (Localization.AtPrime q) Ssh]
  have hρδ : ρ.comp δ = algebraMap (Localization.AtPrime q) K2 := by
    ext s
    change P2.residueMap (β (δ s)) = _
    rw [ringHom_comp_apply hβδ, presentationResidue_base]
  let : Algebra (Localization.AtPrime q) C := (ι.comp δ).toAlgebra
  obtain ⟨f, hf, _⟩ := presentationLift T K2 C Ssh K2 P
    P2.residueMap hsS hkS (RingHom.id K2) (by ext x; rfl)
  have hfres : P2.residueMap.comp f.toRingHom = P.residueMap := by
    simpa only [RingHom.id_comp] using hf
  obtain ⟨g, hg, _⟩ := presentationLift (Localization.AtPrime q) K2 Ssh C K2 P2
    P.residueMap hsC hkC (RingHom.id K2) (by
      ext s
      change P.residueMap (ι (δ s)) = algebraMap (Localization.AtPrime q) K2 s
      rw [presentationResidue_base]
      exact DFunLike.congr_fun hρδ s)
  have hgres : P.residueMap.comp g.toRingHom = P2.residueMap := by
    simpa only [RingHom.id_comp] using hg
  have hf_apply (x : C) : P2.residueMap (f x) = P.residueMap x :=
    DFunLike.congr_fun hfres x
  have hg_apply (x : Ssh) : P.residueMap (g x) = P2.residueMap x :=
    DFunLike.congr_fun hgres x
  have hgS (s : S) : g (algebraMap S Ssh s) = ι (loc (1 ⊗ₜ[R] s)) := by
    have hs := g.commutes (algebraMap S (Localization.AtPrime q) s)
    change g (algebraMap (Localization.AtPrime q) Ssh
      (algebraMap S (Localization.AtPrime q) s)) =
      ι (δ (algebraMap S (Localization.AtPrime q) s)) at hs
    rw [← IsScalarTower.algebraMap_apply S (Localization.AtPrime q) Ssh,
      Localization.localRingHom_to_map] at hs
    exact hs
  let μ : Rsh →+* T :=
    loc.comp (TensorProduct.includeLeft : Rsh →ₐ[R] Rsh ⊗[R] S).toRingHom
  have hβμ : β.comp μ = h.toRingHom := by
    ext r
    change β (loc (r ⊗ₜ[R] (1 : S))) = h r
    rw [ringHom_comp_apply hβ]
    simp [α, αa]
  let γ : Localization.AtPrime p →+* C :=
    (ι.comp μ).comp (algebraMap (Localization.AtPrime p) Rsh)
  let : Algebra (Localization.AtPrime p) C := γ.toAlgebra
  -- Uniqueness over R_p supplies the missing Rsh-linearity of g.
  have hghbase : (g.toRingHom.comp h.toRingHom).comp
      (algebraMap (Localization.AtPrime p) Rsh) = γ := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    change g (h (algebraMap (Localization.AtPrime p) Rsh
      (algebraMap R (Localization.AtPrime p) r))) =
      ι (μ (algebraMap (Localization.AtPrime p) Rsh
        (algebraMap R (Localization.AtPrime p) r)))
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) Rsh, h.commutes,
      IsScalarTower.algebraMap_apply R S Ssh, hgS]
    change ι (loc ((TensorProduct.includeRight : S →ₐ[R] Rsh ⊗[R] S)
      (algebraMap R S r))) =
      ι (loc ((TensorProduct.includeLeft : Rsh →ₐ[R] Rsh ⊗[R] S)
        (algebraMap R Rsh r)))
    exact congrArg (fun z : Rsh ⊗[R] S ↦ ι (loc z))
      (((TensorProduct.includeRight : S →ₐ[R] Rsh ⊗[R] S).commutes r).trans
        ((TensorProduct.includeLeft : Rsh →ₐ[R] Rsh ⊗[R] S).commutes r).symm)
  let gh : Rsh →ₐ[Localization.AtPrime p] C :=
    { __ := g.toRingHom.comp h.toRingHom
      commutes' := fun r ↦ DFunLike.congr_fun hghbase r }
  let j : Rsh →ₐ[Localization.AtPrime p] C :=
    { __ := ι.comp μ
      commutes' := fun _ ↦ rfl }
  have hjres : P.residueMap.comp j.toRingHom = φ.comp P1.residueMap := by
    ext r
    change P.residueMap (ι (μ r)) = φ (P1.residueMap r)
    rw [presentationResidue_base]
    change P2.residueMap (β (μ r)) = _
    rw [ringHom_comp_apply hβμ]
    exact DFunLike.congr_fun hres r
  have hghres : P.residueMap.comp gh.toRingHom = φ.comp P1.residueMap := by
    ext r
    change P.residueMap (g (h r)) = _
    rw [hg_apply]
    exact DFunLike.congr_fun hres r
  obtain ⟨_, _, hu⟩ := presentationLift (Localization.AtPrime p) K1 Rsh C K2 P1
    P.residueMap hsC hkC φ (by
      ext r
      change P.residueMap (j (algebraMap (Localization.AtPrime p) Rsh r)) = _
      have hj (x : Rsh) : P.residueMap (j x) = φ (P1.residueMap x) :=
        DFunLike.congr_fun hjres x
      rw [hj, presentationResidue_base]
      rfl)
  have hgh : gh = j := (hu gh hghres).trans (hu j hjres).symm
  have hgh_apply (r : Rsh) : g (h r) = ι (μ r) := DFunLike.congr_fun hgh r
  have hgβ : g.toRingHom.comp β = ι := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    apply RingHom.ext
    intro x
    change g (β (loc x)) = ι (loc x)
    rw [ringHom_comp_apply hβ]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r s =>
      calc
        g (α (r ⊗ₜ[R] s)) = g (h r) * g (algebraMap S Ssh s) := by simp [α, αa]
        _ = ι (μ r) * ι (loc (1 ⊗ₜ[R] s)) := by rw [hgh_apply, hgS]
        _ = ι (loc (r ⊗ₜ[R] s)) := by
          change ι (loc (r ⊗ₜ[R] (1 : S))) * ι (loc (1 ⊗ₜ[R] s)) = _
          rw [← map_mul, ← map_mul]
          simp
  let gT : Ssh →ₐ[T] C :=
    { __ := g.toRingHom
      commutes' := fun x ↦ DFunLike.congr_fun hgβ x }
  -- Uniqueness over T and S_q now proves both inverse identities.
  have hgf : gT.comp f = AlgHom.id T C := by
    obtain ⟨_, _, huC⟩ := presentationLift T K2 C C K2 P
      P.residueMap hsC hkC (RingHom.id K2) (by
        ext x
        exact presentationResidue_base P x)
    apply (huC _ ?_).trans (huC _ ?_).symm
    · ext x
      change P.residueMap (g (f x)) = P.residueMap x
      rw [hg_apply, hf_apply]
    · simp
  have hfg : f.toRingHom.comp g.toRingHom = RingHom.id Ssh := by
    let fg : Ssh →ₐ[Localization.AtPrime q] Ssh :=
      { __ := f.toRingHom.comp g.toRingHom
        commutes' := fun s ↦ by
          change f (g (algebraMap (Localization.AtPrime q) Ssh s)) =
            algebraMap (Localization.AtPrime q) Ssh s
          rw [g.commutes]
          change f (ι (δ s)) = _
          rw [f.commutes]
          exact DFunLike.congr_fun hβδ s }
    have hfgres : P2.residueMap.comp fg.toRingHom = P2.residueMap := by
      ext x
      change P2.residueMap (f (g x)) = P2.residueMap x
      rw [hf_apply, hg_apply]
    obtain ⟨_, _, hu₂⟩ := presentationLift (Localization.AtPrime q) K2 Ssh Ssh K2 P2
      P2.residueMap hsS hkS (RingHom.id K2) (by
        ext x
        exact presentationResidue_base P2 x)
    have he : fg = AlgHom.id (Localization.AtPrime q) Ssh :=
      (hu₂ fg (by simpa using hfgres)).trans (hu₂ _ (by simp)).symm
    exact congrArg AlgHom.toRingHom he
  let e : C ≃ₐ[T] Ssh := AlgEquiv.ofAlgHom f gT
    (by apply AlgHom.coe_ringHom_injective; exact hfg) hgf
  let P' : StrictHenselizationPresentationIn.{max u v, v} T K2 Ssh :=
    ⟨P.cocone, P.isColimit, P.identification ≪≫ CommAlgCat.isoMk e⟩
  refine ⟨P', ?_⟩
  change P.residueMap.comp g.toRingHom = P2.residueMap
  exact hgres

end Algebra
