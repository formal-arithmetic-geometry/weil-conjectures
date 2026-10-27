/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.FiniteTypeFlatEtaleNeighborhood
import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.FinitePresentationSourceStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Flat.Localization

/-!
# Finite type flat module has a finitely presented stalk

Source: Stacks Project, `flat.tex`, Tag 05I7, lemma-finite-type-flat-at-point-local,
affine translation (blueprint: lem-trf-flat-finite-type-flat-point-local).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private theorem finitePresentation_stalk_of_finitePresentation
    {X : Scheme.{u}} (F : X.Modules) [F.IsFinitePresentation] (x : X) :
    Module.FinitePresentation (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) := by
  obtain ⟨U, hx, m, n, s, a, b, hb, hab, _⟩ :=
    RingedSpace.exists_finitePresentation_source_stalk X.toRingedSpace F x
  exact Module.finitePresentation_of_surjective b hb (by
    exact (LinearMap.exact_iff.mp hab) ▸ Submodule.fg_range a)

private theorem finitePresentation_stalk_of_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) (hF : F.IsQuasiCoherentFiniteType) (x : X)
    (hx : moduleFlatAt f F x) :
    Module.FinitePresentation (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) := by
  obtain ⟨S', s', e, he, _, _, V, x', hxx', _, hfp, _, _⟩ :=
    exists_finite_type_flat_etale_neighborhood f F hF x hx
  have := he
  let p := pullback.fst f (Scheme.fromSpecStalk S' s' ≫ e)
  let j := V.ι ≫ p
  have : Flat j := by dsimp [j, p]; infer_instance
  have hj : j x' = x := hxx'
  have : ((Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback p).obj F)).IsFinitePresentation := hfp
  have hstalk := finitePresentation_stalk_of_finitePresentation
    ((Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback p).obj F)) x'
  let c := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app
    ((Scheme.Modules.tensorPullback p).obj F)
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction V.ι
  let a := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction V.ι)
  obtain ⟨d⟩ := Scheme.Modules.nonempty_tensorPullbackComp V.ι p
  let k := c ≪≫ (a.symm.app _) ≪≫ (d.symm.app F)
  have hstalk' := ((RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace x').mapIso k
    ).toLinearEquiv.finitePresentation_iff.mp hstalk
  algebraize [(j.stalkMap x').hom]
  have : Module.FaithfullyFlat (X.presheaf.stalk (j x'))
      (V.toScheme.presheaf.stalk x') :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap j x') (j.toLRSHom.prop x')
  obtain ⟨b, _⟩ := Scheme.Modules.exists_tensorPullback_stalk_iso j x'
  have : Module.FinitePresentation (V.toScheme.presheaf.stalk x')
      (TensorProduct (X.presheaf.stalk (j x')) (V.toScheme.presheaf.stalk x')
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (j x')).obj F)) :=
    (b.app F).toLinearEquiv.finitePresentation_iff.mp hstalk'
  have h := Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    (A := X.presheaf.stalk (j x')) (B := V.toScheme.presheaf.stalk x')
    (M := (RingedSpace.moduleStalkFunctor X.toRingedSpace (j x')).obj F)
  rwa [hj] at h

private theorem finitePresentation_of_scalar_equiv
    {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [Module S M] (e : R ≃+* S)
    (he : ∀ (r : R) (m : M), r • m = e r • m)
    [Module.FinitePresentation S M] : Module.FinitePresentation R M := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have : IsScalarTower R S M := ⟨fun r s m ↦ by
    rw [Algebra.smul_def, mul_smul, he]
    rfl⟩
  let a : R ≃ₗ[R] S :=
    (AlgEquiv.ofRingEquiv (f := e) (fun _ ↦ rfl)).toLinearEquiv
  have : Module.FinitePresentation R S := Module.FinitePresentation.of_equiv a
  exact Module.FinitePresentation.trans R M S

private theorem isLocalizedModule_affine_stalk
    {B N : Type u} [CommRing B] [AddCommGroup N] [Module B N]
    (x : PrimeSpectrum.Top B) :
    IsLocalizedModule x.asIdeal.primeCompl (StructureSheaf.toStalkₗ B N x) := by
  infer_instance

private theorem finitePresentation_localized_model
    {A B N : Type u} [CommRing A] [CommRing B] [AddCommGroup N]
    [Algebra A B] [Module B N] [Module.Finite B N]
    [Algebra.FinitePresentation A B] (q : Ideal B) [q.IsPrime]
    {Nq : Type u} [AddCommGroup Nq] [Module B Nq]
    (gq : N →ₗ[B] Nq) [IsLocalizedModule q.primeCompl gq]
    {Bq : Type*} [CommRing Bq] [Algebra B Bq] [IsLocalization q.primeCompl Bq]
    [Module Bq Nq] [IsScalarTower B Bq Nq]
    (hflat : @Module.Flat A Nq _ _ (Module.compHom Nq (algebraMap A B))) :
    Module.FinitePresentation Bq Nq := by
  classical
  let x : Spec (.of B) := ⟨q, inferInstance⟩
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let F := tilde (R := .of B) (ModuleCat.of B N)
  let R := (Spec (.of B)).presheaf.stalk x
  let : Algebra B R := StructureSheaf.stalkAlgebra B x
  have : IsLocalization q.primeCompl R := StructureSheaf.IsLocalization.to_stalk B x
  have : LocallyOfFinitePresentation f :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) (X := PrimeSpectrum.Top B)
    (moduleStructurePresheaf B N).presheaf x
  let g := StructureSheaf.toStalkₗ B N x
  have : IsLocalizedModule x.asIdeal.primeCompl g := by
    exact isLocalizedModule_affine_stalk x
  let a := IsLocalizedModule.linearEquiv q.primeCompl gq g
  have hBR : IsScalarTower B R M :=
    inferInstanceAs (IsScalarTower B ((structurePresheafInCommRingCat B).stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := PrimeSpectrum.Top B)
        (moduleStructurePresheaf B N).presheaf x))
  let : Module A M := Module.compHom M (algebraMap A B)
  have : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  let : Module A Nq := Module.compHom _ (algebraMap A B)
  have : IsScalarTower A B Nq := IsScalarTower.of_compHom A B _
  have : Module.Flat A M := @Module.Flat.of_linearEquiv A _ _ _ _ _ _ _ hflat
    (a.restrictScalars A).symm
  let : Algebra B Γ(Spec (.of B), ⊤) := StructureSheaf.openAlgebra B (Opposite.op ⊤)
  let : Module B Γ(F, ⊤) := inferInstanceAs (Module B
    ((modulesSpecToSheaf.obj F).presheaf.obj (Opposite.op ⊤)))
  have : IsScalarTower B Γ(Spec (.of B), ⊤) Γ(F, ⊤) :=
    IsScalarTower.of_compHom B Γ(Spec (.of B), ⊤) Γ(F, ⊤)
  have hF : F.IsQuasiCoherentFiniteType := by
    refine ⟨inferInstance, ?_⟩
    have hfin : Module.Finite B Γ(F, ⊤) := Module.Finite.equiv
      (tilde.isoTop (R := .of B) (ModuleCat.of B N)).toLinearEquiv
    have : Module.Finite Γ(Spec (.of B), ⊤) Γ(F, ⊤) :=
      Module.Finite.of_surjective
        ({ toFun := id, map_add' := fun _ _ ↦ rfl,
           map_smul' := fun _ _ ↦ (IsScalarTower.algebraMap_smul Γ(Spec (.of B), ⊤) _ _).symm } :
          Γ(F, ⊤) →ₛₗ[algebraMap B Γ(Spec (.of B), ⊤)] Γ(F, ⊤))
        Function.surjective_id
    exact ((Scheme.Modules.quasicoherent_finite_type_affine (Spec (.of B))).2 F
      inferInstance).2.1 Unit (fun _ ↦ ⊤) (by simp) (fun _ ↦ isAffineOpen_top _)
      (fun _ ↦ inferInstance) |>.1
  have hx : moduleFlatAt f F x := by
    let p := f x
    let : Algebra A ((Spec (.of A)).presheaf.stalk p) :=
      (StructureSheaf.toStalk A p).hom.toAlgebra
    have : IsLocalization p.asIdeal.primeCompl ((Spec (.of A)).presheaf.stalk p) :=
      StructureSheaf.IsLocalization.to_stalk A p
    let : Module ((Spec (.of A)).presheaf.stalk p) M :=
      Module.compHom M (f.stalkMap x).hom
    have : IsScalarTower A ((Spec (.of A)).presheaf.stalk p) M := by
      apply IsScalarTower.of_algebraMap_smul
      intro r m
      change (f.stalkMap x).hom ((StructureSheaf.toStalk A p).hom r) • m = _
      have h := stalkMap_toStalk_apply (CommRingCat.ofHom (algebraMap A B)) x r
      change (f.stalkMap x).hom ((StructureSheaf.toStalk A p).hom r) =
        (StructureSheaf.toStalk B x).hom (algebraMap A B r) at h
      rw [h]
      exact IsScalarTower.algebraMap_smul R (algebraMap A B r) m
    exact (Module.flat_iff_of_isLocalization _ p.asIdeal.primeCompl M).mpr inferInstance
  have hfp : Module.FinitePresentation R M := finitePresentation_stalk_of_flat f F hF x hx
  let e := IsLocalization.algEquiv q.primeCompl Bq R
  let : Module Bq M := Module.compHom M e.toRingHom
  have : Module.FinitePresentation Bq M :=
    finitePresentation_of_scalar_equiv e.toRingEquiv (fun _ _ ↦ rfl)
  have : IsScalarTower B Bq M := by
    apply IsScalarTower.of_algebraMap_smul
    intro r m
    change e (algebraMap B Bq r) • m = _
    rw [e.commutes]
    exact IsScalarTower.algebraMap_smul R r m
  exact Module.FinitePresentation.of_equiv
    (a.extendScalarsOfIsLocalization q.primeCompl Bq).symm

namespace Module

/-- If `A → B` is finitely presented, `N` is finite over `B`, and the localization
of `N` at a prime of `B` is flat over `A`, then that localization is finitely
presented over the localized ring `B_q`.

Source: Stacks Project, `flat.tex`, Tag 05I7, lemma-finite-type-flat-at-point-local,
affine translation (blueprint: lem-trf-flat-finite-type-flat-point-local).

Proof: Translate to the affine schemes `Spec B → Spec A`, with the finite type
module represented by `N`. The flatness hypothesis at the prime gives, by Tag
05I6, an étale neighbourhood where the pulled-back module is finitely presented.
The induced map of local rings is flat and local, hence faithfully flat; the
localized stalk is the tensor product of `N_q` with the target local ring and is
finitely presented. Faithfully flat descent of finite presentation (Tag 03C4(2))
then gives finite presentation of `N_q` over `B_q`. -/
theorem finitePresentation_localizedModule_atPrime_of_flat
    {A : Type u} {B : Type v} {N : Type w}
    [CommRing A] [CommRing B] [AddCommGroup N]
    [Algebra A B] [Module B N] [Module.Finite B N]
    [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime]
    (hflat : @Module.Flat A (LocalizedModule q.primeCompl N) _ _
      (Module.compHom (LocalizedModule q.primeCompl N) (algebraMap A B))) :
    Module.FinitePresentation (Localization.AtPrime q) (LocalizedModule q.primeCompl N) := by
  classical
  let A' := ULift.{max v w} A
  let B' := ULift.{max u w} B
  let N' := ULift.{max u v} N
  let L := ULift.{max u v} (LocalizedModule q.primeCompl N)
  let : Algebra A' B' := ULift.algebra' A B'
  let : Module B' N' := inferInstance
  let q' : Ideal B' := q.comap ULift.ringEquiv.toRingHom
  have : q'.IsPrime := inferInstance
  have : Module.Finite B' N' := by
    let t : N →ₛₗ[(ULift.ringEquiv : B' ≃+* B).symm.toRingHom] N' :=
      { toFun := ULift.up
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact Module.Finite.of_surjective t (fun y ↦ ⟨y.down, rfl⟩)
  have : Algebra.FinitePresentation A' B' := by
    rw [← RingHom.finitePresentation_algebraMap]
    have h₁ := (RingHom.FinitePresentation.of_bijective
      (f := (ULift.ringEquiv : A' ≃+* A).toRingHom) ULift.ringEquiv.bijective)
    have h₂ := (RingHom.finitePresentation_algebraMap.mpr
      (inferInstance : Algebra.FinitePresentation A B)).comp h₁
    exact (RingHom.FinitePresentation.of_bijective
      (f := (ULift.ringEquiv : B' ≃+* B).symm.toRingHom) ULift.ringEquiv.symm.bijective).comp h₂
  let : Module A (LocalizedModule q.primeCompl N) := Module.compHom _ (algebraMap A B)
  let : Module A L := inferInstance
  let : Module (Localization.AtPrime q) L := inferInstance
  let : Module B' L := inferInstance
  let g : N' →ₗ[B'] L :=
    { toFun := fun n ↦ ULift.up (LocalizedModule.mkLinearMap q.primeCompl N n.down)
      map_add' := fun _ _ ↦ congrArg ULift.up (map_add _ _ _)
      map_smul' := fun _ _ ↦ congrArg ULift.up (map_smul _ _ _) }
  have : IsLocalizedModule q'.primeCompl g := by
    constructor
    · intro s
      rw [Module.End.isUnit_iff]
      have hs := (Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units (S := q.primeCompl)
          (LocalizedModule.mkLinearMap q.primeCompl N)
          ⟨s.val.down, show s.val.down ∉ q from s.property⟩)
      constructor
      · intro x y h
        exact ULift.ext _ _ (hs.1 (congrArg ULift.down h))
      · intro y
        obtain ⟨x, hx⟩ := hs.2 y.down
        exact ⟨ULift.up x, ULift.ext _ _ hx⟩
    · intro y
      obtain ⟨⟨n, s⟩, hs⟩ := IsLocalizedModule.surj q.primeCompl
        (LocalizedModule.mkLinearMap q.primeCompl N) y.down
      exact ⟨⟨ULift.up n, ⟨ULift.up s.val, s.property⟩⟩, ULift.ext _ _ hs⟩
    · intro n m h
      have hn : LocalizedModule.mkLinearMap q.primeCompl N n.down =
          LocalizedModule.mkLinearMap q.primeCompl N m.down := congrArg ULift.down h
      obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
        (S := q.primeCompl) (f := LocalizedModule.mkLinearMap q.primeCompl N) hn
      exact ⟨⟨ULift.up s.val, s.property⟩, ULift.ext _ _ hs⟩
  let : Algebra B' (Localization.AtPrime q) :=
    ((algebraMap B (Localization.AtPrime q)).comp ULift.ringEquiv.toRingHom).toAlgebra
  have : IsLocalization q'.primeCompl (Localization.AtPrime q) :=
    IsLocalization.of_ringEquiv_left (ULift.ringEquiv : B' ≃+* B)
      (RingEquiv.map_primeCompl_comap_eq _ q) (fun _ ↦ rfl)
  let : SMul B' (Localization.AtPrime q) := Algebra.toSMul
  have ht : IsScalarTower B' (Localization.AtPrime q) L :=
    ⟨fun b r m ↦ by
      apply ULift.ext
      change (algebraMap B (Localization.AtPrime q) b.down * r) • m.down =
        b.down • (r • m.down)
      rw [mul_smul, IsScalarTower.algebraMap_smul]⟩
  have hflat' : @Module.Flat A' L _ _ (Module.compHom L (algebraMap A' B')) := by
    change Module.Flat (ULift.{max v w} A) L
    rw [Module.Flat.ulift_left_iff, Module.Flat.ulift_right_iff]
    exact hflat
  have hfp := @finitePresentation_localized_model A' B' N' _ _ _ _ _ _ _ q' _
    L _ _ g _ (Localization.AtPrime q) _ _ _ _ ht hflat'
  exact Module.FinitePresentation.of_equiv
    (ULift.moduleEquiv : L ≃ₗ[Localization.AtPrime q] LocalizedModule q.primeCompl N)

end Module
