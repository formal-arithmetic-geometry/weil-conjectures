/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleKernels
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Shrink
import Mathlib.Algebra.Ring.Shrink

/-! # Finite discrete constructible kernels with coefficient universe retained

Source: Bhatt--Scholze, Section 6.8; finite-coefficient constructible Serre closure.
(blueprint: lem-sf-finite-universe-constructible-kernels). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private def crossUniverseMap {B : Type u} {B₀ : Type}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    [CommRing B₀] [TopologicalSpace B₀] [IsTopologicalRing B₀] [DiscreteTopology B₀]
    (e : B →+* B₀) :
    Profinite.continuousMapRingSheafOfUniverse.{u, u} B ⟶
      Profinite.continuousMapRingSheaf.{u} B₀ :=
  ⟨{ app := fun S ↦ RingCat.ofHom
      { toFun := fun f ↦ ULift.up ⟨fun s ↦ e (f.down s),
          (continuous_of_discreteTopology : Continuous e).comp f.down.continuous⟩
        map_one' := by apply ULift.ext; ext s; exact e.map_one
        map_mul' := by intro f g; apply ULift.ext; ext s; exact e.map_mul _ _
        map_zero' := by apply ULift.ext; ext s; exact e.map_zero
        map_add' := by intro f g; apply ULift.ext; ext s; exact e.map_add _ _ }
     naturality := fun _ _ _ ↦ rfl }⟩

private def crossUniverseIso {B : Type u} {B₀ : Type}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    [CommRing B₀] [TopologicalSpace B₀] [IsTopologicalRing B₀] [DiscreteTopology B₀]
    (e : B ≃+* B₀) :
    Profinite.continuousMapRingSheafOfUniverse.{u, u} B ≅
      Profinite.continuousMapRingSheaf.{u} B₀ where
  hom := crossUniverseMap e.toRingHom
  inv := by
    refine ⟨{ app := ?_, naturality := ?_ }⟩
    · intro S
      exact RingCat.ofHom
        { toFun := fun f ↦ ULift.up ⟨fun s ↦ e.symm (f.down s),
            (continuous_of_discreteTopology : Continuous e.symm).comp f.down.continuous⟩
          map_one' := by apply ULift.ext; ext s; exact e.symm.map_one
          map_mul' := by intro f g; apply ULift.ext; ext s; exact e.symm.map_mul _ _
          map_zero' := by apply ULift.ext; ext s; exact e.symm.map_zero
          map_add' := by intro f g; apply ULift.ext; ext s; exact e.symm.map_add _ _ }
    · intro S T g
      rfl
  hom_inv_id := by
    apply Sheaf.hom_ext
    ext S f
    apply ULift.ext
    ext s
    exact e.symm_apply_apply _
  inv_hom_id := by
    apply Sheaf.hom_ext
    ext S f
    apply ULift.ext
    ext s
    exact e.apply_symm_apply _

/-- Finite quotient constructible internal modules are closed under kernels,
with the coefficient ring in the same universe as the scheme.
Source: Bhatt--Scholze, Section 6.8; finiteDiscrete_constructible_kernel.
(blueprint: lem-sf-finite-universe-constructible-kernels).
Proof: replace the finite quotient ring by a ring structure on a finite standard
set. Postcomposition gives an isomorphism of its continuous-map condensed ring
with the original coefficient ring, retaining the original profinite universe.
Pull back this isomorphism to the scheme. Exact restriction along a coefficient
isomorphism preserves local finite presentations and the same stratifications,
and commutes with kernels. Apply the existing finite discrete kernel theorem
in the small coefficient universe and transport the result back. No assumption
on the scheme or restriction on its universe is introduced. -/
theorem finiteQuotient_constructible_kernel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.finite l E n) T))
    (f : M ⟶ N)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (IntegralQuotient.finite l E n) T) M)
    (hN : IsConstructibleModuleObject
      (condensedRingObj (IntegralQuotient.finite l E n) T) N) :
    IsConstructibleModuleObject
      (condensedRingObj (IntegralQuotient.finite l E n) T) (kernel f) := by
  classical
  let B := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let B₀ : Type := Shrink.{0} B
  let : TopologicalSpace B₀ := ⊥
  let : DiscreteTopology B₀ := ⟨rfl⟩
  let e₀ : B₀ ≃+* B := Shrink.ringEquiv.{0, u} B
  let eR := crossUniverseIso e₀.symm
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e.hom :=
    Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) eR.hom
  let φ := coefficientMap e.hom T
  have : IsIso φ := inferInstance
  let F : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B₀) T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (IntegralQuotient.finite l E n) T) := Mod.comap φ
  let G : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.finite l E n) T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B₀) T) := Mod.comap (inv φ)
  have hGM := _root_.constructible_comap (inv φ) hM
  have hGN := _root_.constructible_comap (inv φ) hN
  have hk := finiteDiscrete_constructible_kernel B₀ T (G.obj M) (G.obj N)
    (G.map f) hGM hGN
  have hk' := _root_.constructible_of_iso
    (PreservesKernel.iso G f).symm hk
  have hback := _root_.constructible_comap φ hk'
  let eback : F.obj (G.obj (kernel f)) ≅ kernel f :=
    ((Mod.comapComp φ (inv φ)).symm ≪≫
      Mod.comapCongr (IsIso.hom_inv_id φ) ≪≫ Mod.comapId _).app (kernel f)
  exact _root_.constructible_of_iso eback hback

end AlgebraicGeometry.ProEtale.CondensedRing
