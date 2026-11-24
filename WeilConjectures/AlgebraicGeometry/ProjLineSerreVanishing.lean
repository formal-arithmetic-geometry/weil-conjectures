/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

import all WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ProjShiftedFreeTwist
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProjTwistInverseTransport
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre

/-! # Serre vanishing for the polynomial Proj model of the projective line

## References

* Stacks Project, Tag 01YS, with twists as in Tag 01MN.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Scheme.Modules

-- Reindex each finite local generator set by ULift (Fin n), apply the kernel clause,
-- construct the local presentations above, then descend finite presentation over the cover.
private theorem finitePresentation_of_finiteType_kernels
    {C : Type u} [SmallCategory C] [Limits.HasBinaryProducts C]
    [∀ U : C, Limits.HasBinaryProducts (Over U)]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R) (hfin : F.IsFiniteType)
    (hker : ∀ (U : C) (n : ℕ)
      (f : SheafOfModules.free (R := R.over U) (ULift.{u} (Fin n)) ⟶ F.over U),
      (Limits.kernel f).IsFiniteType) : F.IsFinitePresentation := by
  classical
  have : F.IsFiniteType := hfin
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hfp (i : q.I) :
      SheafOfModules.IsFinitePresentation (R := R.over (q.X i))
        (F.over (q.X i)) := by
    have := hq.isFiniteType i
    let _ := Fintype.ofFinite (q.generators i).I
    let n := Fintype.card (q.generators i).I
    let e := (SheafOfModules.freeFunctor (R := R.over (q.X i))).mapIso
      ((Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm).toIso)
    let f := e.hom ≫ (q.generators i).π
    have : Epi f := inferInstanceAs (Epi (e.hom ≫ (q.generators i).π))
    let G := SheafOfModules.GeneratingSections.ofEpiFree f
    have : G.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
    have : (Limits.kernel G.π).IsFiniteType := by
      simpa only [G, SheafOfModules.GeneratingSections.ofEpiFree_π]
        using hker (q.X i) n f
    exact isFinitePresentation_of_generators_kernel.{u} (F.over (q.X i)) G
  exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
    F q.I q.X q.coversTop hfp

end Scheme.Modules

/-- Serre vanishing in degree one, expressed for polynomial Proj twists
(Stacks, Tags 01YS and 01MN). -/
theorem exists_subsingleton_H_one_tensor_proj_twist
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      Subsingleton ((G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d).H 1) := by
  obtain ⟨C, -, -⟩ := Proj.proj_shifted_free_is_twist k 0
  have : G.IsFinitePresentation :=
    Scheme.Modules.finitePresentation_of_finiteType_kernels G hG.1 hG.2
  obtain ⟨b, hb⟩ := Scheme.Modules.exists_subsingleton_H_tensor_twist k C.iso.hom G
  refine ⟨b, fun d hd ↦ ?_⟩
  have := hb d hd 1 Nat.zero_lt_one
  obtain ⟨e⟩ := Proj.proj_twist_inverse_transport k C d
  let e' : Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d ≅
      (Scheme.Modules.pullback C.iso.hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) :=
    ((Scheme.Modules.pullbackId _).app _).symm ≪≫
      ((Scheme.Modules.pullbackCongr C.iso.hom_inv_id).app _).symm ≪≫
      ((Scheme.Modules.pullbackComp C.iso.hom C.iso.inv).app _).symm ≪≫
      (Scheme.Modules.pullback C.iso.hom).mapIso e
  exact Scheme.Modules.subsingleton_H_of_iso (Iso.refl G ⊗ᵢ e').symm 1

end AlgebraicGeometry
