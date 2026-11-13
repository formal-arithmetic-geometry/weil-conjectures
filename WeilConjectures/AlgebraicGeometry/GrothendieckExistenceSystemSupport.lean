/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.ThickeningSystemsDictionary
import WeilConjectures.AlgebraicGeometry.FormalSystemsProperSupportSerre
import WeilConjectures.AlgebraicGeometry.NoetherianQuasicoherentSubmodules
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceChowComparison
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Proper closed support for a coherent thickening system

## References

* [Stacks Project, Tags 088E, 088F]
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem serre_of_kernel {C : Type*} [Category C] [Abelian C]
    (z : HasZeroMorphisms C) (P : ObjectProperty C) [P.IsSerreClass]
    {T N : C} (α : T ⟶ N)
    (hk : letI := z; P (kernel α)) (hN : P N) : P T := by
  have hz : z = Preadditive.preadditiveHasZeroMorphisms (C := C) :=
    Subsingleton.elim _ _
  subst z
  exact P.prop_X₂_of_exact (ShortComplex.kernelSequence_exact α) hk hN

set_option backward.isDefEq.respectTransparency false in
private theorem formalSupport_of_chow
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (M : CoherentFormalModule X ((Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f))
    (hM : Scheme.Modules.HasSupportProperOver f (M.obj.obj (Opposite.op 0))) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j),
      IsProper (j ≫ f) ∧ AnnihilatedBy _ j.ker M := by
  classical
  let Q := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  let P : ObjectProperty (CoherentFormalModule X Q) := fun T ↦
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j),
      IsProper (j ≫ f) ∧ AnnihilatedBy Q j.ker T
  let R : ObjectProperty (CoherentFormalModule X Q) := fun T ↦
    Scheme.Modules.HasSupportProperOver f (T.obj.obj (Opposite.op 0))
  obtain ⟨⟨ab⟩, hs⟩ := formalSystems_properSupport_serre f Q
  let := ab
  let : HasZeroMorphisms (CoherentFormalModule X Q) :=
    Preadditive.preadditiveHasZeroMorphisms
  have : R.IsSerreClass := (hs).1
  have : P.IsSerreClass := (hs).2
  have hbot : AnnihilatedBy Q ⊥ M := by
    intro n
    have : (M.obj.obj (Opposite.op n)).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (M.property.1 n)).1
    apply (Scheme.idealPowerProduct_isZero_iff_affine_cover X
      (M.obj.obj (Opposite.op n)) ⊥ Set.univ (fun x ↦ ?_) 1).mpr
    · intro U _
      simp
    · obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
        (x := x) (U := ⊤) (by trivial)
      exact ⟨⟨U, hU⟩, Set.mem_univ _, hx⟩
  let S : Set X.IdealSheafData := {K | ∃ T : CoherentFormalModule X Q,
    AnnihilatedBy Q K T ∧ R T ∧ ¬ P T}
  by_contra h
  have hS : S.Nonempty := ⟨⊥, M, hbot, hM, h⟩
  obtain ⟨K, hK, hmax⟩ :=
    (noetherian_quasicoherent_submodules X (M.obj.obj (Opposite.op 0)) (M.property.1 0)).2.2 S hS
  obtain ⟨T, hKT, hRT, hPT⟩ := hK
  obtain ⟨N, α, J, hKJ, hJ, hN⟩ :=
    grothendieckExistence_chow_comparison A I f K T hKT hRT hPT
  have hkerR : R (kernel α) := R.prop_of_mono (kernel.ι α) hRT
  have hkerP : P (kernel α) := by
    by_contra hn
    have hJS : J ∈ S := ⟨kernel α, hJ, hkerR, hn⟩
    exact (ne_of_gt hKJ) (hmax J hJS hKJ.le)
  exact hPT (serre_of_kernel inferInstance P α hkerP hN)

/-- A coherent system whose first term has proper support has one proper closed subscheme
annihilating all its pushed-forward terms. (Stacks, Theorem 088E and Remark 088F) -/
theorem grothendieckExistence_system_support
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (F : ∀ n : ℕ, (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).Modules)
    (φ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).obj (F (n + 1)) ≅ F n)
    (hF : ∀ n : ℕ, RingedSpace.IsCoherent (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).toRingedSpace (F n))
    (hproper : Scheme.Modules.HasSupportProperOver (pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))) (F 0)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j),
      IsProper (j ≫ f) ∧ ∀ (n : ℕ) (V : X.Opens) (a : Γ(X, V)),
        a ∈ j.ker.idealOfOpens V →
        ∀ t : Γ((Scheme.Modules.pushforward (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj (F n), V),
          a • t = 0 := by
  classical
  let M : CoherentThickeningSystem (fun n ↦ pullback f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) i :=
    ⟨F, hF, φ⟩
  let ai n := (Scheme.Modules.nonempty_tensorPullbackAdjunction (i n)).some
  let aj n := (Scheme.Modules.nonempty_tensorPullbackAdjunction (pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).some
  obtain ⟨hX, _, Φ, β, _, _, c, R, r, ρ, hρ⟩ :=
    thickeningSystems_dictionary f I i hi hp ai aj
  let := hX
  have hproper' : Scheme.Modules.HasSupportProperOver f
      ((Φ.obj M).obj.obj (Opposite.op 0)) := hρ.2.2.2.2.2.2.2 M |>.mp hproper
  obtain ⟨Z, j, hj, hjproper, hjM⟩ := formalSupport_of_chow A I f (Φ.obj M) hproper'
  refine ⟨Z, j, hj, hjproper, ?_⟩
  intro n V a ha t
  have hcoh := (Φ.obj M).property.1 n
  let T : CoherentModules X := ⟨(Φ.obj M).obj.obj (Opposite.op n), hcoh⟩
  let B : ObjectProperty (CoherentModules X) := fun T ↦ CoherentModuleSupportedOn T j
  let T' : B.FullSubcategory := ⟨T, hjM n⟩
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType j
  obtain ⟨E, ⟨e⟩⟩ := closedImmersion_coherent_equivalence j
  let G := E.inverse.obj T'
  let eT : (Scheme.Modules.pushforward j).obj G.obj ≅ T.obj :=
    (e.app G).symm ≪≫
      (ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace)).mapIso
        ((ObjectProperty.ι B).mapIso (E.counitIso.app T'))
  let eF := eT ≪≫ (β n).app M
  have : G.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z G.obj).mp
      G.property).1
  have hz := (Scheme.Modules.closedImmersion_pushforward_annihilated j).1 G.obj |>.2
  have heq : (eF.hom.app V) (a • (eF.inv.app V) t) = a • t := by
    rw [Scheme.Modules.Hom.app_smul]
    have hid := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.app V) eF.inv_hom_id) t
    exact congrArg (a • ·) hid
  rw [← heq, hz V a ha, map_zero]

end AlgebraicGeometry
