/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Over

import WeilConjectures.AlgebraicGeometry.Modules.AmpleFamily
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # The geometric part of the affine-cover acyclic embedding

## References

* Stacks Project, Tag 0BDY
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem jointlyFaithful_restrict_cover {X : Scheme.{u}} (C : X.OpenCover) :
    JointlyFaithful (fun i ↦ Modules.restrictFunctor (C.f i)) := by
  apply JointlyReflectIsomorphisms.jointlyFaithful
  constructor
  intro P Q φ hφ
  apply Modules.isIso_of_isIso_pullback_map C.f
    (fun x ↦ by obtain ⟨y, hy⟩ := C.covers x; exact ⟨C.idx x, y, hy⟩) φ
  intro i
  exact (NatIso.isIso_map_iff (Modules.restrictFunctorIsoPullback (C.f i)) φ).mp (hφ i)

private theorem faithful_pullback_cover {X : Scheme.{u}} (C : X.OpenCover) :
    (Modules.pullback (Sigma.desc C.f)).Faithful := by
  constructor
  intro P Q φ ψ h
  apply (jointlyFaithful_restrict_cover C).map_injective
  intro i
  let e : Modules.restrictFunctor (C.f i) ≅
      Modules.pullback (Sigma.desc C.f) ⋙ Modules.pullback (Sigma.ι C.X i) :=
    Modules.restrictFunctorIsoPullback (C.f i) ≪≫
      Modules.pullbackCongr (Sigma.ι_comp_desc C.f i).symm ≪≫
      (Modules.pullbackComp (Sigma.ι C.X i) (Sigma.desc C.f)).symm
  apply (cancel_epi (e.inv.app P)).mp
  apply (cancel_mono (e.hom.app Q)).mp
  rw [Category.assoc, Category.assoc, NatIso.naturality_1 e φ, NatIso.naturality_1 e ψ]
  exact congrArg ((Modules.pullback (Sigma.ι C.X i)).map) h

/-- A quasi-coherent module embeds in a pushforward from an affine cover source (Stacks, Tag 0BDY).
-/
theorem exists_affine_cover_module_embedding (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k)))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent] :
    ∃ (U : Scheme.{u}) (j : U ⟶ X)
      (G : SheafOfModules.{u} (moduleRings U.toRingedSpace)),
      IsAffine U ∧ IsAffineHom j ∧ G.IsQuasicoherent ∧
        ∃ i : F ⟶ (Modules.pushforward j).obj G, Mono i := by
  classical
  let C := X.affineCover.finiteSubcover
  have hC (i : C.I₀) : IsAffine (C.X i) := by
    dsimp [C, OpenCover.finiteSubcover]
    infer_instance
  have hf (i : C.I₀) : IsAffineHom (C.f i) := by
    constructor
    intro V hV
    apply (Hom.isAffineOpen_iff_of_isOpenImmersion (C.f i)).mp
    rw [Hom.image_preimage_eq_opensRange_inf]
    exact isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k))))
      ⊤ (isAffineOpen_top _) _ (by simp) _ (by simp)
      (isAffineOpen_opensRange (C.f i)) hV
  have hj : IsAffineHom (Sigma.desc C.f) := isAffineHom_sigmaDesc C.f
  have : (Modules.pullback (Sigma.desc C.f)).Faithful := faithful_pullback_cover C
  refine ⟨∐ C.X, Sigma.desc C.f, (Modules.pullback (Sigma.desc C.f)).obj F,
    inferInstance, hj, inferInstance, (Modules.pullbackPushforwardAdjunction _).unit.app F,
    inferInstance⟩

end AlgebraicGeometry.Scheme
