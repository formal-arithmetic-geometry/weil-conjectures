/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeNaturality

/-!
# Affine base change for global Hom out of a perfect complex

## References

* Stacks Project, Tag 0AA7
-/

@[expose] public section

set_option autoImplicit false
universe uAH wAH
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Reuse coefficient naturality without re-elaborating the fixed derived-adjunction choices.
private theorem baseChangeMap_naturality
    [∀ Y : Scheme.{uAH},
      HasDerivedCategory.{wAH} (SheafOfModules.{uAH} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{uAH}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) {E F : schemeDerivedCategory X} (φ : E ⟶ F) :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map φ) ≫
        schemeDerivedBaseChangeMap f f' g g' h F =
      schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map φ) :=
  schemeDerivedBaseChangeMap_naturality f f' g g' h φ

/-- Over affine bases, global derived Hom out of a perfect complex commutes with
Tor-independent base change in D(R'). The comparison is the extension/restriction adjoint of
sections/pushforward comparison (Stacks, Tag 0AA7). -/
theorem affineMorphism_hom_out_of_perfect
    [∀ Z : Scheme.{uAH},
      HasDerivedCategory.{wAH} (SheafOfModules.{uAH} (moduleRings Z.toRingedSpace))]
    [∀ (A : Type uAH) [Ring A], HasDerivedCategory.{wAH} (ModuleCat.{uAH} A)]
    {R B : CommRingCat.{uAH}} {X : Scheme.{uAH}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R)
    [∀ U : X.Opens,
      HasDerivedCategory.{wAH} (SheafOfModules.{uAH} ((moduleRings X.toRingedSpace).over U))]
    (hTor : PullbackStalkTensor.IsTorIndependent f g)
    (M K : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M)
    (hK : schemeDerivedQCohProperty X K) :
    IsIso (affineGlobalHomBaseChangeMap f g M K) :=
    open Opposite TopologicalSpace in by
  classical
  obtain ⟨adj, s, adj', hadj, _, _, hadj'⟩ :=
    scheme_derivedInternalHom_adjunction X
  let N : schemeDerivedQCohCategory X := ⟨K, hK⟩
  obtain ⟨D, _, _, _, hDperfect, comparison, _, hcompN, _, _⟩ :=
    perfect_rhom_tensor_comparison X
      ⟨M, schemeDerivedQCohProperty_of_isPerfect X M hM⟩ N hM adj hadj adj' hadj'
  have : IsIso (comparison N) := hcompN
  let e : MonoidalCategory.tensorObj D.obj K ≅
      (derivedInternalHom (Opens.grothendieckTopology X)
        X.toRingedSpace.sheaf).obj (op M, K) :=
    s D.obj K ≪≫ asIso (comparison N)
  have hbc := torIndependent_perfect_tensor_baseChange f g hTor D.obj K hDperfect hK
  have hnatural := baseChangeMap_naturality f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition e.hom
  have : IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition (MonoidalCategory.tensorObj D.obj K)) := hbc
  have hhom : IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition
      ((derivedInternalHom (Opens.grothendieckTopology X)
        X.toRingedSpace.sheaf).obj (op M, K))) := by
    have : IsIso ((derivedPullback g).map ((schemeDerivedDirectImage f).map e.hom) ≫
        schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition
          ((derivedInternalHom (Opens.grothendieckTopology X)
            X.toRingedSpace.sheaf).obj (op M, K))) := by
      rw [hnatural]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((derivedPullback g).map ((schemeDerivedDirectImage f).map e.hom)) _
  obtain ⟨a, b, hab⟩ := affineGlobalHomBaseChange_factorization f g M K hM hK
  rw [hab]
  infer_instance

end AlgebraicGeometry
