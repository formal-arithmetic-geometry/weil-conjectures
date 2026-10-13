/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.FormalSystemsPullback
import Sheaf.AlgebraicGeometry.FormalModuleSupportConstant
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.FormalSystemClosedSupportPushforward

/-! # Extension of pulled formal systems across a proper compactification

Source: Stacks Project, Theorem 088E, proof, paragraph after Chow's lemma.
(blueprint: lem-weil-pbc-chow-formal-system-extension)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Extend the pulled formal system to a fixed proper compactification. This assertion
uses neither adic completeness nor an algebraization theorem.

Source: Stacks Project, Theorem 088E, proof, paragraph after Chow's lemma.
(blueprint: lem-weil-pbc-chow-formal-system-extension)

Proof:
1. Pull G back along q. Finite-type module support pulls back to the inverse image of
   its support. All levels have the same support: at a stalk, a zero quotient gives
   M = I^k M = I^(2*k) M = 0 by nilpotent annihilation. Properness of q makes this
   inverse-image support proper over S.
2. Its image under j is closed in X: the source support is proper over S and X is
   separated over S. Each pulled level therefore extends by zero to a coherent module
   on X, equivalently its direct image under j (Stacks Lemma 0CYJ).
3. Apply direct image to every transition. On j(Y), ideal products and quotients have
   the original adic identities, since J.comap p pulls back to Q.comap q by hQ and hj.
   On the complement of the closed support every level is zero. These two opens cover
   X, so annihilation and quotient-transition isomorphisms hold globally. The extended
   levels and transitions form H in Coh(X,J.comap p).
4. The open-immersion restriction/direct-image counit is an isomorphism at every level.
   Its naturality with transitions gives the required isomorphism of systems. -/
theorem exists_chow_formal_system_extension
    {S Z Y X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] [IsNoetherian X]
    (f : Z ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (J : S.IdealSheafData) (Q : Z.IdealSheafData) (hQ : Q = J.comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (q : Y ⟶ Z) [IsProper q] (p : X ⟶ S) [IsProper p]
    (j : Y ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q ≫ f) :
    ∃ H : CoherentFormalModule X (J.comap p),
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        H.obj ⋙ Scheme.Modules.tensorPullback j) := by
  classical
  obtain ⟨⟨P, _, hP, _, _⟩, _⟩ := exists_formalSystemsPullback q Q
  let F := P.obj G
  have hF : F.obj = G.obj ⋙ Scheme.Modules.tensorPullback q :=
    congrArg (fun R ↦ R.obj G) hP
  obtain ⟨R, hRset, hRproper⟩ := hR
  let RY := R.preimage (f := q.base) q.continuous
  have hRY : Scheme.IsClosedSubsetProperOver (q ≫ f) RY :=
    (Scheme.isClosedSubsetProperOver_union_preimage (q ≫ f)).2 q f rfl R hRproper
  obtain ⟨T, hTset, _⟩ :=
    (Scheme.closed_subset_proper_over_base_properties (q ≫ f) RY).2.2.2 j p hj hRY
  have hT : (T : Set X) ⊆ Set.range j.base := by
    rw [hTset]
    exact Set.image_subset_range _ _
  have hcoh := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z
    (G.obj.obj (op 0))).mp (G.property.1 0)
  have : (G.obj.obj (op 0)).IsQuasicoherent := hcoh.1
  have : (G.obj.obj (op 0)).IsFiniteType := hcoh.2
  have hsupport : ∀ n : ℕ,
      {y : Y | ¬ Subsingleton ((F.obj.obj (op n)).presheaf.stalk y)} ⊆
        j.base ⁻¹' (T : Set X) := by
    intro n y hy
    have hy0 : y ∈ {y : Y | ¬ Subsingleton ((F.obj.obj (op 0)).presheaf.stalk y)} := by
      rw [← formalModule_support_eq (Q.comap q) F n]
      exact hy
    have hyR : y ∈ (RY : Set Y) := by
      change y ∈ q.base ⁻¹' (R : Set Z)
      rw [hRset]
      have hs := (Scheme.Modules.finiteType_module_support_pullback
        (G.obj.obj (op 0))).2.2 Y q |>.2
      rw [hF] at hy0
      rw [← hs]
      exact hy0
    rw [hTset]
    exact ⟨y, hyR, rfl⟩
  have hK : (J.comap p).comap j = Q.comap q := by
    rw [← Scheme.IdealSheafData.comap_comp, hj,
      Scheme.IdealSheafData.comap_comp, ← hQ]
  have hpush : IsCoherentFormalModule (J.comap p)
      (F.obj ⋙ Scheme.Modules.pushforward j) := by
    apply coherentFormal_pushforward_of_closed_support j (J.comap p) F.obj
      T hT hsupport
    rw [hK]
    exact F.property
  let H : CoherentFormalModule X (J.comap p) :=
    ⟨F.obj ⋙ Scheme.Modules.pushforward j, hpush⟩
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction j
  let α : Scheme.Modules.tensorPullback j ≅ Scheme.Modules.restrictFunctor j :=
    adj.leftAdjointUniq (Scheme.Modules.restrictAdjunction j)
  let ε : Scheme.Modules.pushforward j ⋙ Scheme.Modules.tensorPullback j ≅ 𝟭 Y.Modules :=
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward j) α ≪≫
      asIso (Scheme.Modules.restrictAdjunction j).counit
  refine ⟨H, ⟨?_⟩⟩
  change G.obj ⋙ Scheme.Modules.tensorPullback q ≅
    (F.obj ⋙ Scheme.Modules.pushforward j) ⋙ Scheme.Modules.tensorPullback j
  exact (eqToIso hF).symm ≪≫ (Functor.rightUnitor F.obj).symm ≪≫
    Functor.isoWhiskerLeft F.obj ε.symm ≪≫
      (Functor.associator F.obj _ _).symm

end AlgebraicGeometry
