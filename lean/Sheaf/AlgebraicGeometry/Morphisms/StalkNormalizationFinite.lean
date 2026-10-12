/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleOpenIntegralClosure

/-!
# Finiteness of the normalization over a stalk

Source: Stacks Project, Tag 0EYJ, proof of the local claim.
(blueprint: lem-sbc-stalk-normalization-finite)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Finiteness of the concrete normalization at a generic boundary point.

Source: Stacks Project, Tag 0EYJ (pione-lemma-extend-covering), local claim;
Tags 0EYG, 0EYH (tame normalization) and 0EY6 (depth-two extension).
(blueprint: lem-sbc-stalk-normalization-finite)

Proof: If C is empty, its local pullback is empty and any map into it is an
isomorphism, hence finite. Otherwise smooth connected generic geometry gives
integrality of C and integral closedness of its stalks. The quasi-compact smooth
morphism over the Noetherian S makes C Noetherian. For every affine open V of C,
finiteEtale_open_integralClosure_finite makes the concrete normalization algebra
finite over Gamma(C,V). The normalization's affine chart isomorphism identifies
its structure map with this finite algebra map followed by an isomorphism.
Thus the global relative normalization is finite, and finiteness is preserved
by pullback to the local family at s. The affine algebra lemma uses the trace
bound of Stacks 032L; its only remaining geometric input is the injection of
sections of the open cover into its finite etale generic algebra. No action,
invertible group order, or minimal boundary condition enters this finiteness
argument. The statement retains all the original hypotheses. -/
theorem GaloisCover.stalk_normalization_finite {S C : Scheme.{u}} [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  cases isEmpty_or_nonempty C with
  | inl h =>
    let : IsEmpty ↥(pullback c (S.fromSpecStalk s)) :=
      (pullback.fst c (S.fromSpecStalk s)).base.hom.1.isEmpty
    infer_instance
  | inr h =>
    obtain ⟨hC, hη, hnC, hnη⟩ :=
      smooth_connected_generic_geometry_core hS c q j hCη
    let := hC
    let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType c
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    have hf : IsFinite f.fromNormalization := by
      refine { finite_app := ?_ }
      intro V hV
      let : Algebra Γ(C, V) Γ(PA.obj.left, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
      have hfin : Module.Finite Γ(C, V)
          (integralClosure Γ(C, V) Γ(PA.obj.left, f ⁻¹ᵁ V)) :=
        finiteEtale_open_integralClosure_finite hnC (c ⁻¹ᵁ U) PA V hV
      rw [Scheme.Hom.fromNormalization_app f hV]
      exact (RingHom.finite_respectsIso.cancel_right_isIso
        (CommRingCat.ofHom (algebraMap _ _))
        (Scheme.Hom.normalizationObjIso f hV).inv).2 (RingHom.finite_algebraMap.2 hfin)
    exact inferInstanceAs (IsFinite (pullback.snd f.fromNormalization
      (pullback.fst c (S.fromSpecStalk s))))

end AlgebraicGeometry.Scheme
