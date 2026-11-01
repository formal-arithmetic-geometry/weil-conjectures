/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import all WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSiteOriginComparisonCore

/-! # Origin equivalence for a prescribed coefficient-system comparison

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 09B1.
(blueprint: lem-pur-fixed-exceptional-site-origin-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

/-- Every prescribed section-normalized derived comparison has the origin equivalence.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 09B1.
(blueprint: lem-pur-fixed-exceptional-site-origin-equivalence).

Proof: the ordinary finite inverse image is fully faithful on bounded-below objects.
The exact-derived counit on an origin object is therefore invertible. The triangle
identity and reflection of isomorphisms give the finite unit. Conservative system
evaluations and the unit comparison then give the system unit; the system origin
clause gives its counit. Exact inverse image and its derived adjunction preserve the
common lower bound. Finally the scalar adjunction transpose of each transition,
conjugated by the derived tensor and evaluation comparisons, proves normalization
for inverse image; the origin clause proves it for direct image. These arguments
also give the stated finite inverse-origin property. -/
theorem fixedExceptionalSiteOriginEquivalence
    (O : Type (u + 1)) [CommRing O] (ell : O)
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (T : Scheme.{u}) (PE : StrictEtaleEvaluation T O ell)
    (C : ExceptionalSystemSiteComparison O ell T PE) :
    ExceptionalSystemSiteEquivalence C ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) →
        IsIso ((C.image.level n).adjunction.unit.app M)) ∧
      (∀ n M, C.levelOrigin n M →
        IsIso ((C.image.level n).adjunction.counit.app M)) ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) →
        C.levelOrigin n ((C.image.level n).inverse.obj M)) := by
  let PX := C.proEvaluation
  let S := C.ordinary
  let I := C.image
  have hlim : PreservesFiniteLimits S.inverse := S.systemExact.1
  have hcolim : PreservesFiniteColimits S.inverse := S.systemExact.2
  have hlevelLim (n : ℕ) : PreservesFiniteLimits (S.lift n).modules :=
    (S.inverseExact n).1
  have hlevelColim (n : ℕ) : PreservesFiniteColimits (S.lift n).modules :=
    (S.inverseExact n).2
  have hevalLim (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact.{u + 1, u, u + 1} n).1
  have hevalColim (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact.{u + 1, u, u + 1} n).2
  have heval (n : ℕ) (M : DerivedCategory (CoefficientSystem
      (J := T.smallEtaleTopology) O ell)) (a : ℤ) [M.IsGE a] :
      ((PE.evaluation n).obj M).IsGE a :=
    exactDerived_isGE (coefficientEvaluation (J := T.smallEtaleTopology)
      (O := O) (ell := ell) n) (PE.evaluation n) (PE.evaluationFactors n) M a
  have hfull (n : ℕ) := exceptionalLevel_full O ell T S n
    (I.level n).inverse (I.level n).inverseFactors
  have hlunit (n : ℕ) (M : DerivedCategory (strictEtaleLevel T O ell n))
      (hM : ∃ a : ℤ, M.IsGE a) : IsIso ((I.level n).adjunction.unit.app M) := by
    have hreflect : (I.level n).inverse.ReflectsIsomorphisms :=
      exactDerived_reflectsIso_of_boundedBelow_faithful (S.lift n).modules
        (I.level n).inverse (I.level n).inverseFactors
        (fun A B hA hB ↦ (hfull n A B hA hB).1)
    have hc : IsIso ((I.level n).adjunction.counit.app ((I.level n).inverse.obj M)) :=
      exactDerivedAdjunction_counit_isIso_of_origin (S.lift n).modules
        (I.level n).inverse (I.level n).inverseFactors (I.level n).adjunction
        (hfull n) _ M hM (Iso.refl _)
    have hi : IsIso ((I.level n).inverse.map ((I.level n).adjunction.unit.app M) ≫
        (I.level n).adjunction.counit.app ((I.level n).inverse.obj M)) := by
      rw [(I.level n).adjunction.left_triangle_components M]
      exact ⟨𝟙 _, by simp, by simp⟩
    have : IsIso ((I.level n).inverse.map ((I.level n).adjunction.unit.app M)) :=
      IsIso.of_isIso_comp_right
        ((I.level n).inverse.map ((I.level n).adjunction.unit.app M))
        ((I.level n).adjunction.counit.app ((I.level n).inverse.obj M))
    exact isIso_of_reflects_iso _ (I.level n).inverse
  refine ⟨?_, hlunit, ?_, ?_⟩
  · refine {
      inverseBound := ?_
      directBound := ?_
      unit := ?_
      counit := ?_
      inverseOrigin := ?_
      inverseNormalized := ?_
      directNormalized := ?_ }
    · intro a M hM
      exact exactDerived_isGE S.inverse I.system.inverse I.system.inverseFactors M a
    · intro a M hM
      exact exactDerivedAdjunction_isGE S.inverse I.system.inverse
        I.system.inverseFactors I.system.adjunction M a
    · rintro M ⟨a, ha⟩
      apply (coefficientEvaluation_detectsIso O ell PE _).2
      intro n
      have := hlunit n ((PE.evaluation n).obj M) ⟨a, heval n M a⟩
      have hi : IsIso ((PE.evaluation n).map (I.system.adjunction.unit.app M) ≫
          (I.directEvaluation n).hom.app (I.system.inverse.obj M) ≫
          (I.level n).direct.map ((I.inverseEvaluation n).hom.app M)) := by
        rw [I.unit n M]
        infer_instance
      exact IsIso.of_isIso_comp_right
        ((PE.evaluation n).map (I.system.adjunction.unit.app M))
        ((I.directEvaluation n).hom.app (I.system.inverse.obj M) ≫
          (I.level n).direct.map ((I.inverseEvaluation n).hom.app M))
    · intro M hM
      exact (I.origin hfull M hM.1 hM.2).1
    · rintro M ⟨a, ha⟩
      refine ⟨⟨a, exactDerived_isGE S.inverse I.system.inverse
        I.system.inverseFactors M a⟩, ?_⟩
      intro n
      exact ⟨(PE.evaluation n).obj M, ⟨a, heval n M a⟩,
        ⟨((I.inverseEvaluation n).app M).symm⟩⟩
    · intro M hM hnorm m n h
      let em := (I.inverseEvaluation m).app M
      let en := (I.inverseEvaluation n).app M
      let z := ((PE.scalar h).derivedAdj.homEquiv _ _).symm ((PE.transition h).app M)
      have hz : IsIso z := hnorm h
      let g := (I.derivedTensor h).inv.app ((PE.evaluation m).obj M) ≫
        (I.level n).inverse.map z
      have hg : (PX.scalar h).derivedAdj.homEquiv _ _ g =
          (I.level m).inverse.map ((PE.transition h).app M) ≫
            (I.restrictedInverse h).hom.app ((PE.evaluation n).obj M) := by
        simpa only [z, Equiv.apply_symm_apply] using
          exceptional_inverse_scalar_transpose (PE.scalar h).derivedAdj
            (PX.scalar h).derivedAdj (I.level m).adjunction (I.level n).adjunction
            (I.derivedTensor h) (I.restrictedDirect h) (I.restrictedDirect_mate h)
            (I.restrictedInverse h) (I.restrictedInverse_mate h)
            ((PE.evaluation m).obj M) ((PE.evaluation n).obj M) z
      have he : ((PX.scalar h).derivedAdj.homEquiv _ _).symm
          ((PX.transition h).app (I.system.inverse.obj M)) =
          (PX.scalar h).derived.map em.hom ≫ g ≫ en.inv := by
        apply ((PX.scalar h).derivedAdj.homEquiv _ _).injective
        rw [Equiv.apply_symm_apply, (PX.scalar h).derivedAdj.homEquiv_naturality_left,
          (PX.scalar h).derivedAdj.homEquiv_naturality_right]
        dsimp only [Functor.comp_obj] at hg ⊢
        rw [hg]
        have ht := I.inverseTransition h M
        change (PX.transition h).app (I.system.inverse.obj M) ≫
            (PX.scalar h).restriction.map en.hom = em.hom ≫
            (I.level m).inverse.map ((PE.transition h).app M) ≫
            (I.restrictedInverse h).hom.app ((PE.evaluation n).obj M) at ht
        have hc : (PX.scalar h).restriction.map en.inv ≫
            (PX.scalar h).restriction.map en.hom = 𝟙 _ :=
          ((PX.scalar h).restriction.mapIso en).inv_hom_id
        apply (cancel_mono ((PX.scalar h).restriction.map en.hom)).mp
        simp only [Category.assoc, hc]
        dsimp only [Functor.comp_obj] at ht ⊢
        simpa only [Category.comp_id] using ht
      rw [he]
      dsimp only [g]
      infer_instance
    · intro M hM hnorm
      exact (I.origin hfull M hM.1 hM.2).2 hnorm
  · intro n M hM
    obtain ⟨N, hN, ⟨e⟩⟩ := hM.2
    exact exactDerivedAdjunction_counit_isIso_of_origin (S.lift n).modules
      (I.level n).inverse (I.level n).inverseFactors (I.level n).adjunction
      (hfull n) M N hN e
  · intro n M hM
    obtain ⟨a, ha⟩ := hM
    exact ⟨⟨a, exactDerived_isGE (S.lift n).modules (I.level n).inverse
      (I.level n).inverseFactors M a⟩, M, ⟨a, ha⟩, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry
