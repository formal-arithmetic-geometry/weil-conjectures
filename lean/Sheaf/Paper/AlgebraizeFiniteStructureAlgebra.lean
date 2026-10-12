/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase

import Sheaf.Paper.FiniteStructureAlgebraLift
import Sheaf.Paper.FiniteStructureProperSupport
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.FinitePushforwardCoherent
import Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange
import Sheaf.AlgebraicGeometry.GrothendieckExistence
import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Algebraization of the structure algebras of a finite formal system

Source: Stacks Project, Cohomology of Schemes, Lemma 09ZT, proof via 088F and 088E
(blueprint: lem-weil-pbc-algebraize-finite-structure-algebra).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option autoImplicit false


set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

private theorem quotient_formula {R S : Type u} [CommRing R] [CommRing S]
    (J : Ideal R) (b : R →+* S) (e : R ⧸ J ≃+* S)
    (he : ∀ x, e (Ideal.Quotient.mk J x) = b x) :
    Function.Surjective b ∧ RingHom.ker b = J := by
  constructor
  · intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, (he x).symm⟩
  · ext x
    change b x = 0 ↔ _
    rw [← he x, ← e.map_zero, e.injective.eq_iff]
    exact Ideal.Quotient.eq_zero_iff_mem

/-- Algebraize the structure algebras, retaining the ring maps to each reduction.
Source: Stacks Project, Lemma 09ZT, proof through the construction of the algebra F;
Theorem 088E and Remark 088F.

Proof: The finite direct images of O_Yn are coherent on the locally Noetherian Xn.
Affine base change gives compatible algebra transition isomorphisms. Their first support
is closed and contained in the proper image of Y0, hence proper. Apply Grothendieck
existence to obtain a coherent module F with proper support and compatible reductions.
Choose a proper closed subscheme Z annihilating F. Tensor squares and cubes of F and
O_X/I_Z are coherent with proper support. Full faithfulness algebraizes multiplication
from F tensor F and the unit from O_X/I_Z. Faithfulness checks associativity, symmetry
and the unit identity on every reduction. This gives the commutative algebra B with
underlying module F. The adjoints of the reduction algebra isomorphisms give b_n.
On an affine open U, Xn is defined by ker(j_n.app U), and tensor reduction identifies
B(U)/ker(j_n.app U)B(U) with O_Yn(r_n inverse U). Hence b_n is surjective with the
stated kernel. Compatibility of the module comparisons, multiplication and units gives
the displayed equality with g_n sharp on sections. Empty affine opens and zero algebras
have zero section rings; the same quotient formulas apply.
(blueprint: lem-weil-pbc-algebraize-finite-structure-algebra). -/
theorem algebraize_finite_structure_algebra
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n)
      (pullback.map f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
        f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) (𝟙 X)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
        (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              Ideal.Quotient.factor_comp_mk]))
      (fnY (n + 1)))
    [IsProper (fnY 0 ≫ pullback.snd _ _)]
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) :
    ∃ B : X.CommAlgebraSheaf,
      B.toModule.IsQuasicoherent ∧ RingedSpace.IsCoherent X.toRingedSpace B.toModule ∧
      Scheme.Modules.HasSupportProperOver f B.toModule ∧
      ∃ b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))),
        (∀ (n : ℕ) (U : X.Opens), IsAffineOpen U →
          Function.Surjective ((b n).right.hom.app (op U)).hom ∧
          RingHom.ker ((b n).right.hom.app (op U)).hom =
            (RingHom.ker ((pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).app U).hom).map
              (B.hom.hom.app (op U)).hom) ∧
        (∀ (n : ℕ) (U : X.Opens),
          (b (n + 1)).right.hom.app (op U) ≫
            (gn n).appLE ((fnY (n + 1) ≫ pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⁻¹ᵁ U)
              ((fnY n ≫ pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U)
              (by rw [← Scheme.Hom.comp_preimage, hw n]) =
            (b n).right.hom.app (op U)) := by
  classical
  let Xn (n : ℕ) := pullback f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let j (n : ℕ) : Xn n ⟶ X := pullback.fst _ _
  let i (n : ℕ) : Xn n ⟶ Xn (n + 1) :=
    pullback.map _ _ _ _ (𝟙 X)
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
      (𝟙 _) (by simp)
      (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        Ideal.Quotient.factor_comp_mk])
  have hi (n : ℕ) : i n ≫ j (n + 1) = j n := by simp [i, j]
  have hp (n : ℕ) : i n ≫ pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))) := by
    simp [i]
  let c (n : ℕ) : Scheme.Modules.tensorPullback (j (n + 1)) ⋙
      Scheme.Modules.tensorPullback (i n) ≅ Scheme.Modules.tensorPullback (j n) :=
    (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp (i n)
      (j (n + 1)))).symm ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback (hi n))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hXn (n : ℕ) : IsLocallyNoetherian (Xn n) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
  have hYn (n : ℕ) : IsLocallyNoetherian (Yn n) :=
    LocallyOfFiniteType.isLocallyNoetherian (fnY n)
  let F (n : ℕ) : (Xn n).Modules :=
    (Scheme.Modules.pushforward (fnY n)).obj (SheafOfModules.unit (Yn n).ringCatSheaf)
  let γ (n : ℕ) : (Scheme.Modules.tensorPullback (i n)).obj (F (n + 1)) ⟶ F n :=
    Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
        (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
      (Scheme.Modules.pushforward (fnY n)).map
        (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))
  have hγ (n : ℕ) : IsIso (γ n) := by
    have : (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf).IsQuasicoherent :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp
        (Scheme.Modules.isCoherent_unit_of_finite_to_locallyNoetherian (fnY (n + 1))) |>.1
    have := (Scheme.Modules.affinePushforward_baseChange
      (fnY (n + 1)) (fnY n) (i n) (gn n) (hcart n).flip
      (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf)).2
    have := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso (gn n)).1
    dsimp only [γ]
    infer_instance
  let φ (n : ℕ) : (Scheme.Modules.tensorPullback (i n)).obj (F (n + 1)) ≅ F n :=
    @asIso _ _ _ _ (γ n) (hγ n)
  have hF (n : ℕ) : RingedSpace.IsCoherent (Xn n).toRingedSpace (F n) := by
    have : IsLocallyNoetherian (Xn n) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    exact (Scheme.Modules.isCoherent_pushforward_of_isFinite (fnY n) _
      (Scheme.Modules.isCoherent_unit_of_finite_to_locallyNoetherian (fnY n))).1
  have hproper0 : Scheme.Modules.HasSupportProperOver
      (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))))
      (F 0) := Scheme.Modules.finite_structure_proper_support (fnY 0) _
  obtain ⟨G, hG, hpG, ψ, hψ⟩ :=
    (grothendieck_existence A I f i hi hp c (fun _ ↦ rfl)).2 F φ hF hproper0
  obtain ⟨B, ⟨eG⟩, b, hquot, hcomp⟩ :=
    finite_structure_algebra_lift A I X f i hi hp c (fun _ ↦ rfl)
      Yn fnY gn hcart hw G hG hpG ψ hψ
  obtain ⟨hGqc, hGft⟩ :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG
  have hBqc : B.toModule.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso eG.symm hGqc
  have hBft : B.toModule.IsFiniteType := by
    let := hGft
    obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData G
    let qB : B.toModule.LocalGeneratorsData :=
      { I := q.I
        X := q.X
        coversTop := q.coversTop
        generators := fun t ↦ (q.generators t).ofEpi
          ((SheafOfModules.overFunctor X.ringCatSheaf (q.X t)).map eG.inv) }
    have hqB : SheafOfModules.LocalGeneratorsData.IsFiniteType.{u, u, u, u} qB := by
      constructor
      intro t
      have := hq.isFiniteType t
      dsimp only [qB]
      infer_instance
    exact { exists_localGeneratorsData := ⟨qB, hqB⟩ }
  have hBcoh :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X B.toModule).mpr
      ⟨hBqc, hBft⟩
  have hBproper : Scheme.Modules.HasSupportProperOver f B.toModule := by
    obtain ⟨Z, hZ, hpZ⟩ := hpG
    refine ⟨Z, ?_, hpZ⟩
    rw [hZ]
    ext x
    have e := CategoryTheory.Iso.toLinearEquiv
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapIso eG)
    exact not_congr e.toEquiv.subsingleton_congr.symm
  refine ⟨B, hBqc, hBcoh, hBproper, b, ?_, hcomp⟩
  intro n U hU
  obtain ⟨e, he⟩ := hquot n U hU
  exact quotient_formula _ _ e he

end AlgebraicGeometry
