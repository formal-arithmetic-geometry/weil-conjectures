/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Sheaf.AlgebraicGeometry.Sites.AffinePolynomialProjectionSupport
import Sheaf.AlgebraicGeometry.Sites.SupportedTorsionCohomologyBound
import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# The higher-dimensional polynomial induction step for affine torsion vanishing

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.proof.md, local calculation and affine-space argument.
(blueprint: lem-sc-affine-polynomial-induction-step)
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

private theorem isZero_of_upperStar_at_all_points
    {B : Scheme.{u}} (F : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj F)) : IsZero F := by
  apply (IsZero.iff_id_eq_zero F).2
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  let Ω := AlgebraicClosure (B.residueField x)
  let s := B.algClosurePoint x
  let P := (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hz : IsZero ((pointSmallEtale s).sheafFiber.obj F) := by
    have hz' := P.map_isZero (h Ω s)
    have e := (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      s (𝟙 (Spec (.of Ω)))).app F
    simp only [Category.id_comp] at e
    exact hz'.of_iso e.symm
  let T := (pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  calc
    T.map (𝟙 F) = 𝟙 (T.obj F) := T.map_id F
    _ = 0 := hz.eq_of_src _ _
    _ = T.map 0 := (T.map_zero F F).symm

private theorem nsmul_id_functor_obj
    {X Y : Scheme.{u}}
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) [P.Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (N : ℕ)
    (hF : N • 𝟙 F = 0) : N • 𝟙 (P.obj F) = 0 := by
  calc
    N • 𝟙 (P.obj F) = P.map (N • 𝟙 F) := by rw [Functor.map_nsmul, P.map_id]
    _ = P.map 0 := congrArg P.map hF
    _ = 0 := P.map_zero _ _

/-- The polynomial-space step of the simultaneous induction over all fields.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.proof.md, "Cohomology of the resulting sheaves on B".
(blueprint: lem-sc-affine-polynomial-induction-step)

Proof: Put d=n+2 and project along the first variable to B=A^(d-1). For a sheaf killed
by N, all right derived direct images remain killed by N, since the functors are additive.
On a Leray diagonal p+r=q>d, the terms r=0,1 vanish by the lower-dimensional bound d-1
on B, which is over an algebraically closed field of torsion dimension zero. For r>=2,
the weighted projection-stalk bound gives zero stalks above residue transcendence degree
d-r. If r>d, every stalk vanishes and geometric points detect the zero sheaf. Otherwise,
apply the supported-torsion cohomology theorem with a=d-r. Each closed affine subscheme
of dimension at most a has cohomological dimension at most a by hIH, because a<d. Since
p>a, the required cohomology is zero. The Grothendieck spectral sequence for direct image
and sections therefore has every graded term on this diagonal zero. Its finite filtration
makes H^q of the source zero, and the comparison with derived global sections gives the
stated subsingleton. The q=2 generic case belongs to the separate stalk-bound theorem. -/
theorem subsingleton_H_polynomial_of_lowerDimension
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)
    (hIH : ∀ (L : Type u) [Field L] (m c : ℕ), m < n + 2 →
      (Spec (.of L)).HasTorsionCohomologicalDimensionLE c →
      ∀ (X : Scheme.{u}) [IsAffine X] (a : X ⟶ Spec (.of L))
        [LocallyOfFiniteType a] [QuasiCompact a],
        topologicalKrullDim X ≤ (m : WithBot ℕ∞) →
          X.HasTorsionCohomologicalDimensionLE (m + c))
    (M : Sheaf (Spec (.of (MvPolynomial (Fin (n + 2)) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N) (hM : N • 𝟙 M = 0)
    (q : ℕ) (hq : n + 2 < q) : Subsingleton (Sheaf.H M q)  := by
  let X := Spec (.of (MvPolynomial (Fin (n + 2)) K))
  let B := Spec (.of (MvPolynomial (Fin (n + 1)) K))
  let f : X ⟶ B := Spec.map (CommRingCat.ofHom (MvPolynomial.rename
    (Fin.succ : Fin (n + 1) → Fin (n + 2))).toRingHom)
  let b : B ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
  have : LocallyOfFiniteType b := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hdim : topologicalKrullDim B ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin (n + 1)) K)) ≤ _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField
        (Field.toIsField K)]
    simp
  have hK := hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed K
  have hB : B.HasTorsionCohomologicalDimensionLE (n + 1) := by
    simpa using hIH K (n + 1) 0 (by omega) hK B b hdim
  let D := Etale.lowerStar AddCommGrpCat.{u + 1} f
  have hdiag : ∀ p r : ℕ, p + r = q →
      Subsingleton (Sheaf.H ((D.rightDerived r).obj M) p) := by
    intro p r hpr
    have hkill := nsmul_id_functor_obj (D.rightDerived r) M N hM
    have ht := isTorsion_of_nsmul_id_eq_zero hN hkill
    by_cases hr : r < 2
    · exact hB _ ht p (by omega)
    · have hr2 : 2 ≤ r := by omega
      have hstalk := isZero_stalk_polynomialProjection_of_lowerDimension K n hIH
        M N hN hM r hr2
      by_cases hrd : n + 2 < r
      · have hz : IsZero ((D.rightDerived r).obj M) := by
          apply isZero_of_upperStar_at_all_points
          intro Ω _ _ s
          apply hstalk Ω s
          exact lt_of_lt_of_le (by exact_mod_cast hrd) (le_add_of_nonneg_right bot_le)
        exact Sheaf.subsingleton_H_of_isZero hz p
      · have hrle : r ≤ n + 2 := by omega
        apply subsingleton_H_of_bounded_support b (n + 2 - r) ?_ _ N hN hkill ?_ p
          (by omega)
        · intro Z _ i _ hd
          have : LocallyOfFiniteType (i ≫ b) := inferInstance
          simpa using hIH K (n + 2 - r) 0 (by omega) hK Z (i ≫ b) hd
        · intro Ω _ _ s hs
          apply hstalk Ω s
          have heq : (n + 2 : ℕ) = r + (n + 2 - r) := by omega
          rw [heq, Nat.cast_add]
          exact (Cardinal.add_lt_add_iff_of_left_lt_aleph0
            (Cardinal.natCast_lt_aleph0 (n := r))).mpr hs
  rw [Etale.subsingleton_H_iff_isZero_rightDerived_Γ]
  have : ((sheafSections B.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (⊤_ B.Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (⊤_ X.Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  let G := (Sheaf.sectionsFunctorAt B.smallEtaleTopology (⊤_ B.Etale) :
    Sheaf _ AddCommGrpCat.{u + 1} ⥤ _)
  have hDG := Adjunction.isAcyclicComposablePair
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f) G
  exact (Functor.isZero_rightDerived_comp_of_isZero D G hDG M q
    (fun p r hpr ↦ (Etale.subsingleton_H_iff_isZero_rightDerived_Γ _ p).mp
      (hdiag p r hpr))).of_iso
        ((NatIso.rightDerived
          (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f) q).app M).symm


end AlgebraicGeometry.Scheme
