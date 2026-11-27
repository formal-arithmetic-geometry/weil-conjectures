/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraFlatBaseChange
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.RelativeTangentBundle.RelativeTangentBundle
public import WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential
public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDifferentials
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential

/-!
# Centred diagonal neighbourhood and its differential under an étale source map

## References

* Stacks Project, Tags 02GE, 0473, 0635 and 08S2
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ChartNormalDifferential

attribute [local irreducible] Scheme.Modules.tensorPullback
  ConormalGradedAlgebra.presentation PurityNormalBundle.normalCone
  RelativeTangentBundle.scheme PurityNormalBundle.projection
  RelativeTangentBundle.projection PurityNormalBundle.zeroSection
  RelativeTangentBundle.zeroSection Scheme.Hom.relativeDifferentials

namespace AlgebraicGeometry

attribute [local instance] ChartNormalDifferential.Comparison.closed

private theorem restrictionIdentification {U A Y : Scheme.{u}} {d : ℕ} {p : A ⟶ Y}
    {e : U ⟶ A} [IsSeparated p] [IsSeparated (e ≫ p)] [Smooth p] [Smooth (e ≫ p)]
    (C : Comparison d p e) :
    ∃ ωV : (e ≫ p).relativeDifferentials ≅ ConormalGradedAlgebra.piece C.δ 1,
      IsDifferenceIdentification (e ≫ p) C.δ (C.O.ι ≫ pullback.fst (e ≫ p) (e ≫ p))
        (C.O.ι ≫ pullback.snd (e ≫ p) (e ≫ p)) ωV ∧
      IsNormalTangentIdentification (e ≫ p) C.δ ωV (C.r ≪≫ C.tU) := by
  sorry

/-- The canonical centred-neighbourhood transport, including its graded and tangent maps.
(Stacks, Tags 02GE, 0473, 0635 and 08S2). -/
theorem chart_centre_transport (k : Type u) [Field k]
    {X Y V : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of k))
    (aY : Y ⟶ Spec (CommRingCat.of k))
    (aV : V ⟶ Spec (CommRingCat.of k))
    [IsSeparated aX] [IsSeparated aY] [IsSeparated aV]
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [LocallyOfFiniteType aV]
    [QuasiCompact aX] [QuasiCompact aY] [QuasiCompact aV]
    (g : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d g]
    (hgk : g ≫ aY = aX)
    (uV : V ⟶ X) [Etale uV]
    (huVk : uV ≫ aX = aV)
    (h : V ⟶ Y) (hh : h = uV ≫ g) :
    ∃ (a : pullback h g ⟶ pullback.diagonalObj g)
      (_ : a = pullback.map h g g g uV (𝟙 X) (𝟙 Y) (by simp [hh]) (by simp))
      (b : pullback.diagonalObj h ⟶ pullback h g)
      (_ : b = pullback.map h h h g (𝟙 V) uV (𝟙 Y) (by simp) (by simp [hh]))
      (s : V ⟶ pullback h g)
      (_ : s = pullback.lift (𝟙 V) uV (by simp [hh])),
      IsPullback a (pullback.fst h g) (pullback.fst g g) uV ∧
      IsPullback s uV a (pullback.diagonal g) ∧
      ∃ (O : (pullback.diagonalObj h).Opens) (iO : V ⟶ O.toScheme)
          (hIO : IsClosedImmersion iO)
          (_ : iO ≫ O.ι = pullback.diagonal h),
        O.1 =
          (Set.range (pullback.map uV uV h h (𝟙 V) (𝟙 V) g
            (by simp [hh]) (by simp [hh])) \ Set.range (pullback.diagonal h))ᶜ ∧
        Set.range (pullback.diagonal h) ⊆ O.1 ∧
        IsClosedImmersion
          (pullback.map uV uV h h (𝟙 V) (𝟙 V) g (by simp [hh]) (by simp [hh])) ∧
        IsOpenImmersion (pullback.diagonal uV) ∧
        IsClosedImmersion (pullback.diagonal uV) ∧
        IsPullback iO (𝟙 V) (O.ι ≫ b) s ∧
        IsPullback iO uV (O.ι ≫ b ≫ a) (pullback.diagonal g) ∧
        Etale (O.ι ≫ b) ∧ IsSeparated (O.ι ≫ b) ∧
        Etale (O.ι ≫ b ≫ a) ∧ IsSeparated (O.ι ≫ b ≫ a) ∧
        ∃ (hg : IsSeparated g),
          letI : IsSeparated g := hg
          letI : IsClosedImmersion (pullback.diagonal g) := inferInstance
          letI : IsClosedImmersion iO := hIO
          letI : Smooth g := SmoothOfRelativeDimension.smooth d g
          letI : Smooth (uV ≫ g) := inferInstance
          let Ag := ConormalGradedAlgebra.presentation (pullback.diagonal g)
          let Ah := ConormalGradedAlgebra.presentation iO
          ∃ (hcomp : iO ≫ O.ι ≫ b ≫ a = uV ≫ pullback.diagonal g)
            (c : (Scheme.Modules.tensorPullback uV).obj Ag.algebra.toModule ≅
              Ah.algebra.toModule),
            ConormalGradedAlgebra.IsBaseChangeMap iO (pullback.diagonal g)
              (O.ι ≫ b ≫ a) uV hcomp Ah Ag c.hom ∧
            ∃ (ωV : (uV ≫ g).relativeDifferentials ≅ ConormalGradedAlgebra.piece iO 1)
              (ωX : g.relativeDifferentials ≅
                ConormalGradedAlgebra.piece (pullback.diagonal g) 1)
              (tV : PurityNormalBundle.normalCone iO ≅
                RelativeTangentBundle.scheme (uV ≫ g))
              (tX : PurityNormalBundle.normalCone (pullback.diagonal g) ≅
                RelativeTangentBundle.scheme g)
              (ν : PurityNormalBundle.normalCone iO ⟶
                PurityNormalBundle.normalCone (pullback.diagonal g))
              (du : RelativeTangentBundle.scheme (uV ≫ g) ⟶
                RelativeTangentBundle.scheme g),
              IsDifferenceIdentification (uV ≫ g) iO
                (O.ι ≫ pullback.fst h h) (O.ι ≫ pullback.snd h h) ωV ∧
              IsDifferenceIdentification g (pullback.diagonal g)
                (pullback.fst g g) (pullback.snd g g) ωX ∧
              IsNormalTangentIdentification (uV ≫ g) iO ωV tV ∧
              IsNormalTangentIdentification g (pullback.diagonal g) ωX tX ∧
              IsSpecMap uV Ah.algebra Ag.algebra
                (PurityNormalBundle.projection iO)
                (PurityNormalBundle.projection (pullback.diagonal g))
                (normalAlgebraIso iO) (normalAlgebraIso (pullback.diagonal g)) ν
                (pullbackSection uV Ah.algebra.toModule Ag.algebra.toModule c.hom) ∧
              IsPullback ν (PurityNormalBundle.projection iO)
                (PurityNormalBundle.projection (pullback.diagonal g)) uV ∧
              PurityNormalBundle.zeroSection iO ≫ ν =
                uV ≫ PurityNormalBundle.zeroSection (pullback.diagonal g) ∧
              IsDifferential g uV du ∧
              IsPullback du (RelativeTangentBundle.projection (uV ≫ g))
                (RelativeTangentBundle.projection g) uV ∧
              RelativeTangentBundle.zeroSection (uV ≫ g) ≫ du =
                uV ≫ RelativeTangentBundle.zeroSection g ∧
              ν ≫ tX.hom = tV.hom ≫ du := by
  classical
  subst hh
  have : IsSeparated (g ≫ aY) := hgk ▸ inferInstance
  have : IsSeparated g := IsSeparated.of_comp g aY
  have : LocallyOfFiniteType (g ≫ aY) := hgk ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g aY
  have : QuasiCompact (g ≫ aY) := hgk ▸ inferInstance
  have : QuasiCompact g := QuasiCompact.of_comp g aY
  have : IsSeparated (uV ≫ aX) := huVk ▸ inferInstance
  have : IsSeparated uV := IsSeparated.of_comp uV aX
  have : QuasiCompact (uV ≫ aX) := huVk ▸ inferInstance
  have : QuasiCompact uV := QuasiCompact.of_comp uV aX
  have : IsSeparated ((uV ≫ g) ≫ aY) := by
    rw [Category.assoc, hgk, huVk]
    infer_instance
  have : IsSeparated (uV ≫ g) := IsSeparated.of_comp (uV ≫ g) aY
  have : SmoothOfRelativeDimension d (uV ≫ g) := by
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + d) (uV ≫ g))
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  have : Smooth (uV ≫ g) := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian aY
  have := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := {}
  have := LocallyOfFiniteType.isLocallyNoetherian aX
  have := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  have := LocallyOfFiniteType.isLocallyNoetherian aV
  have := QuasiCompact.compactSpace_of_compactSpace aV
  have : IsNoetherian V := {}
  obtain ⟨C⟩ := comparisonOfChart aY d g uV
  obtain ⟨ωV, hωV, htV⟩ := restrictionIdentification C
  let a := pullback.map (uV ≫ g) g g g uV (𝟙 X) (𝟙 Y) (by simp) (by simp)
  let b := pullback.map (uV ≫ g) (uV ≫ g) (uV ≫ g) g (𝟙 V) uV (𝟙 Y) (by simp) (by simp)
  let s : V ⟶ pullback (uV ≫ g) g := pullback.lift (𝟙 V) uV (by simp)
  have ha : IsPullback a (pullback.fst (uV ≫ g) g) (pullback.fst g g) uV :=
    (isPullback_pullback_map_left uV g g).flip
  have hsq : IsPullback s uV a (pullback.diagonal g) :=
    (pullback_lift_diagonal_isPullback uV g).flip
  have hb : IsPullback b (pullback.snd _ _) (pullback.snd _ _) uV :=
    isPullback_pullback_map (uV ≫ g) (uV ≫ g) g uV rfl
  have hba : pullback.map (uV ≫ g) (uV ≫ g) g g uV uV (𝟙 Y) (by simp) (by simp) = b ≫ a := by
    ext <;> simp [a, b]
  have hq : C.q = C.O.ι ≫ b ≫ a := by rw [C.q_eq, hba]
  have hcomp : C.δ ≫ C.O.ι ≫ b ≫ a = uV ≫ pullback.diagonal g := by
    rw [← hq]
    exact C.square
  have hout : IsPullback C.δ uV (C.O.ι ≫ b ≫ a) (pullback.diagonal g) := by
    rw [← hq]
    exact IsPullback.of_isLimit C.cartesian
  have hds : pullback.diagonal (uV ≫ g) ≫ b = s := by
    ext <;> simp [b, s]
  have : Etale b := MorphismProperty.of_isPullback hb.flip inferInstance
  have : IsSeparated b := MorphismProperty.of_isPullback hb.flip inferInstance
  have : IsSeparated a := MorphismProperty.of_isPullback ha.flip inferInstance
  have hEt : Etale (C.O.ι ≫ b ≫ a) := by
    rw [← hq]
    exact C.etale
  have hbc : ∀ (q' : C.O.toScheme ⟶ pullback g g) (_ : q' = C.q)
      (hs' : C.δ ≫ q' = uV ≫ pullback.diagonal g),
      ConormalGradedAlgebra.IsBaseChangeMap C.δ (pullback.diagonal g) q' uV hs'
        (ConormalGradedAlgebra.presentation C.δ)
        (ConormalGradedAlgebra.presentation (pullback.diagonal g)) C.c.hom := by
    rintro q' rfl hs'
    exact C.graded_comparison
  have hzero : RelativeTangentBundle.zeroSection (uV ≫ g) ≫ C.de =
      uV ≫ RelativeTangentBundle.zeroSection g := by
    have h1 := C.tangent_U.2.1
    have h2 := C.tangent_A.2.1
    have h3 := C.restriction_zero
    have h4 := C.zero_section
    have h5 := C.normal_is_differential
    rw [← h1, Category.assoc, ← h5, ← h3, Category.assoc, Iso.hom_inv_id_assoc,
      reassoc_of% h4, h2]
  refine ⟨a, rfl, b, rfl, s, rfl, ha, hsq, C.O, C.δ, C.closed,
    C.diagonal_factorization, C.open_set, ?_, ?_, inferInstance, inferInstance,
    IsPullback.of_bot (by simpa using hout) (by
      rw [← Category.assoc, C.diagonal_factorization, hds, Category.id_comp]) hsq,
    hout, inferInstance, inferInstance, hEt, inferInstance, inferInstance, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [← C.diagonal_factorization]
    exact (C.δ x).2
  · exact MorphismProperty.of_isPullback
      (pullback_map_diagonal_isPullback uV uV g).flip.flip inferInstance
  · refine ⟨hcomp, C.c, hbc _ hq.symm _, ωV, C.ωA, C.r ≪≫ C.tU, C.tA,
      C.ν, C.de, hωV, C.difference_A, htV, C.tangent_A, C.normal_spec,
      C.normal_cartesian, C.zero_section, C.differential, C.differential_cartesian,
      hzero, ?_⟩
    rw [Iso.trans_hom, Category.assoc, ← C.normal_is_differential, Iso.hom_inv_id_assoc]

end AlgebraicGeometry
