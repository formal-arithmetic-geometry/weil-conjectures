/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalChernAdjunct
import Sheaf.AlgebraicGeometry.OrdinarySupportedChernNormalization
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion

/-!
# The two integrals of the projective-line diagonal class

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-p1-diagonal-integrals.md
(blueprint: lem-amb-p1-diagonal-integrals).

The Boolean indices false and true designate the first and second projection.
The chart and trace below use canonical pullback and derived-adjunction comparisons.
The supported class is specified by the recorded, uniquely determining Kummer boundary.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] projectiveLineTraceDatum projectiveLineTraceTransport

/-- Either projection of the chosen fibre square of the projective line.
Source: blueprint lem-amb-p1-diagonal-integrals, first sentence
(blueprint: lem-amb-p1-diagonal-integrals). -/
def projectiveLineDiagonalProjection (S : Scheme.{u}) (a : Bool) :
    pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ⟶ ProjectiveLine S :=
  match a with
  | false => pullback.fst _ _
  | true => pullback.snd _ _

/-- The canonical projective-line chart for either projection, including its equation
over the base. It comes from projective-space base change and the flipped square.
Source: blueprint lem-amb-p1-diagonal-integrals, proof step 1
(blueprint: lem-amb-p1-diagonal-integrals). -/
def projectiveLineDiagonalChart (S : Scheme.{u}) (a : Bool) :
    {e : ProjectiveLine (ProjectiveLine S) ≅
      pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) //
      e.hom ≫ projectiveLineDiagonalProjection S a =
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)} :=
  match a with
  | false => ⟨(ProjectiveSpace.isPullback_map (ULift (Fin 2))
      (ProjectiveLine S ↘ S)).flip.isoPullback,
      (ProjectiveSpace.isPullback_map (ULift (Fin 2))
        (ProjectiveLine S ↘ S)).flip.isoPullback_hom_fst⟩
  | true => ⟨(ProjectiveSpace.isPullback_map (ULift (Fin 2))
      (ProjectiveLine S ↘ S)).isoPullback,
      (ProjectiveSpace.isPullback_map (ULift (Fin 2))
        (ProjectiveLine S ↘ S)).isoPullback_hom_snd⟩

/-- The projective-line trace along either projection. Transport along its canonical
chart uses the chart's inverse-image/direct-image unit, direct-image composition,
the normalized shifted twist comparison, and the recorded projective-line trace.
Source: blueprint lem-amb-p1-diagonal-integrals, the maps t_{p_a}
(blueprint: lem-amb-p1-diagonal-integrals). -/
def projectiveLineDiagonalTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧) ⟶
      ordinaryFiniteUnit A (ProjectiveLine S) :=
  letI : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  letI : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  letI : IsNoetherian (ProjectiveLine S) := ⟨⟩
  ordinaryFiniteShiftedLineChart N A hA (projectiveLineTraceTransport N hN A hA) S hS
      (projectiveLineDiagonalProjection S a) (projectiveLineDiagonalChart S a).val
      (projectiveLineDiagonalChart S a).property ≫
    projectiveLineTrace N hN A hA (ProjectiveLine S)
      (by simpa only [map_natCast] using hS.map (ProjectiveLine S ↘ S).appTop.hom)

/-- The canonical source identification A_P → Rp_* RDelta_* A_P. The two units
compose to the identity-map unit because p Delta = id, so this is the canonical
derived-composition identification, in the direction required by the integral.
Source: blueprint lem-amb-p1-diagonal-integrals, alpha_a and proof steps 3 and 5
(blueprint: lem-amb-p1-diagonal-integrals). -/
def projectiveLineDiagonalAlpha (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
        ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteUnit A (ProjectiveLine S))) :=
  supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
      (supportedDerivedUnit A (pullback.diagonal (ProjectiveLine S ↘ S)))

private theorem projectiveLineDiagonal_cartier (S : Scheme.{u}) :
    (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible := by
  intro x
  obtain ⟨U, hx, r, hr, hreg, hker⟩ :=
    IsRegularImmersion.exists_isWeaklyRegular_generators
      (c := 1) (i := pullback.diagonal (ProjectiveLine S ↘ S)) x
  obtain ⟨f, rfl⟩ := List.length_eq_one_iff.mp hr
  refine ⟨U, hx, f, ?_, ?_⟩
  · have hf := (RingTheory.Sequence.isWeaklyRegular_singleton_iff
      Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), U.1) f).mp hreg
    exact mem_nonZeroDivisors_iff_right.mpr fun a ha ↦
      hf (by simpa only [smul_eq_mul, mul_zero, mul_comm] using ha)
  · simpa only [Ideal.ofList_singleton] using hker.symm


/-- Both projective-line projections integrate the supported diagonal class to one.
The Cartier witness and the uniquely normalized supported Ext class explicitly specify
the diagonal's Kummer map; `supportedExactDerivedMap` realizes that class after the
canonical exact closed-direct-image comparison.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-p1-diagonal-integrals.md
(blueprint: lem-amb-p1-diagonal-integrals).

Proof plan:
1. Projective-space base change identifies each projection with P1 over P. Properness
and finite type make P Noetherian, and N stays invertible over S.
2. On product affine charts the diagonal equations are v-u, u-v, 1-uv and uv-1.
Coefficient comparison proves they are nonzerodivisors over every base ring. They cut
out the diagonal and agree by units on overlaps, giving its invertible Cartier ideal.
3. Apply lem-asd-ordinary-supported-kummer. Finite closed direct image is exact, so
its Ext realization has source RDelta_* A_P. Derived composition and the composite
adjunction unit formula identify the two units in alpha with the identity source map.
4. On every geometric fibre of either projection, the diagonal is one rational point.
The local equations (b0 y1 - b1 y0)/yi give the O(1) transition relation, including
the point at infinity. Thus its divisor line is the specified O(1).
5. Write c for delta after the constant unit. The supported-Kummer unit equation
identifies c with the Chern class of the diagonal line. Proper geometric-fibre exchange,
its unit/counit mate formula, and Cartier-preserving Kummer pullback identify the
fibre of Rp_* delta after alpha with the adjoint Kummer class of this O(1). The mate
formula and triangle identity fix its scalar and sign.
6. Base-change compatibility of lem-asd-ordinary-finite-p1-adjunction identifies the
trace on that fibre with its projective-line trace. Its value on the Chern adjunct is
one, by pr2 b inverse b in2 = identity, as in def-amb-p1-trace.
7. Full faithfulness of the degree-zero derived embedding turns the resulting
endomorphism into a sheaf endomorphism. Its difference from identity has image with
zero geometric stalks, by their exactness. Conservative stalks kill that image, so
the endomorphism is identity. Apply this separately to both projections. No equality
test on arbitrary derived morphisms is used. -/
theorem projectiveLine_diagonal_integrals (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ∃ hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible,
      ∃ κ : Ext
        ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteConstant A (ProjectiveLine S)))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2,
        SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
          (by
            simpa using hS.map
              ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                (ProjectiveLine S ↘ S)).appTop.hom) κ ∧
        ∀ a : Bool,
          projectiveLineDiagonalAlpha A S a ≫
            (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
              (supportedExactDerivedMap
              (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
              (ordinaryFiniteConstant A (ProjectiveLine S))
              (Scheme.finiteEtaleTateLine
                (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ) ≫
            projectiveLineDiagonalTrace N hN A hA S hS a =
          𝟙 (ordinaryFiniteUnit A (ProjectiveLine S)) := by
  have hI := projectiveLineDiagonal_cartier S
  have hT : IsUnit (N : Γ(
      pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤)) := by
    simpa only [map_natCast] using hS.map
      ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
        (ProjectiveLine S ↘ S)).appTop.hom
  obtain ⟨κ, hκ, huniq⟩ := ordinary_supported_kummer_uniqueBoundary
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N hN A hA hT
    (pullback.diagonal (ProjectiveLine S ↘ S)) hI
  refine ⟨hI, κ, hκ, ?_⟩
  let : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  let : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  let : IsNoetherian (ProjectiveLine S) := ⟨⟩
  have hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)) := by
    simpa only [map_natCast] using hS.map (ProjectiveLine S ↘ S).appTop.hom
  let dS := projectiveLineTraceDatum N hN A hA S hS
  let dP := projectiveLineTraceDatum N hN A hA (ProjectiveLine S) hP
  have hzero : ordinaryFiniteP1Unit A N hA (projectiveLineTraceTransport N hN A hA)
      (ProjectiveLine S) hP ≫
      projectiveLineTrace N hN A hA (ProjectiveLine S) hP = 0 := by
    change _ ≫ (dP.decomposition.inv ≫ biprod.snd) = 0
    have hinl : ordinaryFiniteP1Unit A N hA (projectiveLineTraceTransport N hN A hA)
        (ProjectiveLine S) hP = biprod.inl ≫ dP.decomposition.hom := by
      rw [dP.decomposition_hom, biprod.inl_desc]
    rw [hinl, Category.assoc, dP.decomposition.hom_inv_id_assoc, biprod.inl_snd]
  intro a
  have hcoords :
      (projectiveLineDiagonalProjection S a =
          pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ∧
        (projectiveLineDiagonalChart S a).val.hom ≫
          pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) =
          ProjectiveSpace.map (ULift (Fin 2)) (ProjectiveLine S ↘ S)) ∨
      (projectiveLineDiagonalProjection S a =
          pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ∧
        (projectiveLineDiagonalChart S a).val.hom ≫
          pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) =
          ProjectiveSpace.map (ULift (Fin 2)) (ProjectiveLine S ↘ S)) := by
    cases a
    · exact Or.inl ⟨rfl, (ProjectiveSpace.isPullback_map (ULift (Fin 2))
        (ProjectiveLine S ↘ S)).flip.isoPullback_hom_snd⟩
    · exact Or.inr ⟨rfl, (ProjectiveSpace.isPullback_map (ULift (Fin 2))
        (ProjectiveLine S ↘ S)).isoPullback_hom_fst⟩
  have hnorm := ordinary_supported_kummer_chern
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N hN A hA hT
    (pullback.diagonal (ProjectiveLine S ↘ S)) hI κ hκ
  have hclass := projectiveLine_diagonal_chern_adjunct N A hA
    (projectiveLineTraceTransport N hN A hA) S hS dS.chern dP.chern
    dS.chern_spec dP.chern_spec hI _ hnorm (projectiveLineDiagonalProjection S a)
    (projectiveLineDiagonalChart S a).val (projectiveLineDiagonalChart S a).property hcoords
  have htrace : projectiveLineDiagonalTrace N hN A hA S hS a =
      ordinaryFiniteShiftedLineChart N A hA (projectiveLineTraceTransport N hN A hA) S hS
        (projectiveLineDiagonalProjection S a) (projectiveLineDiagonalChart S a).val
        (projectiveLineDiagonalChart S a).property ≫
      projectiveLineTrace N hN A hA (ProjectiveLine S) hP := by
    rfl
  calc
    _ = (supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
          (supportedDerivedUnit A (pullback.diagonal (ProjectiveLine S ↘ S)) ≫
            supportedExactDerivedMap
              (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
              (ordinaryFiniteConstant A (ProjectiveLine S))
              (Scheme.finiteEtaleTateLine
                (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ)) ≫
        projectiveLineDiagonalTrace N hN A hA S hS a := by
      simp only [projectiveLineDiagonalAlpha, Functor.map_comp, Category.assoc]
    _ = (dS.chern ≫ ordinaryFiniteP1Unit A N hA
        (projectiveLineTraceTransport N hN A hA) (ProjectiveLine S) hP +
        ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S) dP.chern) ≫
        projectiveLineTrace N hN A hA (ProjectiveLine S) hP := by
      rw [htrace]
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ projectiveLineTrace N hN A hA (ProjectiveLine S) hP) hclass
    _ = 𝟙 (ordinaryFiniteUnit A (ProjectiveLine S)) := by
      rw [Preadditive.add_comp, Category.assoc, hzero, comp_zero, zero_add]
      exact projectiveLineTrace_chern N hN A hA (ProjectiveLine S) hP

end AlgebraicGeometry.Etale
