/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.TwistedCoordinateSectionCartier
import Sheaf.Paper.CoordinateSectionProjectiveTrace
import Sheaf.Paper.CoordinateSectionTensorTrace
import Sheaf.Paper.CoordinateSectionSiteTransport
import Sheaf.Paper.CoordinateCartierBoundarySign
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Twisted coordinate-section normalization
Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one and even-shift paragraphs
(blueprint: lem-pur-twisted-coordinate-section-normalization).

The supporting module spells out every arrow; this module records the normalization,
its canonical closed coprojection, its Cartier realization and its signed orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Every allowed exponent, with no flatness or ramification condition. The same
Cartier arrow underlies all the ordinary and pro-etale equations, as CartierRealization
states explicitly. Source: blueprint all finite levels, Steps 1--10
(blueprint: lem-pur-twisted-coordinate-section-normalization). -/
def NormalizationAt [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (hI : (sectionMap T).ker.IsInvertible) : Prop :=
  ∀ (b : ℕ) (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0),
    ∃ hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤)),
      OrdinaryNormalization (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI ∧
      CoprojectionNormalization (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI ∧
      ProNormalization T P b hA aT hT hI

attribute [local irreducible] OrdinaryNormalization CoprojectionNormalization
  ProNormalization CartierRealization ProjectiveNormalization

/-- The coordinate Cartier section integrates to one, its exceptional adjunct is
invertible, and all even Tate twists have the same literal normalization. The sign
against the localization-boundary orientation is negative on that orientation's domain.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one coordinate and even-shift
paragraphs; DAG signed-cone audit
(blueprint: lem-pur-twisted-coordinate-section-normalization).

Proof:
1. Apply lem-pur-line-zero-geometry to the trivial line. Multiplication by t is
injective in R[t], even for nonreduced R, so the zero section is Cartier. Finite type
makes the base, affine line and projective line Noetherian. The zero divisor on P1
has dual-ideal frames t^-1 and 1, hence its line bundle is O(1). Ell^a is invertible
and kills A. The roots sheaf, rather than A over Z/ell^a, is flat; its scalar-extended
line is rank one and has finite Tor amplitude (lem-asd-etale-finite-twist-pullback).
2. Pull back the actual supported Kummer class to the affine chart. The open counit
identifies j!s*A with the projective divisor source by the open-closed exact sequence.
Naturality of this counit identifies the two supported arrows
(lem-asd-ordinary-supported-kummer, lem-weil-pbc-open-closed-short-exact).
3. Apply Rq* and the identity-normalized compact-support compositor. Forgetting
support gives the Kummer Chern class of O(1). The trace sends it to one by
 def-amb-p1-trace. This proves the first three ordinary equations with the actual I_p.
4. The normalized coordinate-line adjunction composes the trace-normalized P1
adjunction with j! adjoint to j*. Its counit is inverse projection followed by
identity tensor I_p. Conjugating its identity left comparison proves that the
specified integration transpose is invertible (lem-pur-coordinate-line-adjunction).
5. Transport the supported arrow, trace, open counit, projection and transpose using
lem-pur-vector-integration-site-comparison. The source is fixed by
lem-pur-closed-section-compact-origin; the closed counit is fixed by
lem-pur-closed-finite-adjoint-counit-transport. Compact-support site coherence and
conjugation fix the exceptional compositor. These are equalities of derived maps.
6. The two adjunct-counit identities identify the exceptional composite with the
compact-support equation of Step 3. It is the identity. Gamma and the compositor
are isomorphisms, so cancellation proves that the Cartier adjunct is an isomorphism.
7. In the frame e=t^-1 the divisor section is tau=t*e. The normalized relative
Yoneda extension therefore represents minus the coordinate localization boundary
(lem-pur-principal-torsor-yoneda-sign). The signed cone of
lem-pur-divisor-relative-cone has boundary b to (0,-b). Coefficient and site comparison
preserve this sign. The orientation of thm-pur-affine-line-orientation is the
positive boundary, so the Cartier adjunct equals its negative.
8. Each M_r is invertible and of finite Tor amplitude. The closed coprojection mate
is the transpose of inverse proper projection followed by the tensor of the closed
counit (lem-pur-immersion-twist, lem-pur-coprojection). Substituting the adjunct-counit
identity gives exactly the tensor of u_s with the identity. Tensor and shift addition
give A_X(r+1)[2r+2], with the root-normalized twistedTarget comparison.
9. The composition-projection mate identifies successive projection maps with the
identity projection for ps=id. Consequently the twisted compact composite is
identity tensor the scalar of Step 3. Its exceptional transpose is precisely the
last ordinary equation and its transported pro-etale equation. The signed interchange
factor is (-1)^(2r*2)=1, since both shifts are even.
10. A common larger annihilating exponent identifies all roots by their power maps.
Unique normalized ordinary supported classes and the projection-normalized finite
Tate site comparison identify all maps with the same published cartierKummerMap.
Thus the assertions hold independently of a; no ramification divisibility or
flatness of A over Z/ell^a has entered. The empty base yields the zero derived
category throughout, so all identities and isomorphy assertions remain valid. -/
theorem twistedCoordinateSectionNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] :
    ∃ hI : (sectionMap T).ker.IsInvertible,
      IsNoetherian T ∧
      CartierRealization T P aT hI ∧
      P.CoordinateCartierSign T aT ∧
      IsClosedImmersion (projectiveZero T) ∧
      (∀ [IsNoetherian T] [IsClosedImmersion (projectiveZero T)],
        ProjectiveNormalization P T) ∧
      ∀ [IsNoetherian T], NormalizationAt T P aT hI := by
  let p : AffineSpace PUnit.{u + 1} T ⟶ T := AffineSpace PUnit.{u + 1} T ↘ T
  have : SmoothOfRelativeDimension 1 p := by
    simpa only [Nat.card_unique] using AffineSpace.smoothOfRelativeDimension_over
      PUnit.{u + 1} T
  have hs : sectionMap T ≫ p = 𝟙 T := AffineSpace.zeroSection_comp_over _ _
  let l := IsClosedImmersion.lift (sectionMap T) (sectionMap T).ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι (sectionMap T).ker).ge
  have : IsIso l := IsClosedImmersion.isIso_lift (sectionMap T)
    (sectionMap T).ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι (sectionMap T).ker).symm
  have hl : (sectionMap T).ker.subschemeι ≫ p = l := by
    rw [← IsClosedImmersion.lift_fac (sectionMap T) (sectionMap T).ker.subschemeι
      (Scheme.IdealSheafData.ker_subschemeι (sectionMap T).ker).ge,
      Category.assoc, hs, Category.comp_id]
  have : IsIso ((sectionMap T).ker.subschemeι ≫ p) := hl ▸ inferInstance
  have hI : (sectionMap T).ker.IsInvertible :=
    Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
      inferInstance inferInstance inferInstance
  have hT : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  have hzero : projectiveZero T ≫ (ProjectiveLine T ↘ T) = 𝟙 T := by
    rw [projectiveZero, Category.assoc, ProjectiveLine.affineChart_over]
    exact hs
  have : IsClosedImmersion (projectiveZero T ≫ (ProjectiveLine T ↘ T)) :=
    hzero ▸ inferInstance
  have hc : IsClosedImmersion (projectiveZero T) :=
    IsClosedImmersion.of_comp (projectiveZero T) (ProjectiveLine T ↘ T)
  let : IsNoetherian T := hT
  let : IsClosedImmersion (projectiveZero T) := hc
  obtain ⟨hprojective, hchern⟩ := coordinateSectionProjectiveTrace P T
  obtain ⟨hcartier, hsite⟩ := coordinateSectionSiteTransport P T aT hI
  refine ⟨hI, hT, hcartier, ?_, hc, ?_, ?_⟩
  · exact P.coordinateCartierBoundarySign T aT
  · intro _ _
    exact hprojective
  · intro _ b hA
    have hunit : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤)) := by
      simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (b + 1)
    have hchern' := hchern b hA hunit hI
    have hintegration' :
        (sectionComposition (Ring P) T).inv.app (Etale.ordinaryFiniteUnit (Ring P) T) ≫
          (compact (Ring P) T).map
            (restrictedSupported (Ring P) T (P.coefficients.l ^ (b + 1))
              (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hunit hI) ≫
          CoordinateLine.integration (Ring P) (P.coefficients.l ^ (b + 1)) hA T
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hunit =
        Etale.ordinaryFiniteP1ChernPushforward (Ring P) (P.coefficients.l ^ (b + 1)) hA T
            (Etale.projectiveLineTraceDatum (P.coefficients.l ^ (b + 1))
              (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (Ring P) hA T hunit).chern ≫
          Etale.projectiveLineTrace (P.coefficients.l ^ (b + 1))
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (Ring P) hA T hunit := by
      unfold CoordinateLine.integration
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ Etale.projectiveLineTrace (P.coefficients.l ^ (b + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (Ring P) hA T hunit) hchern'
    have hscalar := hintegration'.trans
      (Etale.projectiveLineTrace_chern (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (Ring P) hA T hunit)
    obtain ⟨hcoprojection, htensor⟩ := coordinateSectionTensorTrace (Ring P) T
      (P.coefficients.l ^ (b + 1)) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
      hA hunit hI hscalar
    have hord : OrdinaryNormalization (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hunit hI :=
      by
        unfold OrdinaryNormalization
        exact ⟨hchern', hintegration', hscalar, htensor⟩
    exact ⟨hunit, hord, hcoprojection, hsite b hA hunit hord hcoprojection⟩

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
