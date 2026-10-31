/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusWitnessedCompactification
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingRefinementCoordinatesCore
import WeilConjectures.SixFunctors.PurCompactSupport.RingOpenMapOpenUnit

/-! # Finite ring-sheaf coordinates of one normalized refinement

Source: compactification coherence, the proper-composition and proper/open formula;
Stacks Tags 03DI, 03D6 and 0F7B. -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

private theorem normalized_iso_unique
    {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {K T : C} {M : D} (η : K ⟶ T) (ρ : G.obj M ⟶ T)
    (e e' : F.obj K ≅ M) (hu : IsIso adj.unit) (hη : IsIso η)
    (he : adj.homEquiv _ _ e.hom ≫ ρ = η)
    (he' : adj.homEquiv _ _ e'.hom ≫ ρ = η) : e = e' := by
  let := hu
  let := hη
  have : IsIso (adj.homEquiv _ _ e.hom) := by
    rw [Adjunction.homEquiv_unit]
    infer_instance
  have : IsIso (adj.homEquiv _ _ e.hom ≫ ρ) := by
    rw [he]
    infer_instance
  have : IsIso ρ := IsIso.of_isIso_comp_left (adj.homEquiv _ _ e.hom) ρ
  apply Iso.ext
  apply (adj.homEquiv _ _).injective
  exact (cancel_mono ρ).mp (he.trans he'.symm)

/-- The finite open-unit refinement word has the recorded intrinsic coordinates.
Source: compactification-coherence proof, first two paragraphs; Stacks 03DI, 03D6, 0F7B
(blueprint: lem-sf-finite-ring-refinement-coordinates).

Proof: finiteDirectImage_eq identifies the ordinary ring-sheaf direct image with
constant-coefficient direct image on sections. Its left-adjoint comparison is
finitePullbackIso. The induced open left-adjoint comparison is finiteOpenIso;
its defining unit equation identifies the two open adjunction transposes. Transport
the displayed normalization through these comparisons. The restriction factor
becomes pullback composition followed by the proper counit. The fixed-scalar
proper/open comparison, transported by O.alpha, has exactly this transpose.
The open extension is fully faithful, so its unit is invertible. The transpose of
an invertible open comparison is then invertible; its normalization makes the
restriction factor invertible too. Thus postcomposition with that factor and the
open Hom equivalence are injective, identifying epsilon with that comparison.
The proper direct-image compositor is the conjugate of the same pullback
compositor. Sectionwise normalization of the underived direct-image comparisons
and uniqueness of their derived extensions identify the conjugate compositors.
Substitute epsilon, whisker its inverse by the outer proper image, and cancel
the open and proper coordinate comparisons. The remaining coordinate change is
finiteImageIso, and the remaining witnessed word is intrinsicRefinement by its
definition. This proves the asserted equality of actual arrows, without any
assumption that the refinement square is cartesian. The same unit equations cover
identity refinements, zero inputs and empty opens. The unresolved canonical witness is split
off as `finite_ring_refinement_coordinates_canonical` in the companion module. -/
theorem finite_ring_refinement_coordinates
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (O : FrobeniusExchange.CompactOrigin
      (Padic.coefficientExtensionRing l E (n + 1)) X)
    (hi : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.i))
    (hg : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (r.hom ≫ d.g) =
      proEtaleRingCompositeCoefficients r.hom d.g
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull d.g)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom))
    (ε : (PurCompactSupport.openExtension
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.i).mapDerivedCategory.obj O.K ≅
      (PurCompactSupport.push (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n))
        r.hom).obj ((PurCompactSupport.openExtension
          (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c.i).mapDerivedCategory.obj O.K))
    (hε : (PurCompactSupport.openDerivedAdjunction
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.i).homEquiv _ _ ε.hom ≫
      PurCompactSupport.refinementRestriction
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) r hi O.K =
      (PurCompactSupport.openDerivedAdjunction
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c.i).unit.app O.K) :
    ((PurCompactSupport.geometricPushComposition
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) r.hom d.g hg ≪≫
      eqToIso (congrArg (fun h ↦ PurCompactSupport.push
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) h) r.hom_g)).symm.app _) ≪≫
      (PurCompactSupport.push
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.g).mapIso ε.symm ≪≫
      (PurCompactSupport.finiteImageIso l E n d).app O.K =
    (PurCompactSupport.finiteImageIso l E n c).app O.K ≪≫
      FrobeniusExchange.intrinsicRefinement
        (Padic.coefficientExtensionRing l E (n + 1)) r O := by
  obtain ⟨ε₀, hε₀, hcoord⟩ :=
    finite_ring_refinement_coordinates_canonical l E n r O hi hg
  have heq : ε = ε₀ := normalized_iso_unique
    (PurCompactSupport.openDerivedAdjunction
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.i) _ _ ε ε₀
    (PurCompactSupport.openDerivedAdjunction_unit_isIso _ d.i)
    (by
      let adj := PurCompactSupport.openDerivedAdjunction
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c.i
      let := PurCompactSupport.openDerivedAdjunction_unit_isIso
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c.i
      exact NatIso.isIso_app_of_isIso adj.unit O.K) hε hε₀
  subst ε
  exact hcoord

end WeilConjectures.ConstructibleExceptionalCoefficients
