/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationChart.VectorIntegrationChartCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationTransposes

/-! # The ordinary affine transpose in coefficient-unit coordinates

Source: blueprint latest, sec-smooth-purity/sk-prop-an,
lem-amb-affine-space-top-trace.proof.md, ordered tower paragraph, and
thm-amb-vector-bundle-purity.proof.md, second paragraph.
(blueprint: lem-pur-affine-unit-transpose-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

/-- Compare the ordinary adjunct of the ordered affine counit, after its canonical
Tate coefficient descent. This definition uses neither a bundle frame nor purity.
Source: ordered tower paragraph of lem-amb-affine-space-top-trace.proof.md
(blueprint: lem-pur-affine-unit-transpose-coordinates). -/
def affineTransposeRaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :=
  let N := P.coefficients.l ^ (r + 1)
  let hN := pow_pos P.coefficients.prime.out.pos (r + 1)
  let hT : IsUnit (N : Γ(T, ⊤)) := by
    simpa only [N, Nat.cast_pow] using (primeUnit P T aT).pow (r + 1)
  let t := Etale.projectiveLineTraceTransport N hN (Ring P) hA
  let c := Etale.affineLinearCoefficientDescent (Ring P) N hA t T hT d ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback (Ring P) N hA t
      (affineTraceProjection T d) hT d
  let trace :=
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P))
      (affineTraceProjection T d)).map c.inv ≫
    (Etale.affineLinearCompactComparison N hN (Ring P) hA T hT d).inv ≫
    (Etale.affineTraceAdjunction (Ring P) N hA t
      (fun Y _ hY ↦ Etale.projectiveLineTraceDatum N hN (Ring P) hA Y hY)
      T hT d).counit.app (Etale.ordinaryFiniteUnit (Ring P) T)
  (comparison (Ring P) (affineTraceTower T d)).map
    ((Etale.rightDerivedUpperShriekAdjunction (Ring P)
      (affineTraceProjection T d)).homEquiv _ _ trace)

/-- Normalize the two recursive affine-tower presentations without changing the arrow.
Source: canonical coordinate transport in the ordered tower
(blueprint: lem-pur-affine-unit-transpose-coordinates).
Proof: induction identifies the dependent pair consisting of each tower and its
projection: both start at (T,id), and both adjoin one affine coordinate and compose
the new projection. Eliminate that equality to transport the arrow. Proof irrelevance
identifies the compactification witnesses. HEq determines the transported map uniquely. -/
theorem affineTranspose_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :
    ∃! c : (comparison (Ring P) (iteratedAffineLine T d)).obj
      (Etale.affineLinearBaseCoefficient (Ring P) (P.coefficients.l ^ (r + 1)) hA
        (iteratedAffineLine T d) d) ⟶
      (comparison (Ring P) (iteratedAffineLine T d)).obj (ordinaryTarget P T d),
      HEq c (affineTransposeRaw P T aT d r hA) := by
  have ht (Y : Scheme.{u}) (n : ℕ) :
      (⟨affineTraceTower Y n, affineTraceProjection Y n⟩ : Σ X : Scheme.{u}, X ⟶ Y) =
        ⟨iteratedAffineLine Y n, iteratedAffineLineProj Y n⟩ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ Y ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ : Σ X : Scheme.{u}, X ⟶ Y)) ih
  have transport (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (ha : (N : A) = 0)
      (Y X X' : Scheme.{u}) (f : X ⟶ Y) (g : X' ⟶ Y)
      [HasCompactification f] [HasCompactification g]
      (h : (⟨X, f⟩ : Σ X : Scheme.{u}, X ⟶ Y) = ⟨X', g⟩)
      (c : (comparison A X).obj (Etale.affineLinearBaseCoefficient A N ha X d) ⟶
        (comparison A X).obj
          ((Etale.rightDerivedUpperShriek A f).obj
            (Etale.ordinaryFiniteUnit A Y))) :
      ∃ c' : (comparison A X').obj (Etale.affineLinearBaseCoefficient A N ha X' d) ⟶
        (comparison A X').obj
          ((Etale.rightDerivedUpperShriek A g).obj
            (Etale.ordinaryFiniteUnit A Y)), HEq c' c := by
    cases h
    exact ⟨c, HEq.rfl⟩
  let := (projection_geometry T d).2
  obtain ⟨c, hc⟩ := transport (Ring P) (P.coefficients.l ^ (r + 1)) hA
    T _ _ (affineTraceProjection T d) (iteratedAffineLineProj T d) (ht T d)
    (affineTransposeRaw P T aT d r hA)
  exact ⟨c, hc, fun c' hc' ↦ eq_of_heq (hc'.trans hc.symm)⟩

/-- The specified ordinary ordered-counit transpose in the recorded coordinates.
Source: ordered affine trace, followed by its ordinary adjunction Hom bijection
(blueprint: lem-pur-affine-unit-transpose-coordinates). -/
def affineTranspose (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :=
  (affineTranspose_existsUnique P T aT d r hA).exists.choose

end AlgebraicGeometry.ProEtale.VectorIntegrationChart
