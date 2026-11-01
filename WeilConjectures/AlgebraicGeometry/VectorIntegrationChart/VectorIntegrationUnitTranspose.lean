/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationChart.VectorIntegrationChartCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationTransposes
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
public import WeilConjectures.AlgebraicGeometry.EtaleIdentityExceptionalAdjunct
public import WeilConjectures.AlgebraicGeometry.OrderedProjectionUnit.ComparedPullbackUnit
public import WeilConjectures.AlgebraicGeometry.OrderedProjectionUnit.NativeProjectionUnit
public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationIdentityUnit
public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRankZeroLocal
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTensorCoordinates

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

private theorem affineTranspose_ordinaryTrace
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :
    let := (projection_geometry T d).2
    affineTranspose P T aT d P.level (annihilates P) =
      (comparison (Ring P) (iteratedAffineLine T d)).map
        ((Etale.rightDerivedUpperShriekAdjunction (Ring P)
          (iteratedAffineLineProj T d)).homEquiv _ _
            (AffineOrderedIntegration.ordinaryTrace P T aT d)) := by
  let := (projection_geometry T d).2
  have ht :
      (⟨affineTraceTower T d, affineTraceProjection T d⟩ : Σ X : Scheme.{u}, X ⟶ T) =
        ⟨iteratedAffineLine T d, iteratedAffineLineProj T d⟩ := by
    induction d with
    | zero => rfl
    | succ d ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ T ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ : Σ X : Scheme.{u}, X ⟶ T)) ih
  have transport (X X' : Scheme.{u}) (f : X ⟶ T) (g : X' ⟶ T)
      [HasCompactification f] [HasCompactification g]
      (h : (⟨X, f⟩ : Σ X : Scheme.{u}, X ⟶ T) = ⟨X', g⟩)
      (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P)) f).obj
          (Etale.affineLinearBaseCoefficient (Ring P)
            (P.coefficients.l ^ (P.level + 1)) (annihilates P) X d) ⟶
        Etale.ordinaryFiniteUnit (Ring P) T)
      (t' : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P)) g).obj
          (Etale.affineLinearBaseCoefficient (Ring P)
            (P.coefficients.l ^ (P.level + 1)) (annihilates P) X' d) ⟶
        Etale.ordinaryFiniteUnit (Ring P) T) (hh : HEq t t') :
      HEq ((comparison (Ring P) X).map
        ((Etale.rightDerivedUpperShriekAdjunction (Ring P) f).homEquiv _ _ t))
        ((comparison (Ring P) X').map
          ((Etale.rightDerivedUpperShriekAdjunction (Ring P) g).homEquiv _ _ t')) := by
    cases h
    cases hh
    rfl
  have htrace :=
    (AffineOrderedIntegration.ordinaryTrace_existsUnique P T aT d).exists.choose_spec
  change HEq (AffineOrderedIntegration.ordinaryTrace P T aT d)
    (AffineOrderedIntegration.ordinaryTraceRaw P T aT d) at htrace
  have hraw := transport _ _ (affineTraceProjection T d) (iteratedAffineLineProj T d)
    ht (AffineOrderedIntegration.ordinaryTraceRaw P T aT d)
    (AffineOrderedIntegration.ordinaryTrace P T aT d) htrace.symm
  have hnorm := (affineTranspose_existsUnique P T aT d P.level
    (annihilates P)).exists.choose_spec
  change HEq (affineTranspose P T aT d P.level (annihilates P))
    (affineTransposeRaw P T aT d P.level (annihilates P)) at hnorm
  exact eq_of_heq (hnorm.trans hraw)

private theorem chartAffineCoefficient_zero (A : Type (u + 1)) [CommRing A]
    (B : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA) (hB : IsUnit (N : Γ(B, ⊤))) :
    (Etale.affineLinearCoefficientDescent A N hA t B hB 0 ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback A N hA t
        (affineTraceProjection B 0) hB 0) = Iso.refl _ := by
  apply Iso.ext
  change (Etale.affineLinearPullbackId A B).inv.app (Etale.ordinaryFiniteUnit A B) ≫
    (Etale.ordinaryFiniteUnitPullback A (𝟙 B)).hom = 𝟙 _
  rw [Etale.vectorIntegration_identity_unit]
  exact Iso.inv_hom_id_app _ _

private theorem chartAffineCounit_zero (A : Type (u + 1)) [CommRing A]
    (B : Scheme.{u}) [IsNoetherian B] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT) (hB : IsUnit (N : Γ(B, ⊤))) :
    (Etale.affineTraceAdjunction A N hA t D B hB 0).counit.app
      (Etale.ordinaryFiniteUnit A B) = 𝟙 _ := by
  unfold Etale.affineTraceAdjunction
  rfl

-- Normalize the trace before putting it under the adjunction and comparison maps.

private theorem chartAffineTrace_zero (A : Type (u + 1)) [CommRing A] [Finite A]
    (B : Scheme.{u}) [IsNoetherian B] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT) (hB : IsUnit (N : Γ(B, ⊤))) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection B 0)).map
        (Etale.affineLinearCoefficientDescent A N hA t B hB 0 ≪≫
          Etale.vectorIntegrationBaseCoefficientPullback A N hA t
            (affineTraceProjection B 0) hB 0).inv ≫
      (Etale.affineLinearCompactComparison N hN A hA B hB 0).inv ≫
      (Etale.affineTraceAdjunction A N hA t D B hB 0).counit.app
        (Etale.ordinaryFiniteUnit A B) =
      (Etale.unboundedEtaleLowerShriekId A B).hom.app (Etale.ordinaryFiniteUnit A B) := by
  rw [chartAffineCoefficient_zero]
  simp only [Iso.refl_inv]
  erw [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
    (affineTraceProjection B 0)).map_id]
  simp only [Category.id_comp]
  erw [chartAffineCounit_zero, Category.comp_id, Etale.compact_comparison_zero]

-- Separate the identity calculation before the dependent rank induction.

private theorem affineTranspose_unit_coordinates_zero (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] :
    affineTranspose P T aT 0 P.level (annihilates P) =
      (orderedSourceIso P T 0).hom ≫
        AffineOrderedIntegration.integrationTranspose P T aT (unitPlus P T)
          (Etale.ordinaryFiniteUnit (Ring P) T) (unit_properties P T).2 (Iso.refl _) 0 ≫
        (orderedTargetIso P T 0).hom := by
  have hs : (orderedSourceIso P T 0).hom = 𝟙 _ := by
    unfold orderedSourceIso
    exact eq_of_heq (orderedSourceIso_existsUnique P T 0).exists.choose_spec
  have hi : AffineOrderedIntegration.integrationTranspose P T aT (unitPlus P T)
      (Etale.ordinaryFiniteUnit (Ring P) T) (unit_properties P T).2 (Iso.refl _) 0 =
      𝟙 _ := by
    unfold AffineOrderedIntegration.integrationTranspose
    exact eq_of_heq (AffineOrderedIntegration.integrationTranspose_existsUnique
      P T aT _ _ _ _ 0).exists.choose_spec
  have ha : affineTranspose P T aT 0 P.level (annihilates P) =
      affineTransposeRaw P T aT 0 P.level (annihilates P) := by
    unfold affineTranspose
    exact eq_of_heq (affineTranspose_existsUnique P T aT 0 P.level
      (annihilates P)).exists.choose_spec
  rw [hs, hi, Category.id_comp]
  erw [Category.id_comp]
  rw [ha]
  dsimp only [affineTransposeRaw]
  erw [chartAffineTrace_zero]
  have h := congrArg ((comparison (Ring P) T).map)
    (Etale.identityExceptionalAdjunct (Ring P) T (Etale.ordinaryFiniteUnit (Ring P) T))
  exact h

-- The combined site and ordered-coordinate normalizations require a larger elaboration budget.

end AlgebraicGeometry.ProEtale.VectorIntegrationChart
