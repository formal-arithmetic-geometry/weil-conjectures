/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates

/-! # The affine diagonal orientation at the coefficient unit

Source: the model paragraph of the smooth-purity unit, diagonal/DNC normalization.
(blueprint: lem-pur-projection-unit-integration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AffineSpacePurity

/-- The ordinary ordered affine counit mate, with its coefficient descent and its
comparison-adjunction unit. This constructs the arrow without a diagonal orientation.
Source: the model paragraph, integration at the coefficient unit
(blueprint: lem-pur-projection-unit-integration). -/
def projectionUnitIntegrationRaw (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := affineTraceNoetherian Y d
  let f := affineTraceProjection Y d
  let hN := pow_pos P.coefficients.prime.out.pos P.level
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates
  let D := Etale.projectiveLineTraceDatum P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) (affineTraceTower Y d)).mapDerivedCategory.map
      (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d) ≫
    (P.diagonalDualizingComparison f).inv

/-- The coefficient-unit integration mate in the common recursive affine model.
The heterogeneous equality fixes the arrow itself.
Source: the identical recursive tower definitions
(blueprint: lem-pur-projection-unit-integration).
Proof: both dependent tower/projection pairs start at (Y,id) and adjoin one affine
line at each successor. Induction identifies these pairs. Transport the raw arrow
along this equality; proof irrelevance identifies compactifiability instances.
Two transported arrows satisfying the heterogeneous equality are equal. -/
theorem projectionUnitIntegration_existsUnique (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ) :
    letI := (projection_geometry Y d).2
    ∃! z : P.diagonalTwist (iteratedAffineLine Y d) d ⟶
      P.diagonalDualizing (iteratedAffineLineProj Y d),
      HEq z (projectionUnitIntegrationRaw P Y aY d) := by
  have ht (T : Scheme.{u}) (n : ℕ) :
      (⟨affineTraceTower T n, affineTraceProjection T n⟩ : Σ X : Scheme.{u}, X ⟶ T) =
        ⟨iteratedAffineLine T n, iteratedAffineLineProj T n⟩ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ T ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ : Σ X : Scheme.{u}, X ⟶ T)) ih
  have transport (X X' : Scheme.{u}) (f : X ⟶ Y) (g : X' ⟶ Y)
      [HasCompactification f] [HasCompactification g]
      (h : (⟨X, f⟩ : Σ X : Scheme.{u}, X ⟶ Y) = ⟨X', g⟩)
      (z : P.diagonalTwist X d ⟶ P.diagonalDualizing f) :
      ∃ z' : P.diagonalTwist X' d ⟶ P.diagonalDualizing g, HEq z' z := by
    cases h
    exact ⟨z, HEq.rfl⟩
  let := isNoetherian_of_locallyOfFiniteType aY
  let := affineTraceNoetherian Y d
  let := (projection_geometry Y d).2
  obtain ⟨z, hz⟩ := transport _ _ (affineTraceProjection Y d)
    (iteratedAffineLineProj Y d) (ht Y d) (projectionUnitIntegrationRaw P Y aY d)
  exact ⟨z, hz, fun z' hz' ↦ eq_of_heq (hz'.trans hz.symm)⟩

/-- The independently constructed integration transpose at the coefficient unit.
Source: the ordered affine counit (blueprint: lem-pur-projection-unit-integration). -/
def projectionUnitIntegration (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) :=
  (projectionUnitIntegration_existsUnique P Y aY d).exists.choose

private theorem projectionTrace_smooth (Y : Scheme.{u}) (d : ℕ) :
    SmoothOfRelativeDimension d (affineTraceProjection Y d) := by
  induction d with
  | zero => exact inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 Y))
  | succ d ih =>
    let := ih
    have hline : SmoothOfRelativeDimension 1
        (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d) := by
      simpa using (AffineSpace.smoothOfRelativeDimension_over
        PUnit.{u + 1} (affineTraceTower Y d))
    let := hline
    simpa only [affineTraceProjection, affineTraceTower, Nat.add_comm] using
      (smoothOfRelativeDimension_comp
        (f := AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d)
        (affineTraceProjection Y d) (n := 1) (m := d))

private theorem projectionUnitIntegrationRaw_normalized (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ)
    [SmoothOfRelativeDimension d (affineTraceProjection Y d)] :
    letI := isNoetherian_of_locallyOfFiniteType aY
    letI := affineTraceNoetherian Y d
    (P.diagonalDualizingObject d (affineTraceProjection Y d) aY).inv =
      projectionUnitIntegrationRaw P Y aY d := by
  let := isNoetherian_of_locallyOfFiniteType aY
  let := affineTraceNoetherian Y d
  let f := affineTraceProjection Y d
  let X := affineTraceTower Y d
  let hN := pow_pos P.coefficients.prime.out.pos P.level
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates
  let D := Etale.projectiveLineTraceDatum P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates
  let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  obtain ⟨e, he, hθ⟩ := (P.existsUnique_diagonalDualizingObject d f aY).exists.choose_spec
  have hh := he t D N X (𝟙 X) (𝟙 X) (by simp only [Category.id_comp]; rfl)
  have hm : (Etale.ordinaryFinitePullback P.Coefficient (𝟙 X)).map e.inv =
      (Etale.ordinaryFinitePullback P.Coefficient (𝟙 X)).map
        (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d) := by
    apply (cancel_mono (P.diagonalEtaleLocality N (𝟙 X) f).hom).1
    simp only [f, X, diagonalDualizingCongr, eqToIso_refl, Iso.refl_hom,
      Category.comp_id, Iso.hom_inv_id_assoc] at hh
    exact hh
  let hi := Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) X
  have heq : e.inv = P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d := by
    apply (cancel_epi (hi.hom.app _)).1
    calc
      _ = (Etale.ordinaryFinitePullback P.Coefficient (𝟙 X)).map e.inv ≫
          hi.hom.app _ := (hi.hom.naturality e.inv).symm
      _ = _ := congrArg (fun z ↦ z ≫ hi.hom.app _) hm
      _ = _ := hi.hom.naturality _
  exact (congrArg Iso.inv hθ).trans (by
    simp only [Iso.trans_inv, Functor.mapIso_inv, heq]
    rfl)

/-- On the coordinate projection the inverse specified diagonal orientation is
exactly the independently constructed coefficient-unit integration transpose.
This compares only the dualizing object, with no arbitrary coefficient K.
Source: smooth-purity model paragraph, diagonal/DNC calculation, Steps 3--6 of
lem-pur-projection-purity-agreement
(blueprint: lem-pur-projection-unit-integration).

Proof: identify the two recursive tower/projection pairs. Apply the normalized
diagonal orientation at this projection. Its ordinary representative satisfies
DiagonalOrientationNormalization on every coordinate chart. Take the identity
chart of the whole affine tower and the projectiveLineTraceTransport and datum
at diagonalExponent. Both source-etale locality maps are then the same identity
locality comparison. The two Tate pullback maps cancel. Cancel the common
invertible locality map and the exact identity pullback; the remaining equation
says that the representative's inverse is diagonalAffineMate. The unit comparison
in existsUnique_diagonalDualizingObject gives precisely the stated pro-etale
arrow. Equivalently, the diagonal translation preserves the trace, the normalized
DNC comparison is identity on the standard pair, and zero restriction of the
inverse vector integration cancels the diagonal base-change comparison. The
normal frame is the ordered coordinate-difference frame, so no determinant or
sign enters. The rank-zero tower and its counit are identities; the same formulas
apply to the empty base and all positive, including ramified, coefficient levels. -/
theorem projection_diagonal_unit_integration (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ) :
    letI := (projection_geometry Y d).1
    letI := projection_smooth Y d
    (P.diagonalDualizingObject d (iteratedAffineLineProj Y d) aY).inv =
      projectionUnitIntegration P Y aY d := by
  have ht (T : Scheme.{u}) (n : ℕ) :
      (⟨affineTraceTower T n, affineTraceProjection T n⟩ : Σ X : Scheme.{u}, X ⟶ T) =
        ⟨iteratedAffineLine T n, iteratedAffineLineProj T n⟩ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ T ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ : Σ X : Scheme.{u}, X ⟶ T)) ih
  have transport (X X' : Scheme.{u}) (f : X ⟶ Y) (g : X' ⟶ Y)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
      [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d g]
      (h : (⟨X, f⟩ : Σ X : Scheme.{u}, X ⟶ Y) = ⟨X', g⟩) :
      HEq (P.diagonalDualizingObject d f aY).inv
        (P.diagonalDualizingObject d g aY).inv := by
    cases h
    rfl
  let := projectionTrace_smooth Y d
  let := (projection_geometry Y d).1
  let := projection_smooth Y d
  have ho := transport _ _ (iteratedAffineLineProj Y d) (affineTraceProjection Y d)
    (ht Y d).symm
  have hn := projectionUnitIntegrationRaw_normalized P Y aY d
  have hz := (projectionUnitIntegration_existsUnique P Y aY d).exists.choose_spec
  exact eq_of_heq (ho.trans ((heq_of_eq hn).trans hz.symm))

end WeilConjectures.PurityFiniteSetting
