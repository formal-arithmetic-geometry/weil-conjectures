/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Paper.RetaggingCoefficientTowerTransfer
import Sheaf.Paper.TowerPurityAdjointTransport

/-! # Ground-field retagging of the normalized diagonal orientation

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Step 1, semilinear comparison
(blueprint: lem-pur-orientation-ground-field-retagging).

The finite equality uses the published diagonal orientation. The tower equality is
in the ordinary derived category of strict coefficient towers. Both presentations
use the same underlying compactification and coefficient objects. Two presentations
of the exceptional adjoint are compared by the unique counit-preserving isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting

/-- The two equalities after the stipulated underlying-site identifications.
The first compares Pi for aY and Spec(sigma) composed with aY. In the second,
`aσ` and `a` are the normalized orientations of det-sp-tower-gamma in these two
presentations. The normalized `Purity` records retain their finite diagonal equations;
they are not arbitrary isomorphisms. The common b, o, q and w are the identified
underlying-site operations, section coordinates and strict Tate tower. The same
factorization j,p is used on both sides. The adjoint comparison is explicitly
`rightAdjointUniq`; inverse realization puts the equality in D(Tow), retaining
all quotient transitions before localization.
Source: equivariance proof Step 1, ground-field retagging auxiliary input
(blueprint: lem-pur-orientation-ground-field-retagging). -/
def OrientationGroundFieldRetaggingConclusion (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] : Prop :=
  letI := isNoetherian_of_locallyOfFiniteType aX
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI : HasCompactification f := inferInstance
  (P.diagonalDualizingObject d f
      (aY ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))).hom =
    (P.diagonalDualizingObject d f aY).hom ∧
  ∀ (b : SpTowerShriek.Base P.coefficients.l P.extension)
    (o : SpTowerShriek.Operations P.coefficients.l P.extension b)
    (q : SpTowerCalculus.Coordinates P.coefficients.l P.extension b)
    (Z : Scheme.{u}) (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [IsProper p], j ≫ p = f →
    ∀ (w : SpChartAdmissibility.Twists P.coefficients.l P.extension X)
    (hF : ∀ M : SpTowerCalculus.C P.coefficients.l P.extension b q X,
      spConstructibleTorTowers P.coefficients.l P.extension Y (q.abelian Y)
        ((SpTowerCalculus.F P.coefficients.l P.extension b o q
          (SpTowerGamma.factorization j p)).obj M.obj))
    (Gσ G : SpTowerCalculus.C P.coefficients.l P.extension b q Y ⥤
      SpTowerCalculus.C P.coefficients.l P.extension b q X)
    (adjσ : SpTowerGluing.support P.coefficients.l P.extension b o q
      (SpTowerGamma.factorization j p) hF ⊣ Gσ)
    (adj : SpTowerGluing.support P.coefficients.l P.extension b o q
      (SpTowerGamma.factorization j p) hF ⊣ G)
    (lvσ : SpTowerGluing.Levels P.coefficients.l P.extension b o q
      (SpTowerGamma.factorization j p) hF Gσ adjσ)
    (lv : SpTowerGluing.Levels P.coefficients.l P.extension b o q
      (SpTowerGamma.factorization j p) hF G adj)
    (aσ : SpTowerGamma.Purity P.coefficients.l P.extension b o q j p d w hF Gσ adjσ lvσ)
    (a : SpTowerGamma.Purity P.coefficients.l P.extension b o q j p d w hF G adj lv),
    (SpTowerCalculus.realization P.coefficients.l P.extension b X (q.abelian X)).inverse.map
        (aσ.orientation.hom ≫
          (SpTowerGamma.realization P.coefficients.l P.extension b q X).map
            ((adjσ.rightAdjointUniq adj).hom.app
              ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y, aσ.unit_mem⟩)) =
      (SpTowerCalculus.realization P.coefficients.l P.extension b X (q.abelian X)).inverse.map
        a.orientation.hom

/-- Retagging the structural field maps preserves both normalized orientations.
Source: literature/blueprint/latest, equivariance of purity and trace proof, Step 1
(blueprint: lem-pur-orientation-ground-field-retagging).

Proof:
1. Fix m >= 1 and R = Z/ell^m. On every etale coordinate chart U -> A^d_V,
   lem-pur-retagging-coordinate-orientations identifies the two normalized maps.
   The underlying diagonal, deformation family and integration normalization agree,
   with the same underlying compactification and counit-preserving adjoint comparison.
2. The charts of sbc-thm-etale-local-normal-form cover X. Invert Pi using
   thm-pur-diagonal-dualizing-object. The difference of the two maps, composed with
   Pi inverse, is an endomorphism of R_X(d)[2d] vanishing on every chart. Remove
   the shift; lem-weil-pbc-derived-single-fully-faithful identifies it with a sheaf
   endomorphism. Uniqueness in lem-pur-sheaf-hom-cover-gluing makes it zero globally.
3. Apply lem-pur-retagging-coefficient-tower-transfer to these equalities for all m.
   Since ell lies in (varpi_E), ell^n annihilates A_E,n for every n >= 1, giving
   the finite equality without a ramification restriction. Its tower assertion
   identifies the normalized strict-tower maps in their ordinary derived category,
   retaining quotient transitions. The adjunction comparison in the formula is the
   unique counit-preserving one. Thus both asserted orientation equalities hold. -/
theorem orientation_ground_field_retagging (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
    (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] (_hf : f ≫ aY = aX) :
    P.OrientationGroundFieldRetaggingConclusion σ aX aY d f := by
  let := isNoetherian_of_locallyOfFiniteType aX
  let := isNoetherian_of_locallyOfFiniteType aY
  let : HasCompactification f := inferInstance
  -- The structural map occurs only in IsUnit proofs in the defining normalization.
  constructor
  · rfl
  · intro b o q Z j hj p hp hfac w hF Gσ G adjσ adj lvσ lv aσ a
    subst f
    obtain ⟨a', ha'⟩ := SpTowerGamma.purity_rightAdjoint_transport
      P.coefficients.l P.extension b o q j p d w hF Gσ G adjσ adj lvσ lv aσ
    have hprime : ∀ (m : ℕ) (hm : 1 ≤ m),
        RetaggingPrimeOrientation
          (finiteGeneralRingPrimeSetting P.field P.coefficients.l
            P.coefficients.different m hm) σ d (j ≫ p) aY := by
      intro m hm
      rfl
    rw [← ha']
    exact retagging_strict_tower_orientation_transfer P σ b o q aX aY
      j p d _hf w hF G adj lv a a' hprime

end WeilConjectures.PurityFiniteSetting
