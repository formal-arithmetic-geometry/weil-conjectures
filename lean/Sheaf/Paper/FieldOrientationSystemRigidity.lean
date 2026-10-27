/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import Sheaf.Paper.FieldOrientationSystemHeart

/-! Single-coefficient concentration and rigidity of normalized tower orientations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.FieldOrientationSystem
open FieldShriekSystem FieldExceptionalSystem

variable (P : PurityFiniteSetting.{u}) (D : Models P)

variable {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (p : Z ⟶ Y) [IsProper p]
  (b : FieldShriekSystem.Laws P D (SpTowerGamma.factorization j p))
  (a : Domains P D (SpTowerGamma.factorization j p))
  (A : Adjoints P D (SpTowerGamma.factorization j p) b a)

/-- A normalized diagonal orientation has one cohomological degree, is induced from
its canonical heart sheaves, and is the only map with its finite normalization.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2), the
rank-one orientation argument; parent node steps 1, 4 and 5.
(blueprint: new-sp-field-orientation-system-rigidity).

Proof:
Evaluate the ordered Tate line using its root-normalized lineWord. A finite Tate
line is a locally free degree-zero sheaf with shift 2d, so every evaluation is
concentrated in degree -2d. Exact evaluation commutes with homology, and a strict
sheaf-system is zero when all its levels are zero. Thus the ordered line is
concentrated there. Transport this along o to the dualizing system.
After shifting by -2d, use the single/H-zero isomorphism, normalized by its induced
map on H-zero, for both objects. Full faithfulness of single recovers the unique
heart map of o. Naturality of evaluationSingleShift gives the beta/evaluation
characterization in IsHeartInduced; faithfulness of the finite single and shift
functors proves the reverse implication and uniqueness of beta.
For any other normalized orientation, its finite diagonal maps equal those of o:
the diagonal/DNC normalization is unique, as are the counit-normalized right-adjoint
comparisons and the unit comparison. Remove the shift and use fullness of single
to express both arrows as maps of the same heart sheaves. Faithfulness of finite
single and shift then gives equality of every component of these heart maps.
Strict sheaf-system extensionality gives their equality, and shifting back proves
equality of the original arrows. This uses evaluation only on shifted sheaves.
-/
theorem field_orientation_system_rigidity
    [IsNoetherian X]
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [(j ≫ p).IsOver (Spec (.of P.field.k))] [IsSeparated (j ≫ p)]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (E : Index P) (w : Coordinates P D E X) (v : Coordinates P D E Y)
    (h : normalized P D E Y (SpTowerGamma.unit P.coefficients.l E.val Y))
    (o : line P D w d ≅ omega P D j p b a A E h)
    (ho : IsOrientation P D j p b a A E d w v h o.hom) :
    (∀ i : ℤ, i ≠ -2 * (d : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj (omega P D j p b a A E h))) ∧
    IsHeartInduced P D w d (omega P D j p b a A E h) o.hom ∧
    (∀ f : line P D w d ⟶ omega P D j p b a A E h,
      IsOrientation P D j p b a A E d w v h f → f = o.hom) := by sorry

end AlgebraicGeometry.ProEtale.FieldOrientationSystem
