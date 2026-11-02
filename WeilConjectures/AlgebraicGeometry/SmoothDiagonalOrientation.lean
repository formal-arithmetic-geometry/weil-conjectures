/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.RelativeTangentBundle.RelativeTangentBundle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # The normalized smooth diagonal orientation

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
_section.md and sk-prop-sp-orientation.proof.md
(blueprint: sk-prop-sp-orientation).

The ordinary finite-coefficient orientation retains the actual diagonal, normalized
Rees deformation and inverse vector-integration equation. Its pro-etale realization
is specified using the comparison-adjunction unit, with both endpoints in Dctf.
The field is finite or algebraically closed; no fixed finite-field closure is imposed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.ProEtale

/-- The canonical orientation of a separated smooth morphism of pure dimension d.
The coefficient is the existing size presentation of Z/(ell^n), and the target is
its ordered root-line tensor power shifted by +2d. The pro-etale exceptional object
is the finite etale computation of the recorded relative dualizing complex.

`OrientationNormalized` is the actual equation of the diagonal base-change factor
and the unique t=1-normalized Rees specialization with the vector-bundle adjoint,
including its associated-graded cone transport and zero-section restriction.
The displayed comparison-unit equation fixes the pro-etale arrow itself.

Source: latest blueprint sk-prop-sp-orientation, statement and displayed composite
(blueprint: sk-prop-sp-orientation).

Proof plan:
1. The self-product projection is smooth of dimension d and separated finite type.
   Its closed diagonal is a regular section. Centred coordinates identify Sym of
   its conormal with its associated graded, including the augmentation; the canonical
   conormal identification with Omega identifies this normal bundle with T_(X/Y).
   This gives the Geometry certificate, also for d=0 and the empty source.
2. Apply smooth exceptional self-product base change at the unit and restrict by
   the diagonal. The derived composition and identity comparisons give the first
   factor from omega_f to the diagonal pullback of omega_p1, in that direction.
3. Apply finite-ring section deformation at N=ell^n. Its unique family comparison
   is the identity at t=1. Invert its zero-fibre restriction and transport through
   the homogeneous-normalized Rees/associated-graded and conormal comparisons.
4. Pull back inverse integration-normalized vector purity along zero. The root-line
   pullback comparison identifies its target with Lambda_X(d)[2d]. This composite
   satisfies OrientationNormalized. Uniqueness follows by cancellation of the bundle
   adjoint and uniqueness of the normalized family. Rank-zero integration is identity.
5. Finite etale/pro-etale comparison preserves these counits and transposes. The
   comparison-adjunction unit supplies finiteGeneralRingDualizingUnitMap. Its inverse
   followed by the comparison image of the ordinary orientation gives theta and the
   displayed equation. The root line is bounded constructible with finite Tor
   amplitude; the isomorphism gives the same properties for omega_f. Fullness and
   faithfulness transport uniqueness to the actual small pro-etale category.
-/
theorem existsUnique_smoothDiagonalOrientation
    (ell : ℕ) [Fact ell.Prime] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (p : ℕ) [Fact p.Prime] [CharP k p] (hEll : ell ≠ p)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] (d : ℕ)
    [SmoothOfRelativeDimension d f.left] :
    letI := isNoetherian_of_locallyOfFiniteType X.hom
    letI := isNoetherian_of_locallyOfFiniteType Y.hom
    letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    letI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
    letI : QuasiCompact f.left := inferInstance
    letI : HasCompactification f.left := HasCompactification.of_over f
    let A := coefficient.{u} ell n
    let hA : ((ell ^ n : ℕ) : A) = 0 := CharP.cast_eq_zero _ _
    ∃ hX : IsUnit ((ell ^ n : ℕ) : Γ(X.left, ⊤)),
      ∃ G : Etale.FiniteRingSectionDeformation.Geometry d
          (pullback.fst f.left f.left) (pullback.diagonal f.left),
        ∃! theta : (exceptional A f.left).obj (finiteGeneralRingUnit A Y.left) ≅
            (comparison A X.left).obj (line A (ell ^ n) hA X.left d),
          ∃ alpha : Etale.dualizingComplex A f.left ≅ line A (ell ^ n) hA X.left d,
            OrientationNormalized A (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
                hA f.left d G hX alpha ∧
            IsCtf A X.left
                ((exceptional A f.left).obj (finiteGeneralRingUnit A Y.left)) ∧
            IsCtf A X.left ((comparison A X.left).obj (line A (ell ^ n) hA X.left d)) ∧
            finiteGeneralRingDualizingUnitMap A f.left ≫ theta.hom =
              (comparison A X.left).map alpha.hom := by
  sorry

end AlgebraicGeometry.ProEtale
