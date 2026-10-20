/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.RationalStalkExact
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.ConstructiblePullbackTExact
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.Paper.LocalFrobeniusTransportNormalization
import Sheaf.SixFunctors.FrobeniusPointTransportNatural

/-! # Local Frobenius under rational Weil-sheaf pullback

Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2
(blueprint: lem-fd-weil-pullback-local-frobenius).

The pullback, fibres and local geometric Frobenius are the existing common-stage
constructions. Eigenvalues are characteristic-polynomial roots with algebraic multiplicity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The multiset of local geometric Frobenius eigenvalues, retaining multiplicities.
The finite-dimensionality used by charpoly is supplied by the actual point category.
Source: blueprint Step 2, multiset E of local eigenvalues
(blueprint: lem-fd-weil-pullback-local-frobenius). -/
def fdWeilLocalEigenvalues (F : sfCommonStageWeilSheaf D c.l c.different Y₀ c.Qbar)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    Multiset c.Qbar :=
  letI : FiniteDimensional c.Qbar
      ((wfSheafFibre c.l c.Qbar D c.different Y₀
        (localClosedPoint D Y₀ y ι hι)).obj F) :=
    DerivedCategory.coefficientQbarCohomology_finite c.l c.Qbar 0
    ((wfPointFunctor c.l c.Qbar D c.different Y₀
      (localClosedPoint D Y₀ y ι hι)).obj F.obj.carrier)
  (wfSheafClosedFrobenius c.l c.Qbar D c.different Y₀ F y ι hι).hom.charpoly.roots

/-- Derived inverse image preserves the constructible heart. A closed point maps to a
closed point, its residue extension has positive finite degree e, and q_z = q_x^e.
For every compatible pair of geometric lifts, the fibre comparison is natural in the
Weil sheaf, intertwines geometric Frobenius with its e-th power, and raises every
local eigenvalue to that power, with algebraic multiplicity.
Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2
(blueprint: lem-fd-weil-pullback-local-frobenius).
Proof: (1) Apply constructible_pullback_t_exact at every finite coefficient field and
in the common-stage category. The canonical Frobenius square defines the induced Weil
structure on the pulled-back heart object, exactly zlWeilPull.
(2) By lem-kun-closed-point-field, κ(z) is finite over k₀. Its subfield κ(x) is finite
as well, so x is closed. The tower law and counting tuples in field bases give positive
finite e and q_z = q_x^e.
(3) At one finite coefficient field containing the object, Weil maps and their inverse
equations, invert the canonical pullback-composition comparison for zbar followed by f.
Apply the point-fibre functor. Naturality and scalar compatibility of
lem-trf-integral-pullback-comparison-realization and
lem-weil-point-sections-scalar-extension descend this isomorphism to common-stage fibres.
(4) For n divisible by both residue degrees, naturality of the iterated point transports
from lem-weil-frobenius-point-transport-natural and their associative composition
comparisons give c G_Y^n(beta_n) t_X = t_Y c, with the appropriate point-fibre functors.
(5) Induction on n gives theta_X^[n] = f^*(theta_Y^[n]) beta_n. At the degree of z,
substitute this into the preceding square and use naturality for theta_Y^[n]. This
identifies c F_z with the corresponding return operator at x followed by c.
(6) Split the list of point transports into blocks of length d = [κ(x):k₀]. Naturality
for theta_Y^[rd] and the Weil-iterate recurrence identify the (r+1)-block return with
F_x times the r-block return. Induction identifies the e-block return with F_x^e.
(7) The scalar/composition equation and the scalar equation of
lem-trf-local-frobenius-transport-normalization identify every factor after coefficient
extension, including identities and towers. Hence the equation holds in the common-stage
category. Take H^0 to obtain the asserted equation on the rational fibres.
(8) Triangularize F_x over Qbar. The diagonal of its e-th power is the e-th power of
each diagonal entry, with repetitions retained. Conjugacy preserves the characteristic
polynomial, giving the multiset equality; the empty diagonal covers the zero sheaf. -/
theorem fdWeilPullbackLocalFrobenius
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] [IsSeparated Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (∀ F : sfCommonStageWeilSheaf D c.l c.different Y₀ c.Qbar,
      sfCommonStageHeartProperty c.l (D.geometricFiber X₀).left c.Qbar
        ((zlPull D c.l c.different c.Qbar f₀).obj F.obj.carrier)) ∧
    ∀ z : {z : X₀.left // z ∈ closedPoints X₀.left},
      ∃ hx : f₀.left.base z.val ∈ closedPoints Y₀.left,
        (f₀.left.residueFieldMap z.val).hom.Finite ∧
        1 ≤ f₀.left.residueDegree z.val ∧
        Nat.card (X₀.left.residueField z.val) =
          Nat.card (Y₀.left.residueField (f₀.left.base z.val)) ^
            f₀.left.residueDegree z.val ∧
        ∀ (ιz : X₀.left.residueField z.val →+* D.k)
          (hz : ιz.comp (X₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
          (ιx : Y₀.left.residueField (f₀.left.base z.val) →+* D.k)
          (hxι : ιx.comp (Y₀.hom.residueFieldAlgebraMap (f₀.left.base z.val)) =
            algebraMap D.k₀ D.k),
          localClosedPoint D X₀ z ιz hz ≫ zlFiberMap D f₀ =
            localClosedPoint D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hxι →
          ∃ comparison :
            zlWeilPull D c.l c.different c.Qbar f₀ ⋙
                wfSheafFibre c.l c.Qbar D c.different X₀
                  (localClosedPoint D X₀ z ιz hz) ≅
              wfSheafFibre c.l c.Qbar D c.different Y₀
                (localClosedPoint D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hxι),
            ∀ F : sfCommonStageWeilSheaf D c.l c.different Y₀ c.Qbar,
              wfSheafClosedFrobenius c.l c.Qbar D c.different X₀
                  ((zlWeilPull D c.l c.different c.Qbar f₀).obj F) z ιz hz ≫
                  comparison.hom.app F =
                comparison.hom.app F ≫
                  ModuleCat.ofHom
                    ((wfSheafClosedFrobenius c.l c.Qbar D c.different Y₀ F
                      ⟨f₀.left.base z.val, hx⟩ ιx hxι).hom ^
                        f₀.left.residueDegree z.val) ∧
              fdWeilLocalEigenvalues D c X₀
                  ((zlWeilPull D c.l c.different c.Qbar f₀).obj F) z ιz hz =
                (fdWeilLocalEigenvalues D c Y₀ F
                  ⟨f₀.left.base z.val, hx⟩ ιx hxι).map
                    (fun α ↦ α ^ f₀.left.residueDegree z.val) := by
  sorry

end WeilConjectures
