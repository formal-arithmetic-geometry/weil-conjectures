/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData
public import Sheaf.AlgebraicGeometry.FieldActionTransportData
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-! # Canonical normalized point scalar data

Source: main-20261015 blueprint, six-functors direct-images proof paragraph (3),
point coefficient projection; the normalized point and scalar adjunctions.
(blueprint: def-sfb-canonical-point-scalar-comparison).

The existing data types fix all underlying functors, adjunction units, counits and
Hom transposes. Their unique inhabitants supply the canonical point projection;
no arbitrary comparison or existence-only choice is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FieldActionTransport
open CondensedGalois

/-- The actual point module adjunction has a unique normalized presentation.
Source: direct-images proof (3), p_Y and its module adjunction
(blueprint: def-sfb-canonical-point-scalar-comparison).

Proof: the composite point inverse image is exact and strong monoidal. Its
monoidal adjunction lifts by Adjunction.mapModAdjunction to the specified
pointPull and pointModules, with underlying unit and counit those of
pointAdjunction. Limits and colimits of modules are created on underlying
sheaves, giving exactness of pointPull; pointModules is additive as a right
adjoint between additive categories. The forgetful functors are faithful,
so the prescribed underlying unit determines the adjunction uniquely.
All other fields are propositions and hence proof irrelevant. -/
theorem canonicalPointAdjunction_existsUnique (R : Coefficients.{u}) (Y : Scheme.{u}) :
    ∃! d : PointAdjunctionData R Y, True := by
  sorry

/-- The uniquely normalized adjunction of the existing point module functors.
Source: direct-images proof (3), p_Y
(blueprint: def-sfb-canonical-point-scalar-comparison). -/
@[instance_reducible]
def canonicalPointAdjunction (R : Coefficients.{u}) (Y : Scheme.{u}) :
    PointAdjunctionData R Y :=
  (canonicalPointAdjunction_existsUnique R Y).exists.choose

attribute [instance] canonicalPointAdjunction

/-- The point scalar square is uniquely determined by its ordinary restriction
square and its Hom-transpose equation, including for nonflat scalar maps.
Source: direct-images proof (3), K-flat scalar normalization
(blueprint: def-sfb-canonical-point-scalar-comparison).

Proof: strong monoidal point pullback preserves colimits and takes flat modules
and K-flat complexes to flat modules and K-flat complexes. On such a resolution,
the balanced tensor comparison sends b tensor m to b tensor m and preserves
m maps to 1 tensor m. Localize to obtain the derived scalar exchange. The
ordinary mapModComapIso localizes to precisely the square.restriction specified
by PointScalar.normalization. The ordinary balanced-tensor adjunction and the
derived adjunction universal property give square.transpose. Any two extensions
with this transpose equation have the same adjunct on every morphism; putting
the identity morphism in that equation proves equality of their components.
The restriction is fixed by normalization, and every remaining field is a proof. -/
theorem canonicalPointScalar_existsUnique {R R' : Coefficients.{u}} (φ : R ⟶ R')
    (Y : Scheme.{u}) : ∃! c : PointScalar φ Y, True := by
  sorry

/-- The unique scalar square with the recorded restriction and transpose normalizations.
Source: direct-images proof (3), point coefficient projection
(blueprint: def-sfb-canonical-point-scalar-comparison). -/
def canonicalPointScalar {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :
    PointScalar φ Y :=
  (canonicalPointScalar_existsUnique φ Y).exists.choose

end AlgebraicGeometry.ProEtale.FieldActionTransport
