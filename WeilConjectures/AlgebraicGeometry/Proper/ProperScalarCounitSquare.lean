/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement

/-!
# Direct-image restriction and the scalar counit square

Source: Stacks Project, Cohomology on Sites, Tags 07A6, 0D6D and 0D6E;
blueprint det-sp-tower-gluing, Levels paragraph
(blueprint: lem-sp-proper-scalar-counit-square).

The scalar extension, geometric adjunction and balanced pullback comparison are the
published canonical constructions. The direct-image comparison below specializes the
normalized ring-sheaf comparison, in the inverse direction. The theorem identifies its
resolution normalization and states both counit equations on the entire unbounded category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Exact termwise scalar restriction along the specified constant-ring map.
Source: Stacks Tags 03DA and 07A6
(blueprint: lem-sp-proper-scalar-counit-square). -/
abbrev directImageScalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    T.proEtaleDerivedCategory B ⥤ T.proEtaleDerivedCategory A :=
  (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) φ)).mapDerivedCategory

/-- The representative-normalized extension/restriction adjunction already used by the
canonical balancing comparison. Source: Stacks Tag 07A6
(blueprint: lem-sp-proper-scalar-counit-square). -/
abbrev directImageScalarAdjunction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    directImageScalarExtension φ T ⊣ directImageScalarRestriction φ T :=
  proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)

end AlgebraicGeometry.ProEtale
