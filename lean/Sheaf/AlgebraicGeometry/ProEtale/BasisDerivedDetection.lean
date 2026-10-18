/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Derived sections on the affine ind-etale basis detect isomorphisms

Source: Weil conjectures blueprint, `lem-weil-pbc-basis-derived-detection`, order 1288
(blueprint: lem-weil-pbc-basis-derived-detection).

Second reading by NI: the statement and constructions match the node exactly.

The small model `AsSmall` changes neither the objects nor the covering families:
its equivalence transports the given small pro-etale topology. Constant rings,
module sheaves and derived categories below use the recorded Mathlib definitions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The recorded constant ring sheaf transported to this small presentation along
Mathlib's canonical site equivalence; this reuses `Scheme.proEtaleConstantRing`.
Source: blueprint, order 1288, coefficient convention
(blueprint: lem-weil-pbc-basis-derived-detection). -/
noncomputable abbrev smallConstantRing (X : Scheme.{u}) (R : Type u) [CommRing R] :
    Sheaf (proEtaleModelTopology X) RingCat.{u + 1} :=
  ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj
      ((sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing X R))

/-- Module sheaves on the chosen small presentation of the small pro-etale site.
Source: blueprint, order 1288, the category A
(blueprint: lem-weil-pbc-basis-derived-detection). -/
noncomputable abbrev smallModules (X : Scheme.{u}) (R : Type u) [CommRing R] :=
  ringedSiteModules.{u + 1} (smallConstantRing X R)

/-- The usual injective-existence instance for module sheaves on the chosen small site.
Source: Stacks, Section 07A5; blueprint, order 1288, proof step 1
(blueprint: lem-weil-pbc-basis-derived-detection). -/
noncomputable instance smallModulesEnoughInjectives (X : Scheme.{u})
    (R : Type u) [CommRing R] : EnoughInjectives (smallModules X R) :=
  @IsGrothendieckAbelian.enoughInjectives _ _ _
    (SheafOfModules.isGrothendieckAbelian (smallConstantRing X R))

/-- The standard localization model of the bounded-below derived category.
Source: blueprint, order 1288, D+(A)
(blueprint: lem-weil-pbc-basis-derived-detection). -/
noncomputable abbrev smallDerivedPlus (X : Scheme.{u}) (R : Type u) [CommRing R] :=
  @DerivedCategory.Plus (smallModules X R) _ _ (HasDerivedCategory.standard _)

/-- Derived evaluation at a pro-etale object, computed by bounded-below injectives.
Source: blueprint, order 1288, definition of RΓ(W,-)
(blueprint: lem-weil-pbc-basis-derived-detection).
This is Mathlib's right derived functor, not a choice of an arbitrary comparison functor. -/
noncomputable def smallDerivedEvaluation (X : Scheme.{u}) (R : Type u) [CommRing R]
    (W : X.ProEt) :
    smallDerivedPlus X R ⥤
      @DerivedCategory.Plus
        (ModuleCat.{u + 1} ((smallConstantRing X R).obj.obj (op (AsSmall.up.obj W))))
        _ _ (HasDerivedCategory.standard _) :=
  letI := HasDerivedCategory.standard (smallModules X R)
  letI := HasDerivedCategory.standard
    (ModuleCat.{u + 1} ((smallConstantRing X R).obj.obj (op (AsSmall.up.obj W))))
  letI : (SheafOfModules.evaluation (smallConstantRing X R)
      (op (AsSmall.up.obj W))).Additive :=
    inferInstanceAs ((SheafOfModules.forget (smallConstantRing X R) ⋙
      PresheafOfModules.evaluation (smallConstantRing X R).obj
        (op (AsSmall.up.obj W))).Additive)
  (SheafOfModules.evaluation (smallConstantRing X R)
    (op (AsSmall.up.obj W))).rightDerivedFunctorPlus

/-- Derived evaluation on every affine ind-etale basis object detects an isomorphism.
Source: Weil conjectures blueprint, order 1288
(blueprint: lem-weil-pbc-basis-derived-detection).

Proof for stage 3:
1. On the chosen small model module sheaves are Grothendieck abelian and have enough
   injectives. Represent K and L by bounded-below injective complexes. They are K-injective,
   so the conjugate of u is represented by a chain map a between them.
2. Apply the published `AlgebraicGeometry.proEtale_restriction_injectives`
   (lem-weil-pbc-proetale-restriction-injectives). Restriction preserves injectives, so
   evaluation of these complexes computes derived sections. The hypothesis and
   `DerivedCategory.Plus.isIso_iff` imply that every evaluated a on a basis object is a
   quasi-isomorphism.
3. Form the ordinary cone C(a). Evaluation preserves its finite sums and differentials,
   so its evaluation is the cone of the evaluated map and has zero cohomology.
4. The presheaf U ↦ H^n(C(a)(U)) sheafifies to the cohomology sheaf H^n(C(a)), by exact
   module sheafification and the kernel-image calculation. This does not identify its
   values with sections of the cohomology sheaf.
5. This presheaf vanishes on every basis object. Maps from it to any sheaf vanish locally
   on a basis cover, hence globally by separation. The sheafification adjunction then
   makes the identity of its sheafification zero. Thus every H^n(C(a)) vanishes.
6. The cone criterion makes a a quasi-isomorphism, hence its localization and u invertible.
-/
theorem isIso_of_isIso_basis_derivedEvaluation (X : Scheme.{u}) [IsAffine X]
    (R : Type u) [CommRing R] {K L : smallDerivedPlus X R} (f : K ⟶ L)
    (h : ∀ W : X.AffineProEt,
      IsIso ((smallDerivedEvaluation X R ((AffineProEt.toProEt X).obj W)).map f)) :
    IsIso f := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
