/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantSupportProjection
public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint

/-!
# Scalar restricted constant support projection

Source: Stacks Tag 0GL6 and the coefficientwise support comparison.
(blueprint: lem-exc-support-constant-projection-after-restriction)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The constant coefficient projection at the scalar-restricted coefficient object is an
isomorphism under the ambient support adjunction.
Source: Stacks Tag 0GL6; (blueprint: lem-exc-support-constant-projection-after-restriction).
Proof: use the ambient support adjunction to obtain the discrete-colimit preservation
hypothesis, then apply the generic constant-support projection theorem to the scalar-restricted
constant coefficient object. -/
theorem exceptionalSupport_constantProjection_isIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {G : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A}
    (_a : sfAmbientCompactSupportCandidate A c ⊣ G)
    (K : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).app
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj K)).app
      ((constantSheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ModuleCat.restrictScalars.{u + 1} φ.ulift).obj
            (ModuleCat.of (ULift.{u + 1, u} B) (ULift.{u + 1, u} B)))))) := by
  sorry

end WeilConjectures
