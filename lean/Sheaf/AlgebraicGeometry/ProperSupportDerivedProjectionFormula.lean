/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Derived projection formula for a complex with proper support

Source: Stacks Project, Tags 08EV (support reduction) and 08EU (projection formula).
(blueprint: lem-pc-proper-support-derived-projection-formula)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Proper support permits the derived projection formula without assuming f quasi-compact.
Source: Stacks Project, Tag 08EV, proof, support reduction and first displayed equality;
Tag 08EU.
(blueprint: lem-pc-proper-support-derived-projection-formula)

Proof: Boundedness gives finitely many nonzero cohomology sheaves. Their supports
have proper union T over S, hence T is quasi-compact. Choose a quasi-compact open
j:U -> X containing T. Since S is Noetherian and f is locally of finite type,
X is locally Noetherian and f|U is quasi-compact and quasi-separated. Restriction
is exact; the supported-open comparison and composition of derived direct images
identify Rf*E with R(f|U)*(E|U). Coherence implies quasi-coherence here. For a
quasi-coherent F, apply Tag 08EU on U to obtain the projection isomorphism.
Derived tensor and pullback commute with open restriction. The cohomological
support of E tensor^L Lf*(F[0]) is contained in T: its restriction outside T is
zero because E restricts to zero and tensor preserves zero. Thus the same
supported-open comparison identifies its direct image from U with that from X.
Compose these comparisons with the projection isomorphism on U. The result is
an isomorphism of the two displayed objects for the fixed derived localizations
on X and S; auxiliary localizations on U are transported by their equivalences.
No Tor bound is used in this argument. -/
theorem nonempty_properSupport_derivedProjection_iso
    (S : Scheme.{u}) [IsNoetherian S]
    (X : Scheme.{u}) (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (F : SheafOfModules.{u} (moduleRings S.toRingedSpace)) (hF : F.IsQuasicoherent) :
    Nonempty (((schemeDerivedDirectImage f).obj E) ⊗
        (DerivedCategory.singleFunctor _ 0).obj F ≅
      (schemeDerivedDirectImage f).obj
        (E ⊗ (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by sorry

end AlgebraicGeometry.Scheme
