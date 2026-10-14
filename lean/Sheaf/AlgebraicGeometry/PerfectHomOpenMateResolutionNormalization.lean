/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomOpenModuleMate
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties

/-! # Normalization of the open-square comparison on K-injective representatives

Source: Stacks Project, Cohomology, Tags 08FE, 08BS, 079W and 0D5S.
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Derive the ordinary sectionwise comparison and identify exact open pullback
by uniqueness of left adjoints. All data are specified by functorial derivation
and adjunction uniqueness; the ordinary IsIso theorem determines only the inverse.
Source: Stacks Tags 08FE, 08BS, 079W
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization). -/
def perfectHomOpenDerivedComparison {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S) :
    schemeDerivedDirectImage (pullback.fst s r) ⋙ schemeMVDerivedRestriction Y B ≅
      derivedPullback (perfectHomOpenMap s B r) ⋙
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r) := by
  let : HasDerivedCategory.{w} (pullback s r).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (pullback s r).toRingedSpace)))
  let : HasDerivedCategory.{w} (pullback (B.ι ≫ s) r).Modules := inferInstanceAs
    (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback (B.ι ≫ s) r).toRingedSpace)))
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let : HasDerivedCategory.{w} B.toScheme.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings B.toScheme.toRingedSpace)))
  have : IsGrothendieckAbelian.{u} (pullback s r).Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} (pullback (B.ι ≫ s) r).Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} Y.Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : Abelian.HasKInjectiveResolutions (pullback s r).Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have : Abelian.HasKInjectiveResolutions (pullback (B.ι ≫ s) r).Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have : Abelian.HasKInjectiveResolutions Y.Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  let F := Scheme.Modules.pushforward (pullback.fst s r)
  let G := schemeOpenRestriction Y B
  let H := Scheme.Modules.restrictFunctor (perfectHomOpenMap s B r)
  let K := Scheme.Modules.pushforward (pullback.fst (B.ι ≫ s) r)
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits G := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits H :=
    (openImmersion_restriction_derived_properties (perfectHomOpenMap s B r)).1
  have : H.PreservesKInjectiveComplexes :=
    (openImmersion_restriction_derived_properties (perfectHomOpenMap s B r)).2
  have : F.Additive := inferInstance
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  have : H.Additive := restriction_additive _
  have : K.Additive := inferInstance
  have : (F ⋙ G).Additive := inferInstance
  have : (H ⋙ K).Additive := inferInstance
  have : IsIso (perfectHomOpenModuleMate s B r) := perfectHomOpenModuleMate_isIso s B r
  let aH : H.mapDerivedCategory ⊣ schemeDerivedDirectImage (perfectHomOpenMap s B r) :=
    (Scheme.Modules.restrictAdjunction (perfectHomOpenMap s B r))
      |>.mapDerivedCategoryRightDerivedAdjunction
  let σH : H.mapDerivedCategory ≅ derivedPullback (perfectHomOpenMap s B r) :=
    (conjugateIsoEquiv (canonicalPullbackAdjunction (perfectHomOpenMap s B r)) aH).symm
      (Iso.refl _)
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{w, w, w} F G).symm ≪≫
    Functor.rightDerivedFunctorNatIso.{u, u, u + 1, u + 1, w, w}
      (asIso (perfectHomOpenModuleMate s B r)) ≪≫
    Functor.rightDerivedFunctorCompIso.{u, u, u, u + 1, u + 1, u + 1, w, w, w} H K ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory.{w, w} H) _
      ≪≫ Functor.isoWhiskerRight σH _

/-- Transport the explicitly derived comparison to the supplied adjunctions.
The conjugations are isomorphisms determined by the identity of the left adjoints.
Source: Stacks Tag 079W and Mathlib's adjoint uniqueness
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization). -/
def perfectHomOpenSuppliedComparison {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (ap : derivedPullback (pullback.fst s r) ⊣
      schemeDerivedDirectImage (pullback.fst s r))
    (ap' : derivedPullback (pullback.fst (B.ι ≫ s) r) ⊣
      schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r)) :
    schemeDerivedDirectImage (pullback.fst s r) ⋙ schemeMVDerivedRestriction Y B ≅
      derivedPullback (perfectHomOpenMap s B r) ⋙
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r) :=
  let σ := (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
  let σ₀ := (conjugateIsoEquiv (canonicalPullbackAdjunction B.ι)
    (schemeMVAdjunction Y B)).symm (Iso.refl _)
  Functor.isoWhiskerRight
      ((conjugateIsoEquiv ap (canonicalPullbackAdjunction (pullback.fst s r)))
        (Iso.refl _)) (schemeMVDerivedRestriction Y B) ≪≫
    Functor.isoWhiskerLeft (schemeDerivedDirectImage (pullback.fst s r)) (σ ≪≫ σ₀.symm) ≪≫
    perfectHomOpenDerivedComparison s B r ≪≫
    Functor.isoWhiskerLeft (derivedPullback (perfectHomOpenMap s B r))
      ((conjugateIsoEquiv (canonicalPullbackAdjunction (pullback.fst (B.ι ≫ s) r)) ap')
        (Iso.refl _))

/-- On K-injective representatives the derived sectionwise comparison satisfies
the counit equation for the fixed pullback-composition comparison and canonical adjunctions.
Source: Stacks Project, Cohomology, `lemma-restrict-direct-image-open` (08FE),
`lemma-restrict-K-injective-to-open` (08BS), `lemma-adjoint` (079W), and
`lemma-derived-pullback-composition` (0D5S).
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization).

Proof: First take the projection and open adjunctions pinned to the shared
left-derived counits and ordinary tensor adjunctions. Expand the derived
comparison into its exact-composition comparison, right derivation of the
ordinary open mate, K-injective-composition comparison, and exact-open
pullback identification. The right-derived unit factorization equations
identify these factors on I with the ordinary sectionwise comparison; open
restriction preserves K-injectivity by 08BS. The left-derived counit equation
for perfectHomComposition, evaluated on K-flat representatives, identifies
the inverse pullback square with the ordinary pullback-composition square.
Transpose that equation using the normalized derived Hom equivalences of
079W. On each open W of B both sides are the same map from sections on
pi inverse (B.ι image W), obtained by the ordinary tensor counit and
restriction. The equality of opens follows from the cartesian square.
Thus the maps of complexes coincide and localization gives the displayed
counit equation for the canonical adjunctions. No arbitrary adjunctions,
assertion about an arbitrary derived object, or invertibility of the derived
mate occurs in this obligation. Adjunction transport is proved separately
in the importing module. Empty and full opens and
the zero complex satisfy these same sectionwise equations. -/
theorem perfectHomOpenComparison_counit_resolution
    {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (pullback s r).toRingedSpace)) ℤ)
    [I.IsKInjective] :
    let a := canonicalPullbackAdjunction B.ι
    let ap := canonicalPullbackAdjunction (pullback.fst s r)
    let ap' := canonicalPullbackAdjunction (pullback.fst (B.ι ≫ s) r)
    let b := perfectHomOpenMap s B r
    let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
      (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
    let he : b ≫ pullback.fst s r = pullback.fst (B.ι ≫ s) r ≫ B.ι := by
      simp [b, perfectHomOpenMap, pullback.map]
    let κ := perfectHomComposition b (pullback.fst s r) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) he) ≪≫
      (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
      Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r))
    (derivedPullback (pullback.fst (B.ι ≫ s) r)).map
        ((perfectHomOpenDerivedComparison s B r).hom.app
          (DerivedCategory.Q.obj I)) ≫
        ap'.counit.app ((derivedPullback b).obj (DerivedCategory.Q.obj I)) =
      κ.inv.app ((schemeDerivedDirectImage (pullback.fst s r)).obj
        (DerivedCategory.Q.obj I)) ≫
        (derivedPullback b).map (ap.counit.app (DerivedCategory.Q.obj I)) := by sorry

end
end AlgebraicGeometry
