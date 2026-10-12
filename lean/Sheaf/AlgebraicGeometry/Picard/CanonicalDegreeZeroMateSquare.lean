/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Degree-zero compatibility square for the canonical mate

Source: Stacks Project, Cohomology, Remark 08HY.
(blueprint: lem-pc-canonical-degree-zero-mate-square).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The standard degree-zero direct-image identification, computed by the existing
comparison of unbounded and bounded below derived functors.
Source: Stacks, Tags 079V and 0A1G
(blueprint: lem-pc-canonical-degree-zero-mate-square). -/
def canonicalDirectImageH0Iso {X S : Scheme.{u}} (f : X ⟶ S)
    [HasInjectiveResolutions X.Modules] (M : X.Modules) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) ≅
      (pushforward f).obj M :=
  (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).homologyRightDerivedFunctorObjSingleFunctorIso
      M 0 ≪≫
    (pushforward f).rightDerivedZeroIsoSelf.app M

/-- The comparison square commutes for every module and every commutative square.
It asserts no invertibility of the single-complex comparisons or of base change.
Source: Stacks, Cohomology, Remark 08HY; canonical mates and derived adjunctions.
(blueprint: lem-pc-canonical-degree-zero-mate-square).

Proof: Apply the pinned derived Hom equivalence to the underived counit, embedded
as a single-complex morphism. Its defining factorization through the left-derived
counit and right-derived unit is exists_schemeDerivedAdjunction. The derived
composition comparisons are the lifts of the corresponding underived comparisons
through those same left-derived counits. Naturality of these counits and the
right-derived unit therefore identifies the two transposes around the square.
Transport tensor pullback to ordinary pullback by leftAdjointUniq; its counit law
identifies the tensor transpose with the displayed ordinary mate. Take H^0.
The single-complex homology identification is natural. For direct image, the
unbounded-to-bounded-below comparison is characterized by its right-derived unit;
the injective-resolution H^0 comparison followed by rightDerivedZeroIsoSelf takes
that unit to the identity. Thus these identifications give exactly the displayed
square. No quasi-isomorphism of a pullback comparison is used. The proof applies
also to zero modules and empty schemes. -/
theorem canonicalDegreeZeroMateSquare
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g)
    [HasInjectiveResolutions X'.Modules] (M : X.Modules) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr h).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    let k := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).app
        ((pullback g).obj ((pushforward f).obj M))
    H.map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫ k.hom ≫
        (pullbackPushforwardAdjunction f').homEquiv _ _
          (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)) =
      H.map ((derivedPullback g).map (canonicalSingleDirectImageMap f M)) ≫
        H.map (schemeDerivedBaseChangeMap f f' g g' h E) ≫
        H.map ((schemeDerivedDirectImage f').map (canonicalSinglePullbackMap g' M)) ≫
        (canonicalDirectImageH0Iso f' ((pullback g').obj M)).hom := by sorry

end AlgebraicGeometry.Scheme.Modules
