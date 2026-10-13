/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare

/-! # Degree-zero mates with the specified tensor pullback

Source: Stacks Project, Cohomology, Remark 08HY; flat-module comparison, Tag 06YJ.
(blueprint: lem-sc-picard-tensor-degree-zero-mate-square).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor-form degree-zero mate compatibility with the canonical single-image unit.
The derived module comparison is not assumed invertible. Only its source module's
ordinary direct image needs to be finite locally free.
Source: Stacks Project, Remark 08HY, canonical adjunction construction; Tag 06YJ.
(blueprint: lem-sc-picard-tensor-degree-zero-mate-square).

Proof:
1. Use the left-derived counit for tensor pullback chosen by
   exists_derivedPullbackComposition. At G[0] followed by the single-map comparison,
   it defines c:Lv*G[0] to (v*G)[0]. Compose the canonical derived base-change map
   with Rp'*(c) to get phi. This is IsDerivedModuleBaseChangeMap by definition.
2. The direct image M is finite locally free and hence flat. Its single complex is
   K-flat. The same left-derived counit at M[0] is therefore invertible. The inverse
   single-homology identification followed by the inverse H0 counit gives
   e0:k*M to H0(Lk*M[0]).
3. Apply derivedBaseChange_unit_compatibility to the single complex G[0].
   Naturality of the pinned tensor-pullback counit and the right-derived
   direct-image unit reduces its square to the ordinary termwise exchange map.
   The singleMapHomologicalComplex comparisons identify this exchange map with
   singleFunctor.map(moduleBaseChangeMap): check its degree-zero component and
   use functor identity laws. The quotient functor descends this equality to
   the homotopy category. Thus cg followed by single(beta) and the canonical
   single direct-image unit equals Lg(a) followed by phi.
4. Apply H0. canonicalDirectImageH0Unit identifies H0 of the direct-image unit
   followed by the canonical H0 isomorphism with the single-homology identification.
   Naturality of the single-homology isomorphism identifies the ordinary map.
   Cancel the invertible H0 source comparison to obtain the formula. Neither phi
   nor beta is cancelled. The zero module and rank zero require no change. -/
theorem tensorDegreeZeroMateSquare
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [(tensorPullback (pullback.fst f g)).Additive]
    [HasInjectiveResolutions (Limits.pullback f g).Modules]
    (G : X.Modules) [((pushforward f).obj G).IsFiniteLocallyFree] :
    let M := (pushforward f).obj G
    let K := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0
    ∃ (e0 : (tensorPullback g).obj M ≅
        H.obj ((derivedPullback g).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M)))
      (φ : (derivedPullback g).obj K ⟶
        (schemeDerivedDirectImage (pullback.snd f g)).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (Limits.pullback f g).toRingedSpace)) 0).obj
            ((tensorPullback (pullback.fst f g)).obj G))),
      IsDerivedModuleBaseChangeMap f g G φ ∧
      moduleBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition G =
        e0.hom ≫ H.map ((derivedPullback g).map (canonicalSingleDirectImageMap f G)) ≫
          H.map φ ≫ (canonicalDirectImageH0Iso (pullback.snd f g)
            ((tensorPullback (pullback.fst f g)).obj G)).hom := by sorry

end AlgebraicGeometry.Scheme.Modules
