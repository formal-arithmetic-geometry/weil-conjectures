/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Affine spectrum transport before the coefficient morphism

Source: Stacks Project, Tags 0DJ8, 0098 and 0D5S.
(blueprint: lem-pc-affine-spectrum-comparison-source-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- Transport the localized tensor comparison into derived pullback, independently
of any coefficient morphism or target representative.

Proof: put j = X.isoSpec.inv and j' = X'.isoSpec.inv. Their stalk maps are ring
isomorphisms. For each sheaf, the tensor-pullback stalk formula sends a pulled-back
section to 1 tensor its germ. Extension along an isomorphism of rings has an inverse
by restriction along that isomorphism; after forgetting scalars its unit is an
isomorphism. Apply this to j'. Since pullback along an isomorphism is exact, its
universal left-derived counit is invertible on every complex. The natural
pullback-stalk identification therefore descends to derived categories. Exact
stalks and homology, followed by forgetting scalars, give the natural isomorphism
T of functors in the statement, for all objects and morphisms, not just K-flat ones.

For the source identification, naturality of isoSpec and stalkMap_comp identify
R, A, B and C with their spectrum counterparts and intertwine the four ring maps,
including the stalkCongr in rightAlgebra. The restriction equations of tensorMap
and tensor universality identify the tensor-to-C maps. The stalk formula for j
and the equality hQ identify the input complexes after scalar transport. Use the
counit-compatible isomorphism between universal left-derived R-to-B extensions.
The isomorphisms e and e0 identify their derived inputs, correcting any difference
between the selected representative isomorphisms. Applying cohomology yields the
B-linear source isomorphism; naturality for multiplication by elements of A and
the model cohomologyIso_smul equation give the full tensor-algebra action. Extend
to C and forget scalars to obtain l and its inverse.

The model equations comparison_eq and localized_eq identify the localized maps
with the universal scalar-extension counits. The degreewise germ equation for
tensorStalkIso and naturality identify the ordinary pullback maps. On the derived
categories, uniqueness of leftDerivedLift identifies their composite with the
specified affineSpectrumDerivedPullbackIso, rather than an arbitrary composition
isomorphism. The resulting counit square, followed by e and e0, is exactly the
equation below. No localized comparison is required to be invertible. Empty
schemes contribute no points; zero complexes, zero rings, arbitrary degrees and
unbounded complexes are all covered by the same functorial construction.
Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction;
Tag 0098, lemma-stalk-pullback; Tag 0D5S, lemma-pullback-composition.
(blueprint: lem-pc-affine-spectrum-comparison-source-transport). -/
theorem exists_affineSpectrum_comparisonIntoPullback_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ) :
    let z := X'.isoSpec.inv z0
    let H := comparisonStalkCohomology X' z i
    let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    ∃ T : H ⋙ F ≅ derivedPullback X'.isoSpec.inv ⋙ H0 ⋙ F0,
      ∀ (K : schemeDerivedCategory X)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (Q : CochainComplex
          (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace)) ℤ)
        (hP : P.IsKFlat) (hQ : Q.IsKFlat)
        (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
        (hcQ : IsIso ((counit (Spec.map g'.appTop)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
        (e : DerivedCategory.Q.obj P ≅ K)
        (e0 : DerivedCategory.Q.obj Q ≅ affineSpectrumDerivedObject X K)
        (hQ0 : Q = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
          (.up ℤ)).obj P),
      ∃ l : F.obj (Arrow.mk (comparisonIntoPullback f f' g g' sq z P hcP i)).left ≅
          F0.obj (Arrow.mk
            (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i)).left,
        l.hom ≫ F0.map
          (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i ≫
              H0.map ((derivedPullback (Spec.map g'.appTop)).map e0.hom)) =
        F.map (comparisonIntoPullback f f' g g' sq z P hcP i ≫
          H.map ((derivedPullback g').map e.hom)) ≫
            T.hom.app ((derivedPullback g').obj K) ≫
              F0.map (H0.map ((affineSpectrumDerivedPullbackIso g').inv.app K)) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
