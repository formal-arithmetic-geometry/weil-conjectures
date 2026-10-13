/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import Sheaf.AlgebraicGeometry.OpenRestrictedComparisonComposition

/-! # Comparison square on literal restrictions

Source: Stacks Project, Tags 0DJ8 and 0DJ9 (locality of the stalk comparison).
(blueprint: lem-pc-open-restricted-comparison-core).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
/-- The open comparison square when the restricted representative data are supplied.
Source: Stacks Project, Tag 0DJ8 (locality of equation-bc), Tag 0DJ9
(source-open induction), and Tag 06YB (K-flat stalks).
(blueprint: lem-pc-open-restricted-comparison-core).

Proof: put p = pullback.fst g′ U.ι and q = pullback.snd g′ U.ι. The open
immersion p has exact module restriction. Uniqueness of left adjoints identifies
its tensor pullback with restriction, and uniqueness of left derived functors
identifies their derived functors. Descend restrictStalkNatIso to the exact
derived functors and then cohomology, obtaining η independently of P and K.
Open restriction preserves K-flatness of P by the stalk criterion.
The stalk ring maps of p and U.ι are isomorphisms. The pullback condition,
stalkMap_comp, and restriction-stalk extension identify the original and
restricted stalk complexes with their base-ring actions. Apply the universal
derived base tensor functor, cohomology, and final scalar extension to obtain
the source isomorphism. The comparison_eq and localized_eq model equations
identify both comparisons with universal counits and adjunction transposes.
Naturality of these maps and tensorStalkIso proves the square for the canonical
exact-restriction identification. The derived-composition counit equation gives
precisely β. For the supplied eQ, compare it with the canonical identification
through a derived automorphism of the literal restricted representative. Apply
comparisonIntoPullback_naturality and exists_comparisonSourceIso to that
automorphism; compose its source isomorphism with the preceding one. Naturality
of η transports the square along eP. This gives the displayed formula for every
supplied eQ and hcQ. Invertibility of comparisonIntoPullback is never assumed.
Empty opens have no z, and the same operations apply to zero complexes and rings. -/
theorem exists_open_restricted_comparison_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z : (pullback g' U.ι : Scheme.{u})) (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
      AddCommGrpCat.{u}
    let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
      AddCommGrpCat.{u}
    let H := comparisonStalkCohomology X' (pullback.fst g' U.ι z) i ⋙ F
    let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
    ∃ η : H ≅ derivedPullback (pullback.fst g' U.ι) ⋙ HU,
      ∀ (K : schemeDerivedCategory X)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsKFlat)
        (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
        (eP : DerivedCategory.Q.obj P ≅ K),
      let Q : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
        ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
      ∀ (hcQ : IsIso ((counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
        (eQ : DerivedCategory.Q.obj Q ≅ (derivedPullback U.ι).obj K),
      let a := F.map (comparisonIntoPullback f f' g g' sq
        (pullback.fst g' U.ι z) P hcP i)
      let b := FU.map (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sqU z Q hcQ i)
      let β := openRestrictedCompositionMap g' U K
      ∃ l : (Arrow.mk a).left ≅ (Arrow.mk b).left,
        a ≫ H.map ((derivedPullback g').map eP.hom) ≫
            η.hom.app ((derivedPullback g').obj K) =
          l.hom ≫ b ≫ HU.map ((derivedPullback (pullback.snd g' U.ι)).map eQ.hom ≫ β) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
