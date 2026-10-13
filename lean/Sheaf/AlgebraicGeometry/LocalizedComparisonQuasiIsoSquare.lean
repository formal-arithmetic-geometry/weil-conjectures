/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # The localized comparison square for a quasi-isomorphism

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-localized-comparison-quasiiso-square).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- A quasi-isomorphism induces an isomorphism on the source of the localized
comparison, and the counit comparison square commutes.

Proof: stalks and restriction of scalars are exact, so the stalk of s gives an
isomorphism in D(R). The unique isomorphism between the two universal left-derived
scalar-extension functors identifies their values on this isomorphism. Taking
cohomology and conjugating by each model's cohomologyIso gives a B-linear
isomorphism. Naturality for multiplication by a in A, expressed by
cohomologyIso_smul, makes this isomorphism A-tensor-R-B-linear. Extend this
isomorphism to C to obtain e. Naturality of the universal counits gives the square
for comparison by comparison_eq. The pure-tensor specification of
ordinaryToLocalized and localized_eq give the square for localizedComparison
by the extension/restriction adjunction. Finally the specified components of
tensorStalkIso commute with s, by naturality of the pullback-stalk isomorphism.
Taking homology and composing these squares gives the displayed identity.
Neither ordinary pullback of s nor its homology is asserted to be invertible.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8;
More on Algebra, Tags 06Y6 and 08IB.
(blueprint: lem-pc-localized-comparison-quasiiso-square). -/
theorem exists_localizedComparison_quasiIso_square
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (s : P ⟶ G) (hs : QuasiIso s) (z : X') (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    ∃ e : (Arrow.mk ((cohomologyModel f f' g g' sq z P).localizedComparison i)).left ≅
        (Arrow.mk ((cohomologyModel f f' g g' sq z G).localizedComparison i)).left,
      (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
          HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
          HomologicalComplex.homologyMap
            (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
              (.up ℤ)).map
                (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).map s)) i =
        e.hom ≫ (cohomologyModel f f' g g' sq z G).localizedComparison i ≫
          HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z G).hom i := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
