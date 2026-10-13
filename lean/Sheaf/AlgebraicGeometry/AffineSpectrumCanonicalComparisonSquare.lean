/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology
public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The affine spectrum counit square on the canonical representative

Source: Stacks Project, Tag 0DJ8, affine reduction; Tags 0098 and 0D5S.
(blueprint: lem-pc-affine-spectrum-canonical-comparison-square).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- The comparison square for the termwise spectrum pullback with its canonical counit.

Proof: isoSpec naturality and stalkMap_comp identify the four stalk rings and
intertwine their structural maps, including the stalkCongr in rightAlgebra.
The tensor universal property intertwines tensorMap: check on the A and B inclusions.
The tensor-pullback stalk formula identifies the stalk complex of Q with extension
of the stalk complex of P along the resulting ring isomorphism. Restriction along
its inverse gives an inverse exact equivalence. Transport the universal R-to-B
left-derived extension through these equivalences; uniqueness of the left-derived
lift gives the counit-compatible identification. Taking degree-i homology and
using cohomologyIso_smul lifts its B-linear source comparison to an isomorphism
of the full tensor-algebra modules. Extend to C and forget scalars to obtain l.
The model equations comparison_eq and localized_eq identify the comparisons
with the derived counits. The germ formula for tensorStalkIso and the
restriction-stalk construction of isoPullbackStalkCohomologyIso identify the
ordinary pullback factors. The defining leftDerivedLift equation for the
composition comparison gives affineSpectrumDerivedPullbackIso.inv, with the
specified canonical counit d. Combining these counit equations gives the square.
There are no changes of derived representatives in this statement. In particular,
no invertibility of either localized comparison is used; empty schemes, zero
rings, zero complexes, unbounded complexes, and arbitrary i use the same argument.
Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098,
lemma-stalk-pullback-modules; Tag 0D5S, lemma-pullback-composition.
(blueprint: lem-pc-affine-spectrum-canonical-comparison-square). -/
theorem exists_affineSpectrum_canonicalComparison_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (Q : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace)) ℤ)
    (hP : P.IsKFlat) (hQ : Q.IsKFlat)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit (Spec.map g'.appTop)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (hQ0 : Q = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P) :
    let z := X'.isoSpec.inv z0
    let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    let d : DerivedCategory.Q.obj Q ≅
        affineSpectrumDerivedObject X (DerivedCategory.Q.obj P) :=
      eqToIso (congrArg (fun W ↦ DerivedCategory.Q.obj W) hQ0) ≪≫
        (isoPullbackComplexCounitIso X.isoSpec.inv).symm.app P
      ∃ l : F.obj (Arrow.mk (comparisonIntoPullback f f' g g' sq z P hcP i)).left ≅
          F0.obj (Arrow.mk
            (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i)).left,
        l.hom ≫ F0.map
          (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i ≫
              H0.map ((derivedPullback (Spec.map g'.appTop)).map d.hom)) =
        F.map (comparisonIntoPullback f f' g g' sq z P hcP i) ≫
            (isoPullbackStalkCohomologyIso X'.isoSpec.inv z0 i).hom.app
              ((derivedPullback g').obj (DerivedCategory.Q.obj P)) ≫
              F0.map (H0.map ((affineSpectrumDerivedPullbackIso g').inv.app
                (DerivedCategory.Q.obj P))) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
