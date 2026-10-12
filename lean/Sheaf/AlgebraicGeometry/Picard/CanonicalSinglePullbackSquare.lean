/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison

/-! # Pullback composition compatibility on single modules

Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-canonical-single-pullback-square).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Single pullback comparisons respect a commutative square and a module morphism.
This concerns only pullback; it involves neither base change nor direct image.
Source: Stacks Project, Tag 0D5S, and the naturality of left-derived counits.
(blueprint: lem-pc-canonical-single-pullback-square).

Proof: Evaluate the defining `leftDerivedLift` factorization for the selected
composition isomorphisms on N[0]. It identifies successive left-derived counits
with the counit for the composite followed by underived tensor composition.
Apply this identity to (f', g) and (g', f), transport along h, and cancel the
invertible derived composition comparison to obtain the square for N.
Transport tensor pullback to ordinary pullback by the unique left-adjoint
isomorphisms. Their counit laws identify tensor composition, defined as the mate
of pushforward composition, with `pullbackComp`; transport along h becomes
`pullbackCongr h`. Thus the ordinary square comparison is c.inv. Finally,
naturality of the left-derived counit and of the single-map comparisons for the
morphism a moves a across the g' comparison, yielding the displayed formula.
No comparison on a single module is inverted. The argument covers h reflexive,
identity morphisms, zero a, zero modules and empty schemes without extra assumptions. -/
theorem canonicalSinglePullbackSquare
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g) (N : S.Modules) (M : X.Modules)
    (a : (pullback f).obj N ⟶ M) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj N
    let c := (pullbackComp g' f).app N ≪≫ (pullbackCongr h).app N ≪≫
      ((pullbackComp f' g).app N).symm
    let d := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) f' g).hom.app E ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj E) h.symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) g' f).inv.app E
    d ≫ (derivedPullback g').map
        (canonicalSinglePullbackMap f N ≫ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) ≫
        canonicalSinglePullbackMap g' M =
      (derivedPullback f').map (canonicalSinglePullbackMap g N) ≫
        canonicalSinglePullbackMap f' ((pullback g).obj N) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map
            (c.inv ≫ (pullback g').map a) := by sorry

end AlgebraicGeometry.Scheme.Modules
