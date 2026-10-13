/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso

/-! # Restriction of target section classes

Source: Stacks Project, Tags 01E4 and 01FB.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- The top-open germ of the class computed with a fixed global resolution equals
the germ of its target section class after restriction to the inverse-image open.
Source: Stacks Project, Lemma 20.7.3 (Tag 01E4) and Remark 20.14.2 (Tag 01FB).
(blueprint: lem-weil-pbc-target-section-class-restriction)

Proof: Put G = (tensorPullback (pullback.snd g f)).obj F and
W = (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V). Restrict the resolution K to W and
compose with D.target.comparison.inv. In degree zero, D.target.augmentation,
the inverse comparison equation, and naturality of the restriction-adjunction
unit show that this is an augmented lift of G to the pushforward of
D.target.resolution. Resolve this pushed complex into a termwise injective
complex by a quasi-isomorphism lambda. Use lambda times this lift as beta in
ModuleCohomologyFMapData, with source K and target D.target.resolution.
Its global-sections comparison induces an isomorphism by Tag 01EZ; the inverse
cancels the lambda factor on homology. Independence of ModuleCohomologyFMapData
identifies this calculation with moduleCohomologyRestriction W G p.
D.target.components now identifies the remaining complex map with restriction
from top to W. The equality flatBaseChangeOpenEquality transports W to
(pullback.fst g f) ⁻¹ᵁ (g ⁻¹ᵁ V). Naturality of the evaluation homology
comparison and of the presheaf map sectionCohomologyTheta identifies the resulting
section class with restriction of the top section class. Finally naturality of
the module morphism (K.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv
commutes this restriction with its section maps. This proves the displayed
morphism equality, with K fixed. Compose with the germ at y. Presheaf.germ_res cancels
the restriction from top to V. Top opens,
p = 0 and zero modules obey the same argument; no section-class isomorphism is
assumed. If V is empty the hypothesis y ∈ V is impossible. -/
theorem FlatBaseChangeOpenChoices.targetClass_restriction {X S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {F : X.Modules} {I : InjectiveResolution F}
    {K : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)}
    {V : S.Opens} (D : FlatBaseChangeOpenChoices f g F I K V) (p : ℕ)
    (y : S) (hy : y ∈ V)
    (eta : (RingedSpace.moduleCohomology (Limits.pullback g f).toRingedSpace p).obj
      ((tensorPullback (pullback.snd g f)).obj F)) :
    TopCat.Presheaf.germ
      ((pushforward g).obj
        (((pushforward (pullback.fst g f)).rightDerived p).obj
          ((tensorPullback (pullback.snd g f)).obj F))).presheaf ⊤ y (by trivial)
      (Hom.app (K.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv ⊤
        (resolutionSectionClass K
          (((pushforward (pullback.fst g f)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K.cocomplex) ⊤ (Iso.refl _) p eta)) =
    TopCat.Presheaf.germ
      ((pushforward g).obj
        (((pushforward (pullback.fst g f)).rightDerived p).obj
          ((tensorPullback (pullback.snd g f)).obj F))).presheaf V y hy
      (D.targetClass p
        (moduleCohomologyFMap ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
          ((restrictAdjunction ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
            ((tensorPullback (pullback.snd g f)).obj F)) p eta)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
