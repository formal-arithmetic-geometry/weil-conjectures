/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeSectionComplex
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso

/-! # The restricted lift on section homology

Source: Stacks Project, Cohomology of Sheaves, Tags 01E4, 01FB and 01EZ
(blueprint: lem-weil-pbc-flat-base-change-restricted-lift-homology).
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- The restricted augmented lift computes the cohomology h-map before passing
from section homology to sections of the cohomology sheaf.
Source: Stacks Project, Cohomology, Tags 01FB and 01EZ
(blueprint: lem-weil-pbc-flat-base-change-restricted-lift-homology).

Proof: Put U = f inverse image of V and W = g' inverse image of U. Restrict t to
U, transport its source with D.source.comparison, and use the restriction/direct
image comparison and D.target.comparison to obtain a map r from the source
restricted resolution to h_* of the target restricted resolution, where h is
g' restricted to W. The two augmentation identities in D, ht, and D.unit_square
show that the augmentation of r is D.psi followed by h_* of the target
augmentation. Resolve h_* of the target restricted resolution by a quasi-isomorphism
lambda into a bounded-below complex of injectives (Tag 013K, extending by zero
and truncating back to natural indices). Use beta = r followed by lambda in
ModuleCohomologyFMapData. The degreewise section identifications are the canonical
ones by D.source.components and D.target.components, the direct-image section
formula, and the fibre-product open equality. Global sections of lambda induce
invertible homology maps by Tag 01EZ. Cancel H(lambda) against its inverse in the
choice-data map; functoriality of homology leaves H(r). Independence of the choice
data identifies this with moduleCohomologyFMap h D.psi. Transport through the
resolution isomorphisms and the stated section identifications to obtain the
displayed equality. No sheafification or adjunction on homology is needed here.
The same cancellation works for p = 0, zero modules, and empty opens. -/
theorem flatBaseChangeRestrictedLift_homology {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J.ι.f 0))
    (V : S.Opens) (D : FlatBaseChangeOpenChoices f g F I J V) (p : ℕ) :
    resolutionSectionHomology D.source.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V D.source.sections p ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        (pushforwardComplexSections g (flatBaseChangeResolutionQ f g I J t) V) =
    moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p ≫
    resolutionSectionHomology D.target.resolution
      (((pushforward (pullback.fst g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) (g ⁻¹ᵁ V)
      (D.target.sections ≪≫ eqToIso (congrArg (fun U ↦
        ((RingedSpace.openModuleSections
          (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
           (ComplexShape.up ℕ)).obj J.cocomplex)
            (flatBaseChangeOpenEquality f g V))) p := by
  sorry

end AlgebraicGeometry.Scheme.Modules
