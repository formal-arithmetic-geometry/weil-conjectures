/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionOpenMap

/-! # The open cohomology map of a fixed resolution lift

Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- The homology mate of q acts on resolution classes through its open cohomology map.
Source: Stacks Project, Cohomology, Tags 02N7 and 01E4.
(blueprint: lem-weil-pbc-flat-pullback-homology-sections).

Proof: Represent the source section-complex homology class by a cycle s. The unit
followed by pushforward of the termwise adjoint c of q equals q, so it sends s to
q(s). Exactness of tensor pullback identifies the homology comparison in beta with
this cycle-class calculation. The sheafification unit theta is natural for this
calculation, giving equality of the associated cohomology-sheaf sections. In the
open map the inverse target resolution/section isomorphism converts H(q)(s) into
a target cohomology class. Applying targetClass cancels that inverse and applies
theta, followed by the inverse target derived-image comparison. The inverse source
derived-image comparison in sourceClass likewise cancels the source comparison
in beta by adjunction naturality. These cancellations give the displayed formula.
This argument does not use the augmentation of t or a comparison with an h-map. -/
theorem flatBaseChangeResolutionBeta_openMap_sections {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (p : ℕ) :
    ∀ (V : S.Opens)
        (D : FlatBaseChangeOpenChoices f g F I J V)
        (xi : (forget₂ _ AddCommGrpCat.{uBC}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
        Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
          (flatBaseChangeResolutionBeta f g I J t p)) V
          (D.sourceClass p xi) =
        D.targetClass p
          (flatBaseChangeResolutionOpenMap f g I J t p V D xi) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
