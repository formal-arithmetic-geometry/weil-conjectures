/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData
public import Sheaf.Paper.RefinementOpenRestriction

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/--
The proper/open word for an identity compactification is the identity when its open
comparison has the prescribed adjunction transpose.  This is the ambient categorical
calculation used by the integral refinement identity component.

Source: the identity diagram in the integral normalized refinement pasting argument
(blueprint: lem-sf-integral-normalized-ring-refinement-identity-component).
Proof: expand the transpose through the open adjunction, use its triangle identity,
and use the left-unit law for the proper direct-image compositor.  The resulting
composite is the identity on the compact-support image object.
-/
theorem integral_normalized_ring_refinement_identity_core
    (R : PurCompactSupport.Coefficients.{max u v})
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    {c : Compactification f}
    (hi : R.pull (c.i ≫ (Compactification.Refinement.id c).hom) =
      proEtaleRingCompositeCoefficients c.i (Compactification.Refinement.id c).hom
        (R.ring c.Z) (R.ring c.Z) (R.ring X)
        (R.pull (Compactification.Refinement.id c).hom) (R.pull c.i))
    (hg : R.pull ((Compactification.Refinement.id c).hom ≫ c.g) =
      proEtaleRingCompositeCoefficients (Compactification.Refinement.id c).hom c.g
        (R.ring Y) (R.ring c.Z) (R.ring c.Z)
        (R.pull c.g) (R.pull (Compactification.Refinement.id c).hom))
    (K : DerivedCategory (pbcModules X (R.ring X)))
    (ε : (PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K ≅
      (PurCompactSupport.push R (Compactification.Refinement.id c).hom).obj
        ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K))
    (hε : (PurCompactSupport.openDerivedAdjunction R c.i).homEquiv _ _ ε.hom ≫
      PurCompactSupport.refinementRestriction R (Compactification.Refinement.id c) hi K =
        (PurCompactSupport.openDerivedAdjunction R c.i).unit.app K) :
    ((PurCompactSupport.geometricPushComposition R
        (Compactification.Refinement.id c).hom c.g hg ≪≫
      eqToIso (congrArg (fun h ↦ PurCompactSupport.push R h)
        (Compactification.Refinement.id c).hom_g)).symm.app
        ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K)).hom ≫
      (PurCompactSupport.push R c.g).map ε.inv = 𝟙 _ := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
