/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.FiniteProjectionFixedCoordinates
import Sheaf.Paper.FiniteProperProjectionFixedRealizationExpanded

/-! # Proper projection in fixed coefficients

Source: the proper-factor calculation of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The fixed-coordinate proper projection calculation after exposing the full
constructible inclusion. This is the coefficient-level calculation used by the
public realization statement.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph.
(blueprint: lem-sf-finite-proper-projection-fixed-realization-core).
Proof: expand the proper component and the two coordinate comparisons. Apply
finiteProperNormalization at the source and target, then use naturality of the
coefficient realization units and the defining counit transpose of the fixed
rightDerivedLowerStar projection. The equivalence triangle identities cancel the
remaining units. -/
theorem properComponent_fixed_realization_core (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    (coordinates (C := C) (E := E) (n := n) (hn := hn) Y).map
        (((partialTensor S Y).map ((S.finite.properIdentity f).inv.app K)).app L ≫
          component S f (.ofIsProper f.hom.left) K L ≫
          (S.finite.properIdentity f).hom.app
            (((partialTensor S X).obj K).obj ((torPull S f).obj L))) ≫
      (directCoordinates S f (((partialTensor S X).obj K).obj ((torPull S f).obj L))).hom ≫
      (fixedDirect (C := C) (E := E) (n := n) f).map (targetCoordinates S f K L).hom =
    (directTensorCoordinates S f K L).hom ≫
      ((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left).app
            ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K)).app
              ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj) := by
  simpa only [properComponent, Functor.comp_obj, Functor.comp_map, Category.assoc]
    using properComponent_fixed_realization_expanded S f K L

/-- The proper specialization realizes the fixed direct-image projection itself.
No supplied constructible adjunction or transpose occurs in this equation.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph; the proper identity
normalization in def-sf-operation-stages.
(blueprint: lem-sf-finite-proper-projection-fixed-realization).

Proof: expand properComponent into the inverse proper identification, the component
at the identity-open compactification, and the proper identification at its target.
Apply the full inclusion and the inverse coefficient equivalence. Substitute
finiteProperNormalization at both inputs. The operation support comparisons then
cancel, leaving the published fixed-scalar compactification projection conjugated by
the coefficient-unit cancellations. For the identity-open compactification the open
projection is the inverse tensor comparison of the identity functor, with its unit;
its composite with pullback composition cancels that identity factor. The remaining
arrow is the fixed direct-image projection. Naturality moves the fixed direct-image
comparison past the coefficient counit, and the equivalence triangle identities
cancel the source and target inner units. This gives the displayed equation. The
argument uses only proper normalization and naturality, not projection invertibility
or finite Tor amplitude of the first input; it includes empty schemes and zero inputs. -/
theorem properComponent_fixed_realization (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    (coordinates (C := C) (E := E) (n := n) (hn := hn) Y).map
        (properComponent S f K L) ≫
      (directCoordinates S f (((partialTensor S X).obj K).obj ((torPull S f).obj L))).hom ≫
      (fixedDirect (C := C) (E := E) (n := n) f).map (targetCoordinates S f K L).hom =
    (directTensorCoordinates S f K L).hom ≫
      ((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left).app
            ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K)).app
              ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj) := by
  simpa only [properComponent, coordinates, Functor.comp_obj, Functor.comp_map, Category.assoc]
    using properComponent_fixed_realization_core S f K L

end WeilConjectures.CompactSupportFiniteProjection
