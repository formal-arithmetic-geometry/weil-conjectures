/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism

/-! # Image of an ideal power after closed pushforward

Source: Stacks Project, proof of Lemma 088A, lines 6961--6968.
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Compare just the image subobjects, before constructing any quotient comparison.
Source: Stacks Project, proof of Lemma 088A, lines 6961--6968; Morphisms, Lemma 01QO;
Schemes, Lemmas 01I8 and 01IC.
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image).

Proof: For an affine open U = Spec R, its inverse image is affine, Spec S, and the
structure map pi : R → S is surjective. The extended ideal has sections Ideal.map pi
(I(U)). Products and positive powers are quasi-coherent and are computed on affine
sections. Thus the upstairs product has sections (Ideal.map pi (I(U)))^n times G(U'),
and the downstairs product has sections I(U)^n times the same group, with scalars
restricted through pi. Mapping ideals commutes with powers. Surjectivity of pi makes
the mapped ideal the actual image; its action is precisely the restricted R-action.
The two ranges therefore coincide on every affine open of X. Both image inclusions
are subsheaves of the pushforward of G. For an arbitrary open, restrict a section of
either subsheaf to an affine cover. The equal ranges give local lifts into the other
subsheaf; injectivity of its inclusion makes these lifts agree on overlaps, and the
sheaf condition glues them. This proves both inclusions and hence subobject equality.
The empty affine open and the zero ideal or module give zero products on both sides;
no nonemptiness, finite generation or Noetherian hypothesis is used. -/
theorem closedImmersion_idealPower_image
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (G : Z.Modules) [G.IsQuasicoherent]
    (n : ℕ) (hn : 1 ≤ n) :
    Subobject.mk (image.ι ((Modules.pushforward i).map (idealModuleProductι
      (idealSheafPower (I.comap i).toModulesι n).2 G))) =
      Subobject.mk (image.ι (idealModuleProductι
        (idealSheafPower I.toModulesι n).2 ((Modules.pushforward i).obj G))) := by
  sorry

end AlgebraicGeometry.Scheme
