/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.RegularPermanence

/-! # Smoothness near the image of regular precomposition

Source: Temkin, Non-embedded Desingularization, Lemma 2.1.4(ii), printed p.8,
and its application in Proposition 3.3.5, printed p.25; Stacks Project, Tags
07NT, 07C0 and 01V9 (blueprint: lem-per-regular-precomposition-smooth-image).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally finitely presented morphism is smooth on an open containing the image of a
regular morphism when the composite is regular. No surjectivity or finite presentation
hypothesis is imposed on the precomposing morphism.

Source: Temkin, Lemma 2.1.4(ii), printed p.8, and Proposition 3.3.5, printed p.25;
Stacks Project, Tags 07NT, 07C0 and 01V9
(blueprint: lem-per-regular-precomposition-smooth-image).

Proof:
1. For z in Z, put t = p(z) and s = g(t). The local ring maps A = O_{S,s} to
   B = O_{T,t} to C = O_{Z,z} compose to the stalk map of p ≫ g, by the composition
   rule in def-weil-locally-ringed-space-morphism. The regular scheme/stalk criterion
   lem-per-regular-scheme-stalk-criterion applied to p and p ≫ g makes B to C and
   A to C regular ring maps (def-weil-pbc-g-ring). In particular B to C is flat.
2. The flat local map B to C is faithfully flat and surjective on spectra by
   lem-weil-pbc-flat-local-hom-faithfully-flat. Regular permanence
   lem-weil-pbc-regular-permanence then makes A to B regular. This is applied at
   each chosen z and does not require p to be surjective.
3. Apply lem-per-lfp-regular-stalk-smooth-neighborhood to g at t, using its local
   finite presentation, the locally Noetherian source and target, and the regular
   stalk map A to B. This gives a smooth open neighborhood of every point p(z).
4. Take W to be the union of the opens on which g is smooth. Step 3 makes it
   contain the image of p. The affine-local characterization of smoothness in
   def-sbc-smooth-morphisms makes g smooth on W. For empty Z the containment is
   vacuous, and this construction still applies. -/
theorem exists_open_smooth_of_regular_precomposition
    {Z T S : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian T]
    [IsLocallyNoetherian S] (p : Z ⟶ T) (g : T ⟶ S)
    (hp : IsRegularSchemeMorphism p) [LocallyOfFinitePresentation g]
    (hcomp : IsRegularSchemeMorphism (p ≫ g)) :
    ∃ W : T.Opens, (∀ z : Z, p z ∈ W) ∧ Smooth (W.ι ≫ g) := by
  sorry

end AlgebraicGeometry
