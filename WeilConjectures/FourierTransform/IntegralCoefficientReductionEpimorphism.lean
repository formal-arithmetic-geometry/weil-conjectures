/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
public import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRingSupplement
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Epimorphic integral coefficient reductions

Source: `literature/blueprint/latest/blueprint/sec-fourier-transform/`
`sk-lem-wft-character-integral/lem-fd-affine-line-constant-cohomology.proof.md`,
the integral-coefficients paragraph.
(blueprint: lem-fd-integral-coefficient-reduction-epimorphism)
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- The canonical reduction of pulled-back discrete condensed coefficients.
Source: the integral-coefficients paragraph of the Fourier--Deligne blueprint.
It is the existing coefficient pullback applied to the continuous map of discrete
finite residue rings induced by reduction of integer representatives.
(blueprint: lem-fd-integral-coefficient-reduction-epimorphism) -/
noncomputable def integralCoefficientReduction (X : Scheme.{u}) (ℓ n : ℕ) :
    completedCoefficient X
        (Profinite.continuousMapRingSheaf (ZMod (ℓ ^ (n + 1)))) ⟶
      completedCoefficient X (Profinite.continuousMapRingSheaf (ZMod (ℓ ^ n))) :=
  completedCoefficientMap X
    (Profinite.continuousMapRingSheafMap
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n)))
      continuous_of_discreteTopology)

/-- Finite integral coefficient reductions are epimorphic and locally surjective.

Source: the integral-coefficients paragraph of the Fourier--Deligne blueprint,
phrase "a limit of classical sheaves with epimorphic transition maps".

Proof: write A = Z/ℓ^(n+1), B = Z/ℓ^n and let r be reduction. Every class
represented by an integer a in B is the image of the class represented by a in A.
Thus the map between constant abelian presheaves is surjective at every object
and has zero cokernel. Sheafification preserves cokernels, so its image under
the constant-sheaf functor is an epimorphism. The natural constant-sheaf
comparison `constantSchemeIso X`, applied to r, identifies this map with the
pullback of the discrete condensed reduction. Discrete condensed finite rings
are the continuous-function rings used by `completedCoefficientMap`; the
finite coefficient comparison is natural in r. Consequently the underlying
abelian-sheaf map below is epimorphic. On an arbitrary site an epimorphism of
abelian sheaves is locally surjective: the sieve of arrows on which any given
section admits a lift is covering. Applied to the small pro-etale topology,
this is precisely lifting after a pro-etale covering.
(blueprint: lem-fd-integral-coefficient-reduction-epimorphism) -/
theorem integralCoefficientReduction_epimorphism (X : Scheme.{u}) (ℓ n : ℕ)
    [Fact ℓ.Prime] (hn : 1 ≤ n) :
    Epi (integralCoefficientReduction X ℓ n).hom ∧
      Sheaf.IsLocallySurjective (J := Scheme.ProEt.topology X)
        (A := AddCommGrpCat.{u + 1}) (integralCoefficientReduction X ℓ n).hom := by
  sorry

end AlgebraicGeometry.ProEtale
