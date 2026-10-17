/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import WeilConjectures.SixFunctors.BaseChange.Square
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Extension by zero under a proper modification

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
lem-finrepair-modification-extension-zero; Stacks Project, Tags 03S6, 03S5, 03Q1, 0DDF.
(blueprint: lem-finrepair-modification-extension-zero)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Extension by zero from the isomorphism locus of a proper map has no positive higher
 direct images, and its canonical adjunction map is an isomorphism.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc, lemma of the same name;
Stacks Project, Tags 03S6, 03S5, 03Q1, 0DDF and 04JN.
(blueprint: lem-finrepair-modification-extension-zero)

Proof:
1. Put `F = j'_! h⁻¹ G`, `E = j_! G`. By
lem-weil-pbc-etale-shriek-base-change-modules, the base-change map `b : F ⟶ π⁻¹ E`
is invertible. Open immersions are etale (lem-weil-pbc-open-immersion-etale), and their
etale lower shriek is the open extension by zero, since there is at most one lift.
The stated map is the adjoint of `b⁻¹` under def-weil-pbc-inverse-image.
2. For every geometric point of `X`, apply cor-weil-pbc-geometric-fiber-finite to
`F[0]`. The derived fibre formula needs finite coefficients, not finite stalks of `F`.
3. Outside `U`, every geometric stalk of the fibre restriction of `F` is zero, by
lem-weil-pbc-extension-by-zero-stalks and lem-weil-pbc-inverse-image-stalk-germ.
By lemma-weil-pbc-geometric-stalk-conservative that restriction is zero. Its derived
direct image and the stalk of `E` are therefore zero.
4. Inside `U`, the fibre is the geometric point itself because `h` is an isomorphism.
By lem-weil-pbc-geometric-point-pullback-stalk, its section functor is exact; the
fibre's cohomology is `G`'s stalk in degree zero and zero in positive degrees.
By lem-weil-pbc-exchange-forget-coefficients and lem-weil-pbc-derived-exchange-termwise,
the degree-zero comparison is the underived exchange of def-weil-pbc-underived-exchange.
Its section formula (def-weil-pbc-direct-image), composed with the stated adjunction
map, gives the inverse of the base-change stalk isomorphism: compatibility of the unit
with germs is lem-weil-pbc-inverse-image-stalk-germ. Hence the actual stated map,
and not just some map between the same objects, is invertible at this stalk.
5. Exactness of inverse image (prop-weil-pbc-inverse-image-modules-exact) and exact
sections at a geometric point identify higher-direct-image stalks with these fibre
cohomology groups. Apply lemma-weil-pbc-geometric-stalk-conservative to the map and
to each positive higher direct image. Forgetting coefficients reflects both
isomorphisms and zero objects; all comparisons are module-linear. -/
theorem modification_extension_zero
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Y U X : Scheme.{u}} (π : Y ⟶ X) [IsProper π]
    (j : U ⟶ X) [IsOpenImmersion j] [IsIso (pullback.snd π j)]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).homEquiv _ _
      ((@inv _ _ _ _ (etaleLowerShriekBaseChangeMap Λ π j)
        (isIso_etaleLowerShriekBaseChangeMap Λ π j)).app G)) ∧
    ∀ q : ℤ, 0 < q →
      IsZero (higherDirectImage Λ π q
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst π j)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) (pullback.snd π j)).obj G))) := by
  sorry

end AlgebraicGeometry.Etale
