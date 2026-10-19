/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.GabberOpenImmersionSheafFiniteness

/-!
# Bounded constructibility detected by open and exceptional closed restriction

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, Lemma 6.2.2.2,
using Expose XIII, Theorem 1.1.1 and paragraph 1.1.2
(blueprint: lem-per-open-closed-constructible-test).

The coefficient ring is the universe lift of `ZMod (ℓ ^ n)`. The exceptional restriction
is the right adjoint supplied by `lem-exc-closed-ambient` to the ordinary closed direct
image. On bounded-below objects it is the bounded-below exceptional restriction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Bounded constructibility of a bounded-below complex is detected by its ordinary open
restriction and exceptional closed restriction.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, Lemma 6.2.2.2,
and Expose XIII, Theorem 1.1.1 and paragraph 1.1.2
(blueprint: lem-per-open-closed-constructible-test).

Proof, following the nine steps of the DAG node:
1. Exact ordinary inverse image commutes with cohomology
   (prop-weil-pbc-inverse-image-modules-exact, lem-sp-exact-functor-preserves-homology).
   Constructible pullback (prop-constructible-pullback) therefore makes both ordinary
   restrictions preserve constructible cohomology and every cohomological interval.
2. A closed immersion is finite (lem-weil-pbc-closed-immersion-finite). Its abelian direct
   image is exact (lemma-weil-pbc-finite-direct-image-exact). Faithful exact forgetting
   (lem-weil-pbc-module-sheaves-colimits-forgetful) detects exactness for modules as well.
   The counit of prop-openclosed-lowerstar-fully-faithful is linear over Z/ℓ^n and descends
   termwise. Thus closed direct image preserves and reflects cohomological intervals.
3. Finite stalks and the constructibility comparison
   (lem-weil-pbc-constructible-etale-module-sheaf-comparison) allow application of
   lem-weil-pbc-finite-pushforward-finite-stalk-module. Together with steps 1 and 2,
   this makes closed direct image preserve and reflect bounded constructibility.
4. For a constructible sheaf killed by ℓ apply
   lem-per-gabber-open-immersion-sheaf-finiteness over F_ℓ. Excellence implies
   quasi-excellence. The two instances of lem-sbc-higher-direct-image-forget-comparison
   identify its higher direct images over F_ℓ and Z/ℓ^n through abelian sheaves. Every
   abelian homomorphism is Z/ℓ^n-linear, so both constructibility and the sheaf-dependent
   vanishing bound transfer. Negative degrees vanish for a degree-zero sheaf.
5. Filter any constructible sheaf F by the images of ℓ^r for 0 ≤ r ≤ n.
   The quotients are constructible and killed by ℓ (thm-constructible-serre). The short
   exact sequences give triangles (lem-weil-pbc-complex-ses-triangle). Apply the
   triangulated right derived functor (lem-pc-right-derived-functor-triangulated).
   Descending from the zero last filtration term, triangulated constructible closure
   (prop-constructible-derived-subcategory) and step 4 give bounded constructible Rj_*F.
6. For a bounded constructible complex with cohomology in [a,b], use the successive
   lower-truncation triangles (lem-pc-derived-lower-truncation-step-triangle, n = -r).
   Descend from the zero truncation above b to the truncation at a, which is the original
   complex. Step 5 and closure under shifts and extensions give bounded constructible
   open direct image; only finitely many sheaf-dependent bounds occur.
7. The ambient right adjoint (lem-exc-closed-ambient) has the triangle
   i_* Ri^! K → K → Rj_* j^* K → (i_* Ri^! K)[1]
   (lem-exc-closed-support-triangle). If K is bounded below, so is the third term by
   exact restriction and bounded-below direct image (def-weil-pbc-direct-image).
   Triangulated closure of D+ and the counit in step 2 make Ri^! K bounded below.
   Restricting the ambient adjunction therefore gives the specified D+ adjunction.
8. If K is bounded constructible, steps 1 and 6 make j^* K and Rj_* j^* K bounded
   constructible. Rotate the triangle in step 7 and use constructible closure to obtain
   bounded constructible i_* Ri^! K; step 3 reflects it to Ri^! K.
9. Conversely, bounded constructibility of both restrictions makes the first and third
   terms of the same triangle bounded constructible by steps 3 and 6. Triangulated
   constructible closure gives bounded constructibility of its middle term K. -/
theorem isBoundedConstructible_iff_open_closed_exceptional
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (_hn : 1 ≤ n)
    {X Z U : Scheme.{u}} [IsNoetherian X]
    (_hexc : ∀ V : X.affineOpens, IsExcellent Γ(X, V))
    (_hinv : ∀ x : X, IsUnit (ℓ : X.presheaf.stalk x))
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))))) :
    DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod (ℓ ^ n))) X K.obj ↔
      DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod (ℓ ^ n))) U
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
          j).mapDerivedCategory.obj K.obj) ∧
      DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod (ℓ ^ n))) Z
        ((R(lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
          i)).rightAdjoint.obj K.obj) := by
  sorry

end AlgebraicGeometry.Etale
