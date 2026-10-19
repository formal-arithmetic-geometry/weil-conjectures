/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.FunctionField
public import Sheaf.AlgebraicGeometry.NormalScheme
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.RingTheory.QuasiExcellentNagata

/-!
# Rationality of birational local extensions of excellent regular surface rings

Source: Stacks Project, Resolution of Surfaces, Tags 0B4Q, 0BG0 and 0B4N;
More on Algebra, Tags 07QT and 07QV
(blueprint: lem-per-regular-surface-birational-rational-local-rings).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A normal two-dimensional local domain birational and essentially of finite type over
an excellent regular local surface ring has zero first structure-sheaf cohomology on every
integral normal proper modification. The fraction-field map is the map induced by `i`.
The equality on generic points and bijectivity of the actual stalk map express that `g`
induces an isomorphism of function fields. Cohomology is `Sheaf.H'` at the terminal Zariski
open, with the additive structure sheaf as coefficients.

Source: Stacks Project, Tags 0B4Q, 0BG0, 0B4N, 07QT and 07QV
(blueprint: lem-per-regular-surface-birational-rational-local-rings).

Proof:
1. Excellence gives quasi-excellence and Noetherianity by `def-exc-excellent-ring`.
   Apply `lem-exc-quasi-excellent-nagata` to obtain that `R` is Nagata.
2. Apply `lem-per-regular-surface-rational` to the Nagata regular local ring `R` of
   dimension two. It defines a rational singularity in the sense of
   `def-per-rational-surface-singularity`, including its normal-base-ring requirements.
3. Apply `lem-per-rational-singularity-birational-propagation` to `i : R →+* B`.
   Injectivity, locality, the induced fraction-field isomorphism, essential finite type,
   normality of `B`, and dimension two are exactly its hypotheses. Hence `B` defines a
   rational singularity.
4. Evaluate the universal vanishing in `def-per-rational-surface-singularity` at `Z, g`.
   Properness, integrality, normality and the induced function-field isomorphism say that
   this is a normal modification. By `def-sc-topological-abelian-cohomology`, the resulting
   vanishing is ordinary Zariski cohomology of the additive structure sheaf, as below.
-/
theorem subsingleton_H_one_of_regular_surface_birational_local_extension
    (R B : Type u) [CommRing R] [IsRegularLocalRing R] (hRdomain : IsDomain R)
    [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B]
    (hR : IsExcellent R) (hdimR : ringKrullDim R = 2) (hdimB : ringKrullDim B = 2)
    (i : R →+* B) [IsLocalHom i] (hi : Function.Injective i)
    (hfrac : Function.Bijective
      (IsFractionRing.map (K := FractionRing R) (L := FractionRing B) hi))
    (hfinite : i.EssFiniteType)
    (Z : Scheme.{u}) [IsIntegral Z] (hZ : IsNormalScheme Z)
    (g : Z ⟶ Spec (.of B)) [IsProper g]
    (hgeneric : g (genericPoint Z) = genericPoint (Spec (.of B)))
    (hbirational : Function.Bijective (g.stalkMap (genericPoint Z))) :
    Subsingleton (Sheaf.H'
      ((sheafCompose (Opens.grothendieckTopology Z)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj Z.sheaf)
      1 (⊤ : Z.Opens)) := by
  sorry

end AlgebraicGeometry
