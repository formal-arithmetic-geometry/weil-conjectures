/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.Topology.KrullDimension
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds

/-!
# Support-sensitive cohomology on a strictly local punctured spectrum

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Proposition 3.2.1, printed p. 268
(blueprint: lem-per-punctured-support-cohomological-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- On an excellent Noetherian strictly local punctured spectrum, a sheaf of
Z/ell-modules with support closures of dimension at most s has no cohomology in
degrees at least 2s. Closures are taken in the whole local spectrum.
Source: ILO, Travaux de Gabber, Expose XVII, Proposition 3.2.1, printed p. 268
(blueprint: lem-per-punctured-support-cohomological-bound).

Proof plan:
1. Write the local scheme as Spec R. By
   lem-weil-pbc-noetherian-local-finite-krull-dimension its Krull dimension is a
   finite nonnegative integer d; def-weil-pbc-krull-dimension-ring identifies this
   with the dimension of Spec R.
2. Apply the first assertion of lem-per-strict-local-etale-dimension-bounds with
   S = Spec R, its closed point x, exponent n = 1, ambient dimension d and support
   bound e = s. The coefficient ring Z/ell^1 is Z/ell and the puncture is U.
   Excellence, strict henselianity, invertibility and the support condition are
   exactly the hypotheses below. The result is vanishing for p >= 2s, for the
   right derived global sections of the underlying abelian sheaf. No normality,
   constructibility or finite-type hypothesis is used. -/
theorem isZero_cohomology_punctured_of_support_dimension_le
    (R : CommRingCat.{u}) [IsNoetherianRing R] [IsStrictlyHenselianLocalRing R]
    (hR : IsExcellent R) (ℓ : ℕ) (hℓ : ℓ.Prime) (hunit : IsUnit (ℓ : R))
    (U : (Spec R).Opens)
    (hU : (U : Set (Spec R)) = ({IsLocalRing.closedPoint R} : Set (Spec R))ᶜ)
    (F : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (s : ℕ)
    (hs : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ U.toScheme),
      ¬ IsZero (pointedEtaleStalk F t) →
        topologicalKrullDim (closure ({U.ι (t (IsLocalRing.closedPoint Ω))} :
          Set (Spec R))) ≤ (s : WithBot ℕ∞))
    (p : ℤ) (hp : (2 * s : ℤ) ≤ p) :
    IsZero ((cohomology AddCommGrpCat.{u + 1} U.toScheme p).obj
      ((DerivedCategory.singleFunctor
        (Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        ((sheafCompose U.toScheme.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1})).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
