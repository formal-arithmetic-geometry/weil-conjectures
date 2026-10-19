/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Data.ZMod.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.AlgebraicGeometry.EtaleLocalityBaseChange
import WeilConjectures.RingTheory.GRing
import Sheaf.RingTheory.PopescuSmoothing
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit

/-!
# Regular base change for etale derived direct images

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Proposition 4.2.1, printed page 281
(blueprint: lem-per-regular-etale-direct-image-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Regular base change for bounded-below constant prime-power module coefficients.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Proposition 4.2.1, printed page 281
(blueprint: lem-per-regular-etale-direct-image-base-change).

Proof:
1. Apply `lem-weil-pbc-exchange-forget-coefficients`: forgetting coefficients identifies
   the module exchange with the abelian exchange and reflects invertibility. Each
   cohomology sheaf is killed by the positive integer `ℓ ^ n`.
2. Cover `Y` by affine opens mapping into affine opens of `X`. Open immersions are
   etale (`lem-weil-pbc-open-immersion-etale`), so `sbc-lem-etale-locality` reduces
   invertibility of this exchange to the local squares. Base change preserves qcqs
   (`lem-weil-pbc-qcqs-morphism-permanence`); the local source of `g` need not be affine.
3. The coordinate rings of these affine opens are Noetherian
   (`pqf-lem-affine-open-locnoeth`), and their map is flat by
   `lem-weil-pbc-flat-morphism-affine-criterion`. The finite residue-field extensions
   of its fibres are regular by hypothesis, using `def-pc-scheme-fibre` and
   `lem-weil-pbc-fibre-product-affine-spectra`. The coordinate ring map is therefore
   regular in the sense of `def-weil-pbc-g-ring` and `def-weil-regular-scheme`.
4. Apply `lem-weil-pbc-popescu-smoothing` and then the colimit clause of
   `lem-weil-pbc-filtered-category-directed-cofinal`: the target algebra is a directed
   colimit of smooth algebras, with the specified algebra structure preserved.
5. By `lem-weil-pbc-spec-colimit-limit`, its spectrum is the corresponding inverse
   limit, with affine transitions. The smooth affine stage maps are qcqs by
   `lem-weil-pbc-affine-morphism-permanence`. Apply `lem-kun-0f09` with the qcqs
   morphism from step 2. The common annihilator `ℓ ^ n` is invertible on the base.
   Its conclusion is exactly the canonical local abelian exchange isomorphism.
6. Assemble by `sbc-lem-etale-locality` and return to modules using
   `lem-weil-pbc-exchange-forget-coefficients`. No constructibility, finite type of
   `h`, or Noetherianity of `V` enters the argument.

The coefficient ring is lifted only to match the existing site size convention.
Regular fibres are expressed by extending the canonical scheme-theoretic fibre
along every finite residue-field extension, including the identity extension. -/
theorem isIso_derivedBaseChangeMapPlus_of_regular
    (ℓ n : ℕ) (hprime : ℓ.Prime) (hn : 1 ≤ n)
    {X Y V : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (h : Y ⟶ X) [Flat h]
    (hX : IsUnit (ℓ : Γ(X, ⊤))) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    (hreg : ∀ (x : X) (L : Type u) [Field L]
      [Algebra (X.residueField x) L] [Module.Finite (X.residueField x) L],
      IsRegularScheme (pullback (h.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) L)))))
    (g : V ⟶ X) [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))))) :
    IsIso ((derivedBaseChangeMapPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
      (⟨pullback.condition⟩ :
        CommSq (pullback.fst g h) (pullback.snd g h) g h)).app K) := by
  sorry

end AlgebraicGeometry.Etale
