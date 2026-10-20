/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift

import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.AlgebraicGeometry.DerivedExchangeTermwise
import Sheaf.Paper.KunBaseChange
import Sheaf.AlgebraicGeometry.StalkFaithfulDerived
import WeilConjectures.Mathlib.RingTheory.Adjoin.FG
import Sheaf.AlgebraicGeometry.LimitFibreProducts
import Sheaf.Targets.BaseChangeTowardsFields
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.Paper.KunBcMapOnCohomology
import Sheaf.AlgebraicGeometry.HigherDirectImagesLimits

/-!
# Untensored base change for an arbitrary scheme over a field

Source: Stacks Project, Tags 0F1I and 0EZT, the arbitrary-scheme reduction in the proof
of Tag 0F1I, as used in Tag 0F1J
(blueprint: lem-kun-0f1j-arbitrary-scheme-untensored-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Untensored base change for an arbitrary scheme over a field with prime-field coefficients.
Source: Stacks Project, Tags 0F1I and 0EZT, used in Tag 0F1J
(blueprint: lem-kun-0f1j-arbitrary-scheme-untensored-base-change).

Here `X' = pullback z (S' ↘ Spec (.of K))`, its projections are `p = pullback.fst` and
`f' = pullback.snd`, and `Y = pullback f' g` with projections `h = pullback.fst` and
`e = pullback.snd`. The square supplied to `derivedBaseChangeMapPlus` is oriented as
`CommSq e h g f'`. By the definition of the exchange, this is the mate under
`h⁻¹ ⊣ Rh_*` of the inverse image by `e` of the counit for `g`, after the canonical
identification `h⁻¹ f'⁻¹ ≅ e⁻¹ g⁻¹`. The `ULift` only places the prime coefficient field
in the universe of the existing module-valued sheaf interface.

Proof, following the seven steps of the node:

1. Forget the module coefficients, using lem-weil-pbc-exchange-forget-coefficients to
identify the exchange and reflect its invertibility. Every stalk of the underlying
abelian sheaf A is killed by ℓ, so its elements have order 1 or ℓ, invertible in K.
2. The assertion is local on Z. Restrict to an affine open U. Exact inverse image and
lem-weil-pbc-etale-restriction-injectives restrict an injective resolution to an injective
resolution. By lem-weil-pbc-etale-underived-exchange-restriction and
lem-weil-pbc-open-immersion-etale, the termwise open exchange is invertible. The restricted
bounded-below injective complex is K-injective by lem-weil-pbc-dplus-injective-representative.
Apply lem-weil-pbc-derived-exchange-termwise with this complex as its own K-injective
resolution to get the derived open exchange. Clause (1) of lem-kun-bc-base-change identifies
the restricted exchange with that for U. These opens cover X', so
lem-kun-stalk-faithful-derived reduces the assertion to Z = Spec B.
3. By lem-kun-algebra-union, the finitely generated K-subalgebras Bᵢ of B form a nonempty
directed system with union B: the image of K starts the system, and adjoining two finite
generating sets gives an upper bound. Compatible maps on the Bᵢ uniquely glue to a ring
map on B, so B is their ring colimit. Each Zᵢ = Spec Bᵢ is finite type over K.
4. By lem-weil-pbc-spec-colimit-limit, Z is the inverse limit of the Zᵢ with affine
transitions. Apply lem-weil-pbc-limit-fibre-products to identify X' and Y as the limits of
X'ᵢ = Zᵢ ×_K S' and Yᵢ = Zᵢ ×_K T, again with affine transitions. The systems S' and T
are constant with identity transitions. The projection compatibilities identify the limit
square with the original square; Y ≅ Z ×_K T follows from the pullback universal property.
5. Apply lem-kun-0f1i at each finite-type Zᵢ to A. Its torsion-order assumption follows
from step 1, and its qcqs assumption is the given one on g. By
lem-kun-unbounded-exchange-agrees, its unbounded exchange is the image of the bounded-below
exchange. The inclusion D⁺ → D is full, so the latter is invertible. By
lem-kun-bc-map-on-cohomology, every nonnegative cohomology exchange is invertible.
6. Apply lem-kun-0ezt to the system of squares, with constant coefficients A on the
constant T-system. All transitions are affine and every bottom morphism is the given qcqs
g. The coefficient system has colimit A because the index is nonempty and directed.
Step 5 supplies each degree-q hypothesis. Thus the specified degree-q exchange for the
original square is invertible for every q ≥ 0.
7. The negative cohomology of both endpoints vanishes, since A is in degree zero and
exact inverse image and right-derived direct image are left t-exact, by their resolution
formulas. By lem-kun-bc-map-on-cohomology and
lem-weil-pbc-unbounded-derived-iso-cohomology, the abelian exchange is invertible for affine
Z. Step 2 gives arbitrary Z, and lem-weil-pbc-exchange-forget-coefficients gives the stated
prime-field-linear exchange. -/
theorem arbitraryScheme_untensored_baseChange
    {K : Type u} [Field K] {Z S' T : Scheme.{u}}
    (z : Z ⟶ Spec (.of K)) [S'.Over (Spec (.of K))]
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsIso ((derivedBaseChangeMapPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      (CommSq.mk (pullback.condition
        (f := pullback.snd z (S' ↘ Spec (.of K))) (g := g)).symm)).app
      ((_root_.DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) 0).obj F)) := sorry

end AlgebraicGeometry.Etale
