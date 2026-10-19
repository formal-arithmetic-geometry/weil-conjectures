/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.PunctualPurity
public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Ideal.IsPrincipal

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity
import Sheaf.AlgebraicGeometry.PunctualPurityTwoOfThree

/-!
# Smooth ascent of punctual purity over a trait

Source: ILO, Exposé XVI, Corollary 3.5.6, printed p.249
(blueprint: lem-per-smooth-punctual-purity-ascent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Smooth finite-type morphisms preserve punctual purity over a trait.

Source: ILO, Exposé XVI, Corollary 3.5.6, printed p.249
(blueprint: lem-per-smooth-punctual-purity-ascent).

Proof plan, following the seven steps of the DAG:
1. The trait is Noetherian. Finite type makes X Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Smooth regularity is
   lem-per-regular-lci-geometric-calculus. Fix y over x. Use affine charts V -> U
   (lem-weil-pbc-smooth-restrict-open-subschemes), shrink to constant relative dimension r
   (sbc-lem-smooth-relative-dimension-locally-constant), and use
   lem-weil-pbc-lft-affine-pairs for finite type. Open restriction preserves the local pair.
2. Put R_x = O_{X,x}, T = Spec R_x, k = kappa(x), P = V x_U T and F = P x_T Spec k.
   The local ring is regular Noetherian and all its localizations are regular. Base-change
   permanence (lem-sbc-smooth-relative-dimension-permanence and
   lem-sfb-finite-type-composition-base-change) makes P and F smooth and Noetherian.
   Smooth regularity gives their regularity; ell is invertible throughout.
3. The closed point i of T is regular of codimension c = dim R_x: minimal generators
   form a regular sequence (lem-weil-pbc-regular-local-generators-regular-sequence).
   Smooth flatness (lem-pc-smooth-flat) and regular immersion base change
   (lem-per-regular-lci-geometric-calculus) give the same codimension for a : F -> P.
   The smooth map P -> T has geometrically regular fibres by smooth base change and
   smooth regularity over fields, including after finite field extensions.
4. Apply lem-per-regular-supported-base-change at n = 1 to the class at x, with
   twist comparison lem-asd-etale-finite-twist-pullback. For a closed immersion the
   compactification (1,i) of def-amb-etale-compact-support identifies Ri_! with exact i_*.
   Its right adjoint agrees with def-per-closed-support-plus-adjunction, together with
   the counit, by adjoint uniqueness. Class flat-base-change compatibility
   (lem-per-regular-immersion-class-calculus) identifies eta_a with the invertible
   comparison composed with pullback of eta_i. Thus the pair (P,F) is pure.
5. The regular Noetherian fibre F is over the prime subfield of k.
   lem-per-prime-field-punctual-purity makes F punctually pure. Neither perfection of k
   nor finite type over its prime field is required.
6. Apply lem-per-punctual-purity-two-of-three to F -> P: purity of the pair and of F
   imply punctual purity of P at the points of F, including y' over y.
7. With U = Spec C, V = Spec B, x = p and y = q, put S = C \ p. The canonical maps
   B tensor_C C_p <-> S^-1 B send b tensor (c/s) to bc/s and b/s to b tensor (1/s).
   Localizing at S^-1 q gives B_q, since S misses q. Hence O_{P,y'} = O_{Y,y},
   compatibly with residue fields, dimension and closed-point inclusions. The canonical
   classes agree by lem-per-regular-immersion-class-calculus, giving purity at y.
   This includes nonclosed y, empty Y, and c = 0 (the identity class).
-/
theorem smooth_punctual_purity_ascent
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hDim : ringKrullDim R = 1) (hPrincipal : (IsLocalRing.maximalIdeal R).IsPrincipal)
    (hInv : IsUnit (ℓ : R))
    {X Y : Scheme.{u}} [X.Over (Spec (.of R))]
    [LocallyOfFiniteType (X ↘ Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    (hX : IsRegularScheme X) (q : Y ⟶ X) [Smooth q]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsNoetherian Y]
    (hPure : IsPunctuallyPure ℓ hℓ X) :
    IsRegularScheme Y ∧ IsPunctuallyPure ℓ hℓ Y := by
  sorry

end AlgebraicGeometry.Etale
