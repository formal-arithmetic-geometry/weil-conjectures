/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic

import Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf
import Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.RingTheory.StrictHenselizationRegular
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.TraceFormula.DerivedSectionsFinitePushforwardModules
import Sheaf.TraceFormula.FiniteBaseStrictLocalization
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Finite flat descent of regular-divisor purity

Source: ILO, Exposé XVI, Proposition 3.4.3, printed p.246
(blueprint: lem-per-finite-flat-regular-divisor-purity-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Transpose a supported derived morphism under the actual closed direct-image adjunction.
The explicit source and target keep the chosen right adjoint opaque during elaboration.
Source: ILO XVI 2.3.1; ordinary closed adjunction lem-exc-closed-ambient
(blueprint: lem-per-finite-flat-regular-divisor-purity-descent). -/
@[irreducible]
def purityClosedClassTranspose (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (K : DerivedCategoryModule A Z) (L : DerivedCategoryModule A X)
    (k : (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.obj K ⟶ L) :
    K ⟶ (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.rightAdjoint.obj L :=
  (Adjunction.ofIsLeftAdjoint
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).homEquiv K L k

/-- Select the unique supported Cartier boundary from its recorded existence theorem.
Its relative torsor boundary fixes the class uniquely, including its sign.
Source: Stacks 03PL, 0A45; ILO XVI 2.3.1
(blueprint: lem-per-finite-flat-regular-divisor-purity-descent). -/
@[irreducible]
def purityCartierSupportedClass (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hX : IsUnit (m : Γ(X, ⊤))) :
    Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine X m A hA) 2 :=
  Classical.choose (ExistsUnique.exists
    (ordinary_supported_kummer_uniqueBoundary X m hm A hA hX i hI))

/-- The canonical Cartier class is the transpose of the unique relative supported Kummer
boundary, normalized by the divisor section and the positive Chern class of O(D).
This is the codimension-one class of regular_immersion_class_calculus, whose normalization
uses precisely SupportedKummerBoundary. Source: ILO XVI 2.3.1, 3.4.3
(blueprint: lem-per-finite-flat-regular-divisor-purity-descent). -/
@[irreducible]
def purityCartierClassMap (ℓ : ℕ) (hℓ : ℓ.Prime)
    {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hX : IsUnit (ℓ : Γ(X, ⊤))) :=
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  purityClosedClassTranspose (ULift.{u + 1} (ZMod ℓ)) i _ _
      (supportedExactDerivedMap
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) i)
        (ordinaryFiniteConstant (ULift.{u + 1} (ZMod ℓ)) D)
        (Scheme.finiteEtaleTateLine X ℓ (ULift.{u + 1} (ZMod ℓ))
          (congrArg ULift.up (ZMod.natCast_self ℓ)))
        (purityCartierSupportedClass (ULift.{u + 1} (ZMod ℓ)) ℓ hℓ.pos
          (congrArg ULift.up (ZMod.natCast_self ℓ)) i hI hX))


/-- The reduced inverse-image divisor, using the actual nilradical reduction of the fibre
product. Source: ILO XVI Proposition 3.4.3
(blueprint: lem-per-finite-flat-regular-divisor-purity-descent). -/
abbrev purityReducedInverseImage {Y X D : Scheme.{u}} (f : Y ⟶ X) (i : D ⟶ X) :=
  (pullback f i).nilradical.subscheme

/-- The canonical inclusion of the reduced inverse image into Y, retaining the scheme
structure and not just its underlying closed subset. Source: ILO XVI Proposition 3.4.3
(blueprint: lem-per-finite-flat-regular-divisor-purity-descent). -/
abbrev purityReducedInverseImageι {Y X D : Scheme.{u}} (f : Y ⟶ X) (i : D ⟶ X) :
    purityReducedInverseImage f i ⟶ Y :=
  (pullback f i).nilradical.subschemeι ≫ pullback.fst f i

/-- Regular-divisor purity descends along a finite locally free morphism of positive
constant degree prime to the coefficient characteristic, without generic etaleness.
Source: ILO XVI Proposition 3.4.3, printed p.246
(blueprint: lem-per-finite-flat-regular-divisor-purity-descent).

Proof:
1. By lem-per-divisor-purity-strict-local-criterion, fix a geometric point of D and
   pass to its strict henselization S. It suffices to show H^q(S minus D,A)=0 for q>=2.
   Use lem-trf-closed-immersion-strict-localization-cartesian to identify the divisor.
2. By lem-trf-finite-base-strict-localization, Y over S is a finite disjoint union of
   strict localizations. They are Noetherian and regular by
   lem-sc-strict-henselization-noetherian and lem-sc-strict-henselization-regular.
   The Cartier ideal and its radical have the same closed support. The complementary
   cover V over U remains finite locally free of rank d, by lem-pc-flf-properties,
   lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-finite-flat-rank-iso.
   No commutation of reduction with arbitrary base change is asserted.
3. Apply the strict-local criterion to (Y,D'). The hypothesis gives vanishing on
   every complementary component in degrees q>=2. Sections and injective resolutions
   on a finite disjoint union are componentwise; exact finite products give H^q(V,A)=0.
4. By lem-pur-quasifinite-flat-weighted-trace the trace composed with the unit is d.
   Since ell does not divide d, the unit splits. The comparison
   lem-trf-derived-sections-finite-pushforward-modules then makes H^q(U,A) inject
   into H^q(V,A), hence vanish for q>=2.
5. Apply the converse strict-local criterion at every geometric point of D. This
   proves invertibility of the specified Kummer class of (X,D).
-/
theorem finite_flat_regular_divisor_purity_descent (ℓ : ℕ) (hℓ : ℓ.Prime)
    {Y X D : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (hY : IsRegularScheme Y) (hX : IsRegularScheme X)
    (hℓY : IsUnit (ℓ : Γ(Y, ⊤))) (hℓX : IsUnit (ℓ : Γ(X, ⊤)))
    (f : Y ⟶ X) (d : ℕ) [f.IsFiniteLocallyFreeOfDegree d]
    (hd : 0 < d) (hℓd : ¬ ℓ ∣ d)
    (i : D ⟶ X) [IsClosedImmersion i] (hD : IsRegularScheme D)
    (hI : i.ker.IsInvertible)
    (hD' : IsRegularScheme (purityReducedInverseImage f i))
    (hI' : (purityReducedInverseImageι f i).ker.IsInvertible)
    (hpure : IsIso (purityCartierClassMap ℓ hℓ (purityReducedInverseImageι f i) hI'
      hℓY)) :
    IsIso (purityCartierClassMap ℓ hℓ i hI hℓX) := by
  sorry

end AlgebraicGeometry.Etale
