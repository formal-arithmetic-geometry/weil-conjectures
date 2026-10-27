/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Compactness.Compact
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier
import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-!
# Geometry of the blowup at a regular surface point

Source: Stacks Project, Resolution of Surfaces, Tags 0AGQ and 0AGR, globalized by
flat base change and the complement isomorphism
(blueprint: lem-sfb-regular-point-blowup-geometry).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Blowing up the reduced closed point of local dimension two preserves integral,
regular, Noetherian geometry. The blowup is proper, is unchanged off the point, and
has dimension-two local rings at closed exceptional points.

Source: Stacks Project, Tags 0AGQ and 0AGR
(blueprint: lem-sfb-regular-point-blowup-geometry).

Proof plan:
1. The reduced point ideal is quasi-coherent and finite type on the Noetherian base
   (def-sbc-closed-immersion-ideal-sheaf, pqf-def-coherent). It is nonzero since its
   localization has dimension two, whereas a field has dimension zero.
2. Properness follows from lemma-nagata-blowup-proper, and Noetherianity from
   lem-weil-pbc-finite-type-over-noetherian. The complement of the center is nonempty
   and integral. Its inverse image is scheme-theoretically dense by
   det-nagata-boundary-divisor-cartier and is isomorphic to that complement by
   thm-nagata-global-blowup-complement. Thus every nonempty affine ring of the blowup
   embeds in the function field (lem-sc-integral-function-field-affine-fraction),
   proving integrality.
3. The complement isomorphism identifies local rings away from the center with
   regular local rings of X (def-weil-regular-scheme).
4. Localize X at p using lem-weil-pbc-spec-local-ring-canonical-morphism. Flat base
   change identifies the pullback blowup with the blowup of the maximal ideal in
   the regular local ring O_{X,p} (thm-nagata-blowup-flat-base-change).
5. On affine charts this base change is B to T^{-1}B, where T is the complement of
   the prime for p. Every prime Q above p avoids T and has a unique lift T^{-1}Q
   (lem-weil-pbc-localization-base-change, lem-weil-pbc-localization-spectrum-embedding).
6. The local rings B_Q and (T^{-1}B)_{T^{-1}Q} are canonically isomorphic: the
   inverse sends (b/s)/(d/t) to bt/(sd), with s,t in T and d outside Q
   (lem-weil-pbc-affine-open-stalk-localization).
7. Apply lem-sfb-local-surface-maximal-blowup-geometry to O_{X,p}. Regularity of its
   blowup transfers along these local-ring isomorphisms to every point over p;
   step 3 handles all other points.
8. If q is closed, its unique lift is closed, since its singleton is the inverse
   image of the closed singleton {q}. The local surface theorem gives dimension
   two there, and the local-ring isomorphism preserves ringKrullDim
   (def-weil-pbc-krull-dimension-ring).
-/
theorem regular_point_blowup_geometry (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hX : IsRegularScheme X) (p : X) (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    IsIntegral (IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowup ∧
    IsRegularScheme (IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowup ∧
    IsNoetherian (IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowup ∧
    IsProper (IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowupMap ∧
    IsIso ((IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowupMap ∣_
      (⟨({p} : Set X)ᶜ, hp.isOpen_compl⟩ : X.Opens)) ∧
    ∀ q : (IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowup,
      IsClosed ({q} : Set (IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowup) →
      (IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowupMap q = p →
      ringKrullDim ((IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowup.presheaf.stalk q) = 2 := by
  sorry

end AlgebraicGeometry.Scheme
