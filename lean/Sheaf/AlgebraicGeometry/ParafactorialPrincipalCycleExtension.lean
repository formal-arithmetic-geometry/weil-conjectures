/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.LocallyFinitePrincipalCycle
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PuncturedCurveBranches
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Extension of principal cycles from an arbitrary subset

Source: EGA IV4, Corollary 21.13.15, implication (b) implies (a)
(blueprint: lem-sfb-parafactorial-principal-cycle-extension).

The cycle is Mathlib's `AlgebraicCycle X ℤ` (locally finite support), with nonzero
coefficients only at points of one-dimensional local ring. Normality is stated on all
stalks, so the scheme need not be integral. The closure condition is global, even for
an arbitrary subset `T`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicCycle

/-- Punctured-local triviality extends local equations of a codimension-one cycle from
any subset `T` to the entire locally Noetherian normal scheme.

Source: EGA IV4, Corollary 21.13.15 (b) implies (a), with punctured-spectrum
invertible-module triviality expressing parafactoriality in the normal case
(blueprint: lem-sfb-parafactorial-principal-cycle-extension).

Proof:
1. Choose a Noetherian affine neighbourhood meeting only finitely many cycle terms
   (pqf-lem-affine-open-locnoeth). Normality is unchanged by open restriction.
   Use the open integral components of rem-pc-regular-normal and an affine refinement
   to work on Spec A for a Noetherian normal domain A. The stalk identifications of
   lem-weil-pbc-spec-domain-stalks-function-field and
   lem-weil-pbc-normal-domain-of-local-normal give normality of A. The restricted
   cycle is a finite height-one divisor.
2. Form the embedded fractional module I_A(D) using
   lem-per-divisorial-fractional-module-lattices. It is finite and its localization
   at a point agrees with the local divisor module, by
   lem-weil-pbc-localization-noetherian, lem-weil-pbc-localization-normal-domain and
   lem-weil-pbc-localization-prime-residue-field-iso. The intersection of height-one
   lattices shows that local principality is equivalent to this module being aB
   for a nonzero fraction a: divide by a for one implication, and take orders in
   each height-one DVR for the other.
3. This locus P is open. If a finite module M is cyclic at p, represent a generator
   by m/s with s outside p. For each of finitely many generators m_i, clear a
   denominator of m_i/m outside p. Their product t gives M_t = m A_t, so D(t)
   lies in P. The chart argument glues. The closed complement N misses T.
4. A normal zero-dimensional local domain is a field, so its empty divisor has
   equation 1. A one-dimensional normal Noetherian local domain is a DVR by
   lem-sc-normal-dim1-dvr; an integer power of a uniformizer gives any coefficient.
   Consequently all points of N have local dimension at least two.
5. If N is nonempty, choose a generic point eta of an irreducible component of
   N in a Noetherian affine chart, using lem-sc-noetherian-closed-subset-finite-components
   and lem-weil-pbc-scheme-sober. Every strict generization of eta is outside N:
   otherwise its closure would enlarge that component. Since N is globally closed,
   the closure of eta in X is contained in N and misses T.
6. Put B = O_{X,eta}. The canonical local-spectrum morphism of
   lem-weil-pbc-spec-local-ring-canonical-morphism identifies the punctured spectrum
   with strict generizations and preserves their local rings. Thus the localized
   divisor module J is cyclic there. The same denominator argument, together with
   lem-weil-pbc-spec-module-tilde-sections, makes its associated sheaf on the puncture
   invertible. The hypothesis provides a trivialization by the structure sheaf.
7. The image of 1 in this trivialization is one nonzero fraction a in Frac(B): every
   nonempty basic open contains the generic point and its sections embed in Frac(B),
   compatibly with restriction (lem-weil-pbc-spec-module-tilde-sections). Every
   height-one prime lies in the puncture since dim B is at least two. On its stalk
   J_q = a B_q, and the lattice formula of lem-per-divisorial-fractional-module-lattices
   gives the prescribed valuation of a. This is principality at eta, contradicting
   eta in N. Hence N is empty. -/
theorem isPrincipalAt_of_punctured_triviality
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (T : Set X)
    (hpunctured : ∀ x : X, 2 ≤ ringKrullDim (X.presheaf.stalk x) →
      Disjoint (closure ({x} : Set X)) T →
      ∀ L : (puncturedSpectrum (X.presheaf.stalk x)).toScheme.Modules,
        L.IsInvertible → Nonempty (L ≅ SheafOfModules.unit _))
    (D : AlgebraicCycle X ℤ)
    (hD : ∀ z : X, D z ≠ 0 → ringKrullDim (X.presheaf.stalk z) = 1)
    (hT : ∀ x : X, x ∈ T → D.IsPrincipalAt x (hX x).1 (hX x).2) :
    ∀ x : X, D.IsPrincipalAt x (hX x).1 (hX x).2 := by
  sorry

end AlgebraicGeometry.AlgebraicCycle
