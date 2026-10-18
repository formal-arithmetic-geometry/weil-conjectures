/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties

import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.GenericFiniteModulePresentation
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.RingTheory.FinitelyPresentedAlgebraModuleGenericFreeness
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Nonreduced fibres near the generic point

Source: Stacks Project, More on Morphisms, Tag 0575,
Lemma `lemma-nonreduced-in-neighbourhood` (blueprint: lem-trf-nonreduced-fibre-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nonreduced generic fibre of a finite type morphism over an irreducible scheme
spreads to all fibres over a nonempty open subset of the base.

Source: Stacks Project, More on Morphisms, Tag 0575,
Lemma `lemma-nonreduced-in-neighbourhood` (blueprint: lem-trf-nonreduced-fibre-open).

Proof:
1. Base change to the reduction of T, using
   lem-weil-pbc-reduction-universal-homeomorphism. The topology and residue fields are
   unchanged, so the fibres are canonically isomorphic (def-pc-scheme-fibre). Finite type
   persists by lem-weil-pbc-lft-base-change and lem-pc-quasi-compact-base-change. The base
   is now integral (def-pc-integral-scheme).
2. Choose a nonempty affine base Spec A with fraction field K = kappa(xi), using
   lem-sc-integral-function-field-affine-fraction and def-weil-residue-field. The finite
   affine cover supplied by def-weil-finite-type-morphism induces an open cover of the
   generic fibre (lem-weil-pbc-open-fibre-product). By lem-trf-reduced-scheme-open-cover,
   one chart Spec B has nonreduced generic fibre. The affine fibre product description
   (lem-weil-pbc-fibre-product-affine-spectra) and lem-weil-pbc-affine-scheme-reduced-iff
   give a nonzero nilpotent e in B tensor_A K.
3. Identify that tensor product with the localization at nonzero scalars, using
   def-weil-pbc-localization-at-prime at (0). Write e = b/s. If e^n = 0, some nonzero
   a in A kills b^n. Restricting to D(a) makes b/1 nilpotent, and it remains generically
   nonzero. These denominator shrinkings preserve finite type
   (def-weil-ring-localization-away, def-weil-pbc-finite-type-algebra). Write h for b/1.
4. Put I = Ann(h), C = B/I and D = B/hB. These are finite type A-algebras. Multiplication
   by h gives 0 -> C -> B -> D -> 0. No nonzero scalar annihilates h, since h is
   generically nonzero; hence C remains nonzero after any nonzero scalar localization.
5. Choose a finite polynomial algebra P over A surjecting onto B. The P-modules C and D
   are cyclic. Apply lem-pur-generic-finite-module-presentation to each. On the common
   principal restriction both have finite presentations over the localized polynomial
   algebra. Localization preserves their presentations by clearing denominators in the
   kernel (def-weil-pbc-module-localization-away, def-weil-ring-localization-away).
6. Apply lem-pur-fp-algebra-module-generic-freeness to the polynomial algebra and these
   two finitely presented modules. Further localization preserves a basis, so a common
   principal restriction makes C and D free over A (def-weil-pbc-free-module). All the
   restrictions combine to D(g), g nonzero. The sequence remains exact and C nonzero.
7. For any residue field k, the nonzero free module C has nonzero C tensor_A k: a basis
   coordinate exhibits k as a retract. The free module D is flat, so
   lem-weil-pbc-flat-quotient-tensor-injective injects C tensor_A k into B tensor_A k.
   Its image is multiplication by h. If h tensor 1 were zero this injection would be
   zero, a contradiction. Thus h tensor 1 is a nonzero nilpotent. Here scalar extension
   is def-weil-module-base-change and flatness is def-weil-pbc-flat-ring-map.
8. By lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-affine-scheme-reduced-iff,
   the chart fibre is nonreduced. It is open in the whole fibre by
   lem-weil-pbc-open-fibre-product, so the whole fibre is nonreduced
   (def-pc-reduced-scheme). The final principal open contains the generic point, hence
   is nonempty. Transport it back through the reduction, preserving the original fibres.
-/
theorem exists_nonempty_open_nonreduced_fibers_of_nonreduced_generic_fiber
    {Z T : Scheme.{u}} (h : Z ⟶ T) [LocallyOfFiniteType h] [QuasiCompact h]
    [IrreducibleSpace T] (ξ : T) (hξ : IsGenericPoint ξ (Set.univ : Set T))
    (hgeneric : ¬ IsReduced (h.fiber ξ)) :
    ∃ W : T.Opens, (W : Set T).Nonempty ∧ ∀ t : T, t ∈ W → ¬ IsReduced (h.fiber t) := by
  sorry

end AlgebraicGeometry
