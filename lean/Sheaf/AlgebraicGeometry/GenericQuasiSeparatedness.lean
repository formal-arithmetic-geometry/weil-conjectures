/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties

import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.RingTheory.FinitelyPresentedSupportComplement
import Sheaf.RingTheory.GenericFiniteModulePresentation

/-! # Generic quasi-separatedness

Source: Stacks Project, Tag 052A, proof of generic flatness, last paragraph
(blueprint: lem-pur-generic-quasi-separatedness).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite type morphism to an integral scheme is quasi-separated over a nonempty open.
No Noetherianity or separatedness assumption is imposed on either scheme or the morphism.

Source: Stacks Project, Tag 052A, proof of generic flatness, last paragraph.
(blueprint: lem-pur-generic-quasi-separatedness)

Proof:
1. Choose a nonempty affine open Spec A in T. Integrality makes A a domain
   (def-pc-integral-scheme). Finite type (def-weil-finite-type-morphism) supplies a finite
   affine cover Spec B_i of its inverse image. For each pair i,j choose an ideal I_ij
   cutting out the complement of the intersection inside Spec B_i, and set M_ij = B_i/I_ij.
   These modules are cyclic; no finite generation of I_ij is required.
2. Apply lem-pur-generic-finite-module-presentation to all the M_ij. Invert the product a
   of the resulting nonzero elements of A. The product is nonzero, so D(a) is nonempty;
   further localization preserves the finite presentations. For an empty cover use a = 1.
3. By lem-weil-pbc-principal-localization-open-immersion the restricted charts are
   Spec (B_i)_a. The localized quotient is (B_i)_a/I_ij(B_i)_a, whose support is the zero
   locus of the extended ideal: outside it an ideal element becomes a unit and kills the
   quotient, while on it the quotient maps onto the residue field. Thus
   lem-pur-finitely-presented-support-complement makes every pairwise intersection compact.
4. Apply lem-weil-pbc-quasi-separated-affine-cover-criterion to this affine cover, including
   the empty source case, to obtain a quasi-separated source. Then clause (1) of
   lem-weil-pbc-qcqs-morphism-permanence makes the restricted morphism quasi-separated. -/
theorem exists_nonempty_open_quasiSeparated_restrict {Z T : Scheme.{u}}
    (h : Z ⟶ T) [LocallyOfFiniteType h] [QuasiCompact h] [IsIntegral T] :
    ∃ W : T.Opens, (W : Set T).Nonempty ∧ QuasiSeparated (morphismRestrict h W) := by
  sorry

end AlgebraicGeometry
