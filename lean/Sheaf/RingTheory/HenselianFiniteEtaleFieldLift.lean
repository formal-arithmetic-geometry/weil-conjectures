/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.FieldTheory.Separable

import Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition
import Sheaf.RingTheory.Etale.QuasiFiniteAtPrime
import WeilConjectures.Mathlib.RingTheory.Etale.ResidueField

/-!
# Lifting a finite separable residue-field extension

Source: Stacks Project, Algebra, Tag 04GK, the field-lifting paragraph.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace CommAlgCat.FiniteEtale

/-- A finite separable extension of the residue field lifts to a finite étale algebra.
Source: Stacks Project, Algebra, Tag 04GK, using Tags 00UD and 04GJ.
(blueprint: lem-weil-pbc-henselian-finite-etale-field-lift).

Proof: Apply the prescribed-residue-field étale algebra theorem (00UD) at the maximal
ideal of R to obtain an étale R-algebra C and a prime q over that ideal whose residue
extension is L. Henselian finite-type decomposition (04GJ) writes C as a finite product
of local finite R-algebras Aᵢ and a factor B with no quasi-finite prime above the maximal
ideal. Each factor is an idempotent localization of C, hence étale. Étale algebras are
quasi-finite everywhere (00U5), so B has no prime above the maximal ideal and q belongs
to one Aᵢ. Finiteness over the local base shows that this prime is maximal. The étale
prime-generation theorem (00U4) gives mAᵢ = nᵢ, and hence κ ⊗[R] Aᵢ is its residue
field, compatibly with the prescribed isomorphism to L. Take S to be this finite étale
factor. This is an existence theorem only; it defines no algebra by choosing a witness.
The degree-one case is included, while the field hypothesis excludes the zero algebra. -/
theorem exists_finiteEtale_residueField_equiv_of_finite_separable
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (L : Type (max u v)) [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [Module.Finite (IsLocalRing.ResidueField R) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) L] :
    ∃ S : CommAlgCat.FiniteEtale.{max u v} R,
      Nonempty ((IsLocalRing.ResidueField R ⊗[R] S) ≃ₐ[IsLocalRing.ResidueField R] L) := by
  sorry

end CommAlgCat.FiniteEtale
