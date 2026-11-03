/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.LatticeSubquotientFiltration
import all WeilConjectures.AlgebraicGeometry.SixFunctors.LatticeSubquotientFiltration
import WeilConjectures.AlgebraicGeometry.OrderedSpectralLatticesAnyCharacteristic

/-! # Lattice subquotient filtration over an arbitrary field

Source: latest blueprint, `part-six-operations/sec-reduction-finite-coefficients/`
`sec-integral-models/sk-lem-integral-models/sk-lem-integral-models-generators.proof.md`,
proof (1)
(blueprint: lem-sfb-lattice-subquotient-filtration).

The existing conclusion predicate uses the pulled-back condensed coefficient rings,
actual lattice inclusions, and subobjects of the canonical locally closed extension.
This statement includes characteristic zero and reuses that predicate unchanged.
-/

@[expose] public section

set_option autoImplicit false
set_option cleanup.letToHave false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A lisse E-module on a separated finite-type scheme over any field of characteristic
other than ell has stratified integral lattices and an ordered extension-by-zero filtration.
Its successive quotients are the rationalized integral extensions along the composite
stratum immersions. The predicate allows varying rank, empty strata, and zero quotients.

Source: latest blueprint, `part-six-operations/sec-reduction-finite-coefficients/`
`sec-integral-models/sk-lem-integral-models/sk-lem-integral-models-generators.proof.md`,
proof (1),
from the stratified lattices through the rationalized extension-by-zero quotients
(blueprint: lem-sfb-lattice-subquotient-filtration).

Proof plan:
1. Finite type over the field makes S and X Noetherian, by
   `lem-weil-pbc-finite-type-over-noetherian`. Apply `lem-sfb-ordered-spectral-lattices`
   to get a finite stratification with open prefixes, lisse integral modules, monic
   inclusions into the restricted rational module, and invertible scalar adjoints.
   Use its arbitrary-field form; no positive-characteristic assumption is required.
2. Apply `lem-sfb-locally-closed-ordered-filtration` to the actual canonical a_! L.
   Exact locally closed extension transports the open-prefix filtration, and
   transitivity identifies each quotient with the extension of the rational restriction
   along the composite stratum immersion.
3. Invert the scalar adjoint of each lattice inclusion and map this isomorphism through
   extension by zero. Compose with `lem-sfb-condensed-locally-closed-scalar-extension`.
   The quotient is then E_X tensor over O_E,X with the integral composite extension.
   No derived rationalization or flatness hypothesis enters this argument. Empty strata
   and zero ranks give repeated terms, so the filtration inequalities are non-strict. -/
theorem exists_latticeSubquotientFiltration_of_char_ne (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] (_hchar : ringChar k ≠ ℓ)
    (S X : Scheme.{u}) [S.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (a : S ⟶ X) [a.IsOver (Spec (.of k))] [IsImmersion a] :
    LatticeSubquotientFiltration ℓ E k a := by
  have hlat := exists_orderedSpectralLattices_of_char_ne ℓ E k _hchar S
  let := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  let A := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E))
  let B := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
  let c := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)
  have : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E))
      (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers ℓ E)) ↦
        mul_comm a b)
  have : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
      (fun U (a b : ULift.{u + 1} C(U.unop, E)) ↦ mul_comm a b)
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have : IsNoetherian S :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k)) }
  have result := @lattice_filtration_from_lattices _ _ _ _ _ _ _ _ S X
    inferInstance inferInstance a inferInstance hlat
  exact result

end AlgebraicGeometry.ProEtale
