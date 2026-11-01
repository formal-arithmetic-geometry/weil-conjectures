/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbar.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs

/-!
# Finite coefficient lattices on normal schemes

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
 sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
 sk-lem-finite/thm-lisse-qlbar-representations.proof.md`, clause (4), Normality;
 (blueprint: lem-sfb-normal-lisse-finite-coefficient-lattice).

The normality clause supplies an embedded, locally free integral lattice for every
lisse finite coefficient module.  The lattice is expressed by `hasLattice`, whose
inclusion is monic and whose scalar-extension adjoint is invertible.

The source route has an unresolved generic-open lattice premise, recorded as a
BLUEPRINT QUESTION in the delivery report. Its later component and strict-local
steps are recorded below conditional on that premise; the theorem signature is
unchanged.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.LisseQlbar

universe u

section
variable (ell : ℕ) [Fact ell.Prime]
variable (E : PadicAlgCl.FiniteIntermediateField ell)
variable (X : Scheme.{u})
local instance : NormedField E.1 := PadicAlgCl.normedFieldOfAlgebra ell E.1
noncomputable local instance rationalMonObj :
    MonObj (condensedRingObj (fieldRing ell E) X) :=
  Functor.monObjObj (F := upperStarFromPoint X) (fieldRing ell E)
noncomputable local instance rationalCommMonObj :
    IsCommMonObj (condensedRingObj (fieldRing ell E) X) :=
  Functor.isCommMonObj_obj (F := upperStarFromPoint X)

/--
For a nonempty connected locally Noetherian quasi-compact normal scheme, every
lisse module over a finite continuous coefficient field has an embedded integral
lattice.  This is clause (4), Normality, of the lisse representation theorem.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
 sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
 sk-lem-finite/thm-lisse-qlbar-representations.proof.md`, clause (4), Normality;
 (blueprint: lem-sfb-normal-lisse-finite-coefficient-lattice).

Proof plan of the source, with its open point explicitly retained:
(1) The normal decomposition theorem makes connected Noetherian X integral.
The source cites the stratified-lattice result for a lattice on a dense open U.
BLUEPRINT QUESTION: that result assumes separated finite type over a field of
characteristic different from ell, hypotheses absent here. Stop at this premise;
Steps (2)--(5) describe the source argument conditional on it.
(2) On Noetherian affine charts of Lat(L), etale normality and normal decomposition
make the components integral and clopen; no quasi-compactness of all Lat(L) is used.
The lattice section over U is clopen, so the component T′ containing it has T′_U=U.
(3) The filtered-etale-colimit normal-local-domain theorem makes each strict
localization a normal domain. An etale point above its closed point gives a section
by the strictly henselian section theorem, hence a lattice N there.
(4) Strictly henselian finite etale splitting makes the fundamental group trivial.
The integral equivalence of thm-lisse-qlbar-representations clause (1) makes N free.
The trivial-model clause for Lat(L) gives disjoint strict-local copies; T′ has one
point over the generic point, hence exactly one copy.
(5) T′→X is surjective etale and universally injective. The radicial-etale theorem
makes it an open immersion, hence an isomorphism; pull back the universal lattice.
The generic-open premise remains open, without strengthening the statement.
-/
theorem has_lattice_of_normal
    (ell : ℕ) [Fact ell.Prime]
    (X : Scheme.{u}) [Nonempty X] [ConnectedSpace X] [IsLocallyNoetherian X]
    [CompactSpace X]
    (hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z))
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (L : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (fieldRing ell E) X))
    (hL : IsLisseCoefficientModule (fieldRing ell E) L) :
    hasLattice (Λ := integerRing ell E) (B := fieldRing ell E)
      (integerInclusion ell E) X L := by
  sorry

end

end AlgebraicGeometry.ProEtale.LisseQlbar
