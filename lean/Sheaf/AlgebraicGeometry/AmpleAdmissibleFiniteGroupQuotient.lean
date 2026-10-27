/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Ampleness on an already constructed finite group quotient

Source: Rydh, arXiv:0708.3333v2, Proposition 4.7, norm argument;
Stacks Project, Properties Tags 01PS, 01PV and 09NV.
(blueprint: lem-per-ample-admissible-finite-group-quotient)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Absolute ampleness descends to an admissible finite group quotient. The scheme
Q and its quotient map are inputs. Neither quotient existence nor any relative
projective-space embedding is asserted.

Source: Rydh Proposition 4.7, norm argument; Stacks Properties 01PS, 01PV, 09NV.
(blueprint: lem-per-ample-admissible-finite-group-quotient).

Proof:
1. Form N=the tensor product over h∈H of a_h^*L with permutation linearization.
   Apply orbit_tensor_line_descent to the invariant-section formula in hq.
   Its formulas expressed on equal inverse-image opens are equivalent to the
   overlap equations in hq: restrict the equation on the whole invariant open
   to any common subopen, and conversely take that whole open. This supplies
   an invertible M on Q, the isomorphism q^*M≅N and fixed sections for every
   tensor power. The fixed-section inclusion specifies M uniquely as a subsheaf.
2. For y∈Q its inverse image E is a finite orbit, by finiteness, surjectivity
   and the orbit-fibre clause of hq. Choose a positive-power section s of L
   with affine nonvanishing locus containing E, using the ample finite-set lemma.
   Tensor all a_h^*s. The tensor comparison identifies it as a section σ of N^d,
   fixed by the permutation linearization, so descent gives t in Γ(Q,M^d).
3. The pullback and tensor fibre formulas identify V_σ with the intersection of
   the finitely many inverse images of V_s. It contains E. Begin with the
   identity factor V_s and successively apply affine_cap_section_open to the
   other section factors. Thus this invariant intersection is affine.
4. The fibre formula and q^*M≅N give q^-1(Q_t)=V_σ. An invariant affine open
   Spec A in an admissible quotient has affine image Spec A^H: the orbit
   topology identifies their spaces, and the sectionwise invariant formula
   identifies their sheaves by C_f=(A_f)^H, proved by a common annihilating
   power for the finitely many differences h(a)-a. This works with zero divisors.
   Therefore Q_t is affine and contains y.
5. Q is quasi-compact, as the continuous surjective image of V, which is
   quasi-compact by ampleness. The sections t through each point are exactly
   the remaining clause of the absolute ample criterion, proving M ample.
The proof uses no properness, normality, freeness or restriction on characteristic.
For an empty source the quotient is empty by surjectivity and the ample criterion
is vacuous; for the trivial group the orbit tensor is L and the quotient is V. -/
theorem exists_ample_on_admissible_finiteGroup_quotient
    {V Q : Scheme.{u}} [IsNoetherian V]
    (H : Type v) [Group H] [Finite H] (a : H →* Aut V) (q : V ⟶ Q)
    (hq : IsAdmissibleFiniteSchemeQuotient a q)
    (L : V.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple V L) :
    ∃ (M : Q.Modules) (hM : M.IsInvertible), @Scheme.Modules.IsAmple Q M hM := by sorry

end AlgebraicGeometry
