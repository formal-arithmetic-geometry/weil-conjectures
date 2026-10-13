/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Projectivity of zeroth opcycles from connective residue homology

Source: Stacks Project, Tag 00O0, negative-tail splitting argument.
(blueprint: lem-sc-residue-connective-projective-opcycles).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The last cokernel in a bounded finite projective negative tail is finite projective
if every residue complex is exact in negative degrees.

Source: Stacks Project, Tag 00O0; the negative-tail cancellation argument in
lem-sc-universal-h0-projective-normalization.
(blueprint: lem-sc-residue-connective-projective-opcycles).

Proof: Choose a lower support bound a and induct on max(0,-a). If a is nonnegative,
P^(-1) is zero, so opcycles in degree zero is P^0 and is finite projective.
Otherwise the incoming term at a is zero. Negative residue homology vanishing
makes d:P^a -> P^(a+1) residue-injective at every prime. Tag 00O0 makes this
map injective with projective cokernel locally. Its cokernel is finitely presented
as the cokernel of a map between finitely presented modules. The local-to-global
criterion Module.projective_of_localization_maximal therefore makes it projective
globally; it is finite as a quotient of P^(a+1). Split the map, remove P^a and
its image, and replace P^(a+1) by its cokernel. The resulting complex has a higher
lower bound and finite projective terms. The removed pair is contractible, so
scalar extension preserves its homotopy equivalence and the residue vanishing.
If a < -1, the degree-zero term and the image of its incoming differential are
unchanged, hence so are zeroth opcycles. If a = -1, the new degree-zero term
is exactly the original zeroth opcycles. Apply induction, transferring along
these identifications. This is a statement about the canonical quotient P.opcycles 0,
not a choice of a new complex. Empty support intervals and the zero ring are allowed. -/
theorem residueConnective_projective_opcycles
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite R (P.X n))
    (hp : ∀ n : ℤ, Module.Projective R (P.X n))
    (hnegative : ∀ (p : Ideal R) [p.IsPrime],
      let Pp := ((ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomologicalComplex
        (.up ℤ)).obj P
      ∀ i : ℤ, i < 0 → IsZero (Pp.homology i)) :
    Module.Finite R (P.opcycles 0) ∧ Module.Projective R (P.opcycles 0) := by sorry

end CochainComplex
