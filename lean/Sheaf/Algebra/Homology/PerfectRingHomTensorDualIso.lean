/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Algebra.Homology.PerfectRingDualTermFlat
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap

/-! # Finite-projective Hom as the total tensor with the explicit dual

Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1).
(blueprint: lem-pc-perfect-ring-hom-tensor-dual-iso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

/-- Hom from a bounded finite-projective complex is tensor with its explicit dual.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1), expanded
finite-projective representative argument.
(blueprint: lem-pc-perfect-ring-hom-tensor-dual-iso)

Proof: evaluation on the unique object identifies internal sheaf Hom and tensor
with linear Hom and tensor over A. Projection identifies the degree-r term of
perfectRingDual P with Hom(P^(-r),A). For a finite free module the evaluation map
Hom(M,A) tensor N -> Hom(M,N) is an isomorphism by a basis and its dual basis.
For a finite projective module restrict this map and its inverse along a splitting
as a summand of a finite free module. Apply these maps with M=P^(-r) and N=Q^s.
The diagonal r+s=n is finite after deleting zero source factors, by the bounds on P.
Thus the direct sum of these maps identifies the total tensor degree with the
product of Hom(P^p,Q^(p+n)), after p=-r. With the Hom differential on the dual,
send a homogeneous pure tensor lambda tensor y in degrees r,s to the map
x -> (-1)^(r*s) lambda(x)*y. The postcomposition differential has coefficient
(-1)^r on the tensor side, and changing s to s+1 changes this sign by (-1)^r.
The dual differential is -(-1)^r precomposition; changing r to r+1 changes
the evaluation sign by (-1)^s. These give precisely the two terms
 d_Q f - (-1)^(r+s) f d_P of the Hom differential. The degreewise maps
and their inverses therefore form a chain isomorphism. No flatness or boundedness
of Q is assumed, so this also applies to unbounded Q and the zero complex. -/
theorem perfectRingHom_tensorDual_iso {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hf : ∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    Nonempty (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _) ≅
      homComplex (R := CochainComplex.onePointRingSheaf A) P Q) := by sorry

end CategoryTheory
