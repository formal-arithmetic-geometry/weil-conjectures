/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
import Sheaf.Algebra.Homology.PerfectRingDualTermFlat

/-! # Invertibility of normalized evaluation

Source: Stacks Project, More on Algebra, Tags 0A6A and 0ATK.
(blueprint: lem-pc-perfect-ring-hom-tensor-degree-isiso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

/-- A normalized evaluation map is invertible for a bounded finite-projective source.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1).
(blueprint: lem-pc-perfect-ring-hom-tensor-degree-isiso)

Proof: evaluation at the unique object identifies sheaves on the bottom-topology
one-object site with A-modules, identifies sheafification with the identity, and
reflects isomorphisms. Project the dual degree r to Hom(P^(-r),A[0]^0), then identify
A[0]^0 with A. All other product factors are zero, so this projection is invertible.
For each r+s=n, the diagonal block in the normalization is therefore the map
from the dual of P^(-r) tensor Q^s to Hom(P^(-r),Q^s), multiplied by (-1)^(r*s).
The first map is invertible by Mathlib dualTensorHomEquiv for the finite projective
module P^(-r); the scalar is a unit, since its square is one. The normalization
identifies this block on pure tensors, which generate the module tensor; all other
blocks vanish by its first clause. The bound on P restricts the nonzero Hom factors
to a finite interval, and also restricts the nonzero dual factors to its negative.
Remove the zero factors, reindex r+s=n by p=-r, and identify the resulting finite
coproduct and product with the same finite biproduct. The map is then diagonal with
invertible blocks; assemble their inverses to obtain a two-sided inverse. Empty
support yields zero objects and the same inverse equations. No bound on Q is used,
and rank-zero modules and the zero ring are covered by the same argument. -/
theorem perfectRingHom_tensorDual_degree_isIso {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hf : ∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∀ f : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n,
      PerfectRingHomTensorDegreeCondition P Q n f → IsIso f := by sorry

end CategoryTheory
