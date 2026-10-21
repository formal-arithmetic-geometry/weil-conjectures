/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement
public import Sheaf.Paper.PrimeFieldTensorDevissage
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions

/-!
# Tensor devissage in the constructible category of a directed partition

Source: ILO, Travaux de Gabber, Expose XVII, Proposition 7.4.6 and Lemma 7.4.7,
pp. 307--308 (blueprint: lem-per-directed-galois-tensor-filtration-closure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.GaloisPartition

/-- A single finite prime-field family generates the constructible category by finite
extensions of constructible tensor retracts. This is a statement in the ambient abelian
category, before choosing representatives for subobjects or normalizing zero filtrations.

Source: ILO XVII, Proposition 7.4.6, proved using Lemma 7.4.7, pp. 307--308
(blueprint: lem-per-directed-galois-tensor-filtration-closure).

Proof: For every stratum S with its connected Galois cover V, put K = Aut_S(V).
There are finitely many simple F_l[K]-modules: every simple is a quotient of the finite
regular module by a maximal left ideal. Descend these representatives to local systems
on S and extend them to X by the open-then-closed extension associated to the directed
ordering. These are constructible members of the fixed partition class; collect them
in a finite list C. The list depends only on the partition and l. On a stratum, monodromy
identifies a finite-type member of the weak class with a finitely generated module that
is unipotent for the kernel of pi_1(S) -> K. Its finite unipotent filtration has finite
quotients on which that kernel acts trivially. Apply the finite-algebra external tensor
filtration with B = F_l[K] to each such quotient. Exact additive descent transports the
filtration and retractions, and its mixed tensor comparison identifies the factors with
N_S tensor a simple descended prime-field local system. Open extension and closed direct
image are exact. Their stalk formulas, together with the tensor stalk formula, identify
extension of these mixed tensors with N_X tensor C. All factors are constructible and in
the fixed class. Finally the directed open/closed exact sequences give a finite filtration
of the original object by its stratum extensions. Refine it by the filtrations just
constructed. Closure under extensions is exactly membership in filtrationClosure.
Zero objects belong to the closure without any factor. The zero coefficient ring gives
only zero objects, so requires no simple coefficient-algebra modules. -/
theorem exists_tensor_filtrationClosure (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsNoetherian X] [Nonempty X]
    (P : GaloisPartition X) (hP : P.IsDirected) :
    ∃ (r : ℕ)
      (C : Fin r → Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))),
      (∀ a, P.constructible (ULift.{u + 1} (ZMod ℓ)) (C a)) ∧
      ∀ (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
        [Algebra (ULift.{u + 1} (ZMod ℓ)) A],
        P.constructible A ≤ ObjectProperty.filtrationClosure (fun Q ↦ P.constructible A Q ∧
          ∃ (a : Fin r) (N : ModuleCat.{u + 1} A), Module.Finite A N ∧
            ∃ (ι : Q ⟶ (Etale.primeFieldTensorSheaf X ℓ A N).obj (C a))
              (π : (Etale.primeFieldTensorSheaf X ℓ A N).obj (C a) ⟶ Q),
              ι ≫ π = 𝟙 Q) := by
  sorry

end AlgebraicGeometry.Scheme.GaloisPartition
