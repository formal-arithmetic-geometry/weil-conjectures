module

public import Sheaf.RingTheory.CompletionFiniteExtensionTensorMap
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

universe u v
namespace AdicCompletion

/-- The explicitly constructed completed tensor map is bijective.
Source: Stacks Project, Algebra, Lemma 10.97.8 (Tag 07N9), first equality, using
Lemma 10.97.1 (Tag 00MA), part (3).
(blueprint: new-completion-finite-extension-tensor-bijective)

Proof: Put A = R_p, m = pA, C = the m-adic completion of A, and B = A tensor_R S.
Localization preserves Noetherianity, so A is Noetherian. Base change of a finite
module is finite, so B is finite over A. The finite-module completion theorem
(`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`) identifies
C tensor_A B with the m-adic module completion of B (first shrink the finite
A-module B into the universe of A if needed by the Mathlib theorem). Tensor associativity and
C tensor_A A = C identify C tensor_A (A tensor_R S) with C tensor_R S.
For every n, the submodule m^n B is the underlying A-submodule of the ideal J^n,
since m = pA and J = pB = mB, and extension of ideals commutes with powers.
Thus the identity on B induces compatible bijections between the quotients
B/(m^n B) and B/J^n. Their inverse limits give a bijection from the m-adic module
completion of B to the J-adic ring completion of B. The composite of these three
bijections is the map in the conclusion: on a pure tensor c tensor s, its nth
coordinate is the image of c_n multiplied by the image of 1 tensor s in B/J^n,
which is exactly the quotient-level construction of completionFiniteExtensionTensorMap.
Pure tensors generate the tensor product additively, so the maps agree everywhere.
The displayed map is therefore bijective. -/
theorem completion_finite_extension_tensor_bijective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    Function.Bijective (completionFiniteExtensionTensorMap R S p) := by sorry

end AdicCompletion
