module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Coefficient endomorphisms preserve independence in a direct sum

Source: agent algebraic refinement supporting Milne, Algebraic Groups (2017),
Proposition 14.50, printed p.296; this refinement is not stated in Milne
(blueprint: lem-sfb-coefficient-endomorphism-preserves-independence).

The coefficientwise map is Mathlib's `Finsupp.mapRange`; no surjectivity is assumed.
-/

@[expose] public section

universe u v

namespace Finsupp

/-- An injective field endomorphism applied to every coefficient preserves independence
of a finite family in a direct sum. Source: agent algebraic refinement supporting Milne,
Algebraic Groups (2017), Proposition 14.50, printed p.296; not a statement in Milne
(blueprint: lem-sfb-coefficient-endomorphism-preserves-independence).

Proof plan:
1. Let S be the finite union of the supports of the vectors. Restriction to S preserves
   independence, since a relation extends by zero to all coordinates. Since sigma preserves
   zero, the transformed vectors also vanish outside S.
2. The image K of sigma is a subfield of k: ring-homomorphism laws give the ring operations,
   and sigma(a) inverse is sigma(a inverse). Regard the transformed restrictions as vectors
   over K. Lift each coefficient of a K-relation through sigma; injectivity of sigma turns
   this into a relation between the original restrictions. Their independence makes every
   lifted coefficient, and hence every coefficient of the K-relation, zero.
3. Enumerate S by Fin n and apply lem-weil-linear-independence-field-extension, recorded
   as `linearIndependent_algebraMap_comp_iff`, to K contained in k. The transformed
   restrictions are therefore independent over k.
4. Restrict any k-relation between the transformed vectors to S and use step 3 to make
   every coefficient zero. No arbitrary coefficient of k is lifted through sigma.
   If m = 0 the conclusion is vacuous. If S or I is empty, independence of the original
   family forces m = 0: otherwise the coefficient 1 at one index gives a nonzero relation.
-/
theorem linearIndependent_mapRange_ringHom
    {k : Type u} [Field k] (σ : k →+* k) (hσ : Function.Injective σ)
    {I : Type v} (m : ℕ) (w : Fin m → I →₀ k) (hw : LinearIndependent k w) :
    LinearIndependent k (fun j : Fin m => Finsupp.mapRange σ σ.map_zero (w j)) := by
  sorry

end Finsupp
