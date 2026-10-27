module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # The kernel alternative for a split torus endomorphism

Source: Milne, Algebraic Groups (2017), Theorem 12.9(b), pp.233--234,
Remark 12.5, p.232, and the proof of Theorem 17.48, p.367
(blueprint: lem-sfb-torus-endomorphism-kernel-dichotomy).

The second alternative is a closed subgroup of the actual scheme-theoretic kernel.
The exclusive disjunction includes both existence of an alternative and incompatibility.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Exactly one of faithful flatness with finite presentation and a positive-rank
closed split subtorus in the kernel holds for a torus endomorphism.
Source: Milne, Theorem 12.9(b), pp.233--234, Remark 12.5, p.232,
and the proof of Theorem 17.48, p.367
(blueprint: lem-sfb-torus-endomorphism-kernel-dichotomy).

Proof plan:
1. Choose a split presentation T = D(L), L = Z^r. By
   lem-sfb-split-torus-hom-matrices and lem-sfb-multiplicative-character-antiduality,
   f is contravariantly an endomorphism u of L. Its coordinate map sends e_m
   to e_{u(m)}. Apply lem-sfb-pid-submodule-smith-bases to u(L) inside L,
   obtaining generators a_i b_i for i <= n, with every a_i nonzero. The rational
   image of u is exactly the span of b_1,...,b_n.
2. If n = r, lem-sfb-finite-linear-injective-surjective makes u rationally
   injective, hence integrally injective, so f's coordinate map is injective.
   The affine-source separatedness lemma makes T separated. By
   lem-sfb-algebraic-group-homomorphism-factorization, f factors as a faithfully
   flat finitely presented map q followed by a closed immersion j. The closed
   image is affine (def-weil-closed-immersion). Its surjective coordinate map
   is injective because its composite is f's injective coordinate map. Thus
   it is an isomorphism, whose inverse gives j's inverse by
   def-weil-affine-spectrum. Consequently f has all five properties in (i).
3. If n < r, project L onto Z^(r-n) by killing b_1,...,b_n. This surjection p
   satisfies pu = 0. By lem-sfb-multiplicative-character-antiduality and
   lem-sfb-diagonalizable-group-geometric-criteria, D(p) is a closed inclusion
   of a rank-(r-n) split torus into T. Contravariance makes its composite with
   f trivial. The kernel pullback therefore gives the required closed subgroup
   of GrpObj.ker f, with positive rank.
4. For exclusivity, flatness and surjectivity give a faithfully flat coordinate
   map by lem-weil-pbc-flat-morphism-affine-criterion and
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat. By
   lem-weil-pbc-faithfully-flat-universally-injective it is injective, forcing
   u injective. Clear denominators and apply the equal-dimension theorem to
   see that u is rationally surjective. A positive-rank closed kernel torus
   would give a surjective character map v : L -> Z^s with vu = 0. For each x,
   rational surjectivity gives u(y) = d*x with d > 0. Then d*v(x) = 0,
   whence v(x) = 0 by torsion-freeness, contradicting surjectivity onto Z^s.
   Rank zero uses the empty bases in step 2. In characteristic p the map [p]
   still has an injective lattice map, so inseparable isogenies are included. -/
theorem torusEndomorphism_kernel_dichotomy
    {F : Type u} [Field F] [IsAlgClosed F]
    (T : Grp (Over (Spec (.of F))))
    (hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)) (f : T ⟶ T) :
    Xor
      (Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
        LocallyOfFinitePresentation f.hom.hom.left ∧ QuasiCompact f.hom.hom.left ∧
        QuasiSeparated f.hom.hom.left)
      (∃ (s : ℕ) (i : (MultiplicativeType.splitTorus F s).X ⟶ GrpObj.ker f.hom.hom),
        1 ≤ s ∧ IsClosedSubgroupScheme i) := by
  sorry

end AlgebraicGeometry
