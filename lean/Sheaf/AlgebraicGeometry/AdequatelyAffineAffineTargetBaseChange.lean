module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Sheaf.AlgebraicGeometry.StackQcqsMorphism
import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Adequate affineness after stack base change over an affine scheme

Source: Alper, *Adequate moduli spaces and geometrically reductive group schemes*,
arXiv:1005.2398v3, Proposition 4.2.1(6), affine-target specialization
(blueprint: lem-sfb-adequately-affine-affine-target-base-change).

The algebraicity proofs required by the adequate-affineness predicate are bound
existentially together with that predicate. In particular, algebraicity of the
2-fibre product is part of the assertion, never an additional hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- Adequate affineness over an affine scheme survives arbitrary stack base change.
Neither the base-changing map nor the absolute diagonals have extra hypotheses.
Source: Alper, arXiv:1005.2398v3, Proposition 4.2.1(6)
(blueprint: lem-sfb-adequately-affine-affine-target-base-change).

Proof:
1. The actual product P = U ×_T V is algebraic by
   lem-sfb-algebraic-stack-fibre-products. Reassociating triples identifies
   P ×_V W with U ×_T W, with their projections and restricted algebras.
2. Quasi-compactness and quasi-separatedness of f pass to the projection:
   apply the tests of def-sfb-stack-qcqs-morphism after this reassociation;
   its relative diagonal is a base change of the relative diagonal of f.
3. Take any surjection A → B of quasi-coherent algebras on P, a smooth scheme
   W → V, and a section t of B over P ×_V W. Cover W by affine opens W_i.
   Restriction is precomposition in def-sfb-stack-quasi-coherent-algebra:
   it preserves the structure action, local presentations and local lifts.
   Thus A_i → B_i remains a surjection of quasi-coherent algebras.
4. Write T = Spec R and W_i = Spec S_i. The projection
   q_i : U ×_T W_i → U is affine by lem-sfb-stack-affine-algebra-direct-image.
   Push A_i → B_i forward along q_i. That lemma preserves surjections and
   identifies global section rings naturally, compatibly with powers.
   Apply lem-sfb-affine-target-adequacy-criterion to f to lift a positive
   power of t|W_i, and transfer the lift back along these ring isomorphisms.
5. The affine open cover is étale and jointly surjective. The lifts of step 4
   are exactly universal adequacy on each smooth test in
   def-sfb-adequately-affine-morphism. Combine with step 2. No flatness,
   representability of h, or absolute-diagonal condition was used. -/
theorem adequatelyAffine_affineTarget_baseChange {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [IsAffine T.left]
    {U : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {V : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    (hU : IsAlgebraicModuliStack U) (hV : IsAlgebraicModuliStack V)
    (f : BasedFunctor U (discreteModuli (yoneda.obj T)))
    (h : BasedFunctor V (discreteModuli (yoneda.obj T)))
    (hf : ∃ hT : IsAlgebraicModuliStack (discreteModuli (yoneda.obj T)),
      IsAdequatelyAffineMorphism f hU hT) :
    ∃ hP : IsAlgebraicModuliStack (moduliTwoFiberProduct f h),
      IsAdequatelyAffineMorphism (moduliTwoFiberSnd f h) hP hV := by
  sorry

end CategoryTheory
