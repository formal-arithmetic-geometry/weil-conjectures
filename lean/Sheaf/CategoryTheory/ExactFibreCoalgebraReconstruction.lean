module

public import Sheaf.CategoryTheory.FibreCoefficientQuotient
public import Sheaf.RingTheory.FiniteRightComodule
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Coalgebra reconstruction from an exact faithful fibre functor

Source: Milne, Algebraic Groups (2017), Theorems 9.32 and 9.37, pp.175–178;
9.41–9.43, pp.179–181, with the explicit coefficient quotient presentation.
(blueprint: lem-sfb-exact-fibre-coalgebra-reconstruction)

A chosen small skeletal equivalence is supplied explicitly. It witnesses essential smallness
and records all representative transports. The field, the original category's objects and
morphisms have independent universes. The skeleton and fibre spaces lie in the fixed containing
universe max u w, so the coefficient quotient and its finite comodules do too.
-/

set_option autoImplicit false

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CategoryTheory.FibreReconstruction

/-- Reconstruction on the specified quotient, with both coefficient formulas and the coactions
for every finite basis, including the empty basis.

Source: Milne, Algebraic Groups (2017), Theorems 9.32 and 9.37, pp.175–178;
9.41–9.43, pp.179–181.
(blueprint: lem-sfb-exact-fibre-coalgebra-reconstruction)

Proof:
1. On the small skeleton let C_X consist of subquotients of finite sums of X. It is abelian:
kernels are subobjects, cokernels are quotients, and finite sums and iterated subquotients stay
in C_X. Faithful exact F detects zero objects and isomorphisms, and embeds Hom spaces into
finite-dimensional linear-map spaces.
2. Apply lem-sfb-single-generator-fibre-representability to obtain (P,p) representing F on C_X.
A finite spanning family in F(Y) gives an epimorphism from a finite sum of copies of P to Y,
because its cokernel has zero fibre. Thus P is a projective generator, also in dimension zero.
3. Under representability, natural endomorphisms of F are precompositions with End(P), so
E_X = End(F|C_X) is End(P) opposite, and evaluation at p identifies E_X with F(P).
Apply lem-sfb-finite-projective-generator-module-equivalence to get the equivalence with
finite-dimensional left E_X-modules.
4. The identity tensor of a finite vector space is basis independent. By
lem-sfb-finite-free-tensor-dual, this proves basis independence of Delta and epsilon. Expand
F(f) in bases of its source and target: the quotient relation in each tensor factor makes
Delta respect naturality, and both counits evaluate to psi(F(f)v). Both iterated Delta maps
give the same double sum, and both counit laws follow from the dual basis identity.
The identical construction on C_X gives B_X. The tensor universal property is that of
def-weil-pbc-module-tensor-product; bases exist by lem-weil-pbc-vector-space-free.
5. The same identity tensor gives basis-independent rho. Its counit is the dual basis
expansion of v, and coassociativity follows from Delta's formula. The coefficient relation
gives rho_W F(f) = (F(f) tensor 1) rho_V, defining K and the corresponding K_X.
6. Map B_X to E_X dual by c_V(phi,v)(a) = phi(a_V v). Naturality makes this well defined.
Represent v as F(h_v)p. Then c_V(phi,v) = c_P(phi F(h_v),p). This reduces the map to the
dual of evaluation E_X to F(P), hence proves it invertible. Pairing the comultiplication
with a tensor b gives phi(a_V b_V v); the counit is evaluation at 1. Thus this is a
coalgebra isomorphism compatible with the action/coaction dictionary of
lem-sfb-finite-algebra-comodule-duality.
7. The module equivalence of step 3 and this dictionary identify K_X with an equivalence
onto finite-dimensional right B_X-comodules, on the stated underlying spaces and maps.
8. The preorder C_X contained in C_Y is nonempty and directed, using 0 and X plus Y.
Every coefficient occurs in C_V and every relation in C_(V plus W), so B is the vector-space
colimit of B_X, by def-weil-pbc-category-colimit. No injectivity of transitions is asserted.
9. By lem-sfb-directed-coalgebra-comodule-descent a B-colinear map between F(V) and F(W)
becomes B_Y-colinear at a sufficiently large stage. Fullness of K_Y supplies a morphism
V to W, uniquely by faithfulness. Thus K is fully faithful.
10. The object-descent clause of that lemma brings every finite B-comodule to a B_X-comodule
on its same space. Essential surjectivity of K_X then gives essential surjectivity of K.
The composite forgetful functor equals F by construction. Representative isomorphisms give
the coefficientAt transport, and naturality gives the same displayed formulas there.
For the zero category B is zero; counitality forces every right zero-comodule to be zero.
-/
theorem exact_fibre_coalgebra_reconstruction
    {k : Type u} [Field k] {A : Type v} [Category.{t} A] [Abelian A] [Linear k A]
    (F : A ⥤ ModuleCat.{max u w} k) [F.Additive] [F.Linear k] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hfd : ∀ V : A, FiniteDimensional k (F.obj V))
    (S : Type (max u w)) [SmallCategory S] (hS : Skeletal S) (e : S ≌ A) :
    ∃ d : Coalgebra k (CoefficientQuotient (e.functor ⋙ F)),
      (∀ (V : S) (φ : Module.Dual k (F.obj (e.functor.obj V)))
        (v : F.obj (e.functor.obj V)) (n : ℕ)
        (b : Module.Basis (Fin n) k (F.obj (e.functor.obj V))),
        d.comul (coefficient (e.functor ⋙ F) V φ v) =
          ∑ i : Fin n, coefficient (e.functor ⋙ F) V φ (b i) ⊗ₜ[k]
            coefficient (e.functor ⋙ F) V (b.coord i) v) ∧
      (∀ (V : S) (φ : Module.Dual k (F.obj (e.functor.obj V)))
        (v : F.obj (e.functor.obj V)),
        d.counit (coefficient (e.functor ⋙ F) V φ v) = φ v) ∧
      ∃ E : A ≌ Coalgebra.FiniteRightComodule d,
        ∃ h : E.functor ⋙ Coalgebra.finiteRightComoduleForget d = F,
          ∀ (V : A) (n : ℕ) (b : Module.Basis (Fin n) k (F.obj V))
            (x : (E.functor.obj V).obj.V),
            ((eqToHom (congrArg (fun G : A ⥤ ModuleCat.{max u w} k ↦ G.obj V) h)).hom.rTensor
                (CoefficientQuotient (e.functor ⋙ F))) ((E.functor.obj V).obj.str.hom x) =
              ∑ i : Fin n, b i ⊗ₜ[k] coefficientAt F e V (b.coord i)
                ((eqToHom (congrArg (fun G : A ⥤ ModuleCat.{max u w} k ↦ G.obj V) h)) x) := by
  sorry

end CategoryTheory.FibreReconstruction
