module

public import Sheaf.AlgebraicGeometry.SemiabelianGroupSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Sheaf.AlgebraicGeometry.AbelianVariety.HomFiniteFree
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Finite free Hom groups of semiabelian algebraic spaces

Source: Milne, Abelian Varieties, I Theorem 10.15, pp.49–50; Milne, Algebraic Groups,
Theorem 12.9, pp.233–234 and Section 8(e), p.151; Deligne, Le lemme de Gabber,
proof of Lemma 3.5.1, pp.139–140
(blueprint: lem-sfb-semiabelian-hom-finite-free).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The group of homomorphisms of semiabelian group algebraic spaces has a finite integer
basis. A homomorphism is a natural transformation of the functors of points preserving the
given group laws, i.e. a morphism of the additive point functors; its pointwise addition is the
preadditive structure on abelian-group-valued presheaves. The endomorphism ring has the same
addition, composition as multiplication, and the identity natural transformation as its unit.

Source: Milne, Abelian Varieties, I Theorem 10.15, pp.49–50; Milne, Algebraic Groups,
Theorem 12.9, pp.233–234 and Section 8(e), p.151; Deligne, Le lemme de Gabber,
proof of Lemma 3.5.1, pp.139–140
(blueprint: lem-sfb-semiabelian-hom-finite-free).

Proof plan:
1. Write the two exact fppf extensions as T_G -> G -> A_G and T_H -> H -> A_H.
   By lem-sfb-torus-abelian-hom-vanishing, q_H f i_G is zero. The kernel property
   induces f_T : T_G -> T_H. Lift a section of A_G fppf locally to G and apply q_H f.
   Lifts differ by T_G, so their images agree and glue uniquely to f_A : A_G -> A_H.
   Naturality and additivity follow from uniqueness. Yoneda identifies maps between
   the represented torus and abelian sheaves with their group-scheme maps. This gives
   an additive map Phi : Hom(G,H) -> Hom(T_G,T_H) direct-sum Hom(A_G,A_H).
2. If Phi(f)=0, then q_H f=0, so f factors through T_H. Its restriction to T_G is
   zero. The same local lifting and gluing descends this factor to A_G -> T_H, which
   vanishes by lem-sfb-torus-abelian-hom-vanishing. Thus f=0. Applying this to a
   difference shows Phi is injective. No representability theorem for G or H is needed.
3. By lem-sfb-split-torus-hom-matrices and lem-sfb-abelian-hom-finite-free, both
   summands have finite integer bases. Their direct sum is a finite power of Z.
   Identify Hom(G,H) with its image and apply
   lem-weil-subgroup-finite-free-abelian-group-free to obtain the asserted basis.
4. Take H=G. The category laws give associative composition and identity id_G.
   Both distributive laws follow pointwise because all components are additive maps.
   The standard preadditive endomorphism ring is therefore the required ring, with
   its finite basis from step 3. This includes the trivial group and its zero ring. -/
theorem semiabelian_hom_finite_free {k : Type u} [Field k] [IsAlgClosed k]
    (G H : SemiabelianGroupSpace k) :
    (∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ (G.additivePoints ⟶ H.additivePoints))) ∧
      (∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ (End G.additivePoints))) ∧
      (∀ f g : End G.additivePoints, f * g = g ≫ f) ∧
      (1 : End G.additivePoints) = 𝟙 G.additivePoints := by
  sorry

end AlgebraicGeometry
