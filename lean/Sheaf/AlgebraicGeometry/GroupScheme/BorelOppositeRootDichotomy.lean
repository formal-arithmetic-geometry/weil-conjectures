module

public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Mathlib.Order.SupIndep
public import Mathlib.Data.Set.Card
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.TorusCentralizerBorelIntersection
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-! # Opposite character roots in a Borel Lie algebra

Source: Milne, Algebraic Groups (2017), Lemma 21.28, p.433; Theorem 21.11(b),(c),
pp.428--429; proof of Proposition 21.29, p.434
(blueprint: lem-sfb-borel-opposite-root-dichotomy).

The images of the tangent maps identify Lie(T) and Lie(B) inside Lie(G).
The direct sum is expressed by independence of the family indexed by `Option Ψ_B`
and equality with its supremum. Inversion of actual characters expresses negation
in the character lattice, including in characteristic two.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.RankOneRoots

/-- A Borel through a maximal torus selects precisely one root in each opposite pair.
Source: Milne, Lemma 21.28, Theorem 21.11(b),(c), and Proposition 21.29, pp.428--434
(blueprint: lem-sfb-borel-opposite-root-dichotomy).

Proof plan:
1. Apply lem-sfb-reductive-rank-one-reflections. Its character weight decomposition
   is finite, has zero weight Lie(T), and each root space has dimension one.
   The only rational multiples of a root among roots are that root and its inverse.
2. For a root α let S be the largest subtorus of ker α and H = C_G(S).
   The rank-one theorem makes H reductive of semisimple rank one. Apply
   lem-sfb-torus-centralizer-borel-intersection: D = B ×_G H is a Borel of H
   containing T, with all intersections taken scheme-theoretically.
3. By lem-sfb-split-rank-one-classification, H is a central split-torus factor
   times SL2, PGL2 or GL2. Its matrix factor acts on the projective line, proper
   by lemma-nagata-projective-space-base-change-proper. By
   lem-sfb-solvable-proper-fixed-point, D fixes a line. Since T is contained in D,
   the line is a coordinate line. Thus D lies in an upper or lower triangular
   stabilizer. Each stabilizer is smooth connected solvable, so Borel maximality
   makes D equal to it. In SL2 choose s with s² ≠ 1; such s exists also in
   characteristic two over the algebraically closed field.
4. The off-diagonal tangent characters are ±2χ for SL2, ±χ for PGL2 and
   ±(e₁-e₂) for GL2. In PGL2 they survive in gl2/FI in every characteristic.
   Write α = ma with primitive a and extend a to an integral character basis,
   using lem-sfb-multiplicative-character-antiduality. Characters trivial on S
   are exactly the integral multiples of a. Dual-number points identify Lie(H)
   with the S-fixed tangent subspace, hence with Lie(T) ⊕ g_α ⊕ g_(-α).
   Tangents commute with B ×_G H, and each triangular model contains exactly
   one off-diagonal direction. Hence precisely one opposite root space lies in Lie(B).
5. Lie(B) is T-stable and contains Lie(T). Comparing the independent Laurent
   monomials in the coaction shows that every weight component of a vector in
   Lie(B) is in Lie(B). Each intersection with a root space is zero or the whole
   one-dimensional space, giving the asserted direct sum. Characters form a
   torsion-free integral lattice, so α and -α are distinct even in characteristic
   two. The previous step therefore gives cardinality one. If there are no roots,
   the decomposition reduces to Lie(B) = Lie(T). -/
theorem borel_opposite_root_dichotomy
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F))))
    (iT : T ⟶ G) (iB : B ⟶ G) (j : T ⟶ B)
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hB : IsBorelGroupScheme iB.hom.hom) (hj : j ≫ iB = iT) :
    ∃ a : ModObj T.X G.X,
      a.smul = adjointMap iT ∧
      (roots T G a).Finite ∧
      (∀ α ∈ roots T G a, ∃ β ∈ roots T G a, β.hom.hom = α.hom.hom⁻¹) ∧
      iSupIndep (fun k : Option {χ : Character T //
          χ ∈ roots T G a ∧
            weight T G a χ ≤ (GrpObj.differential iB.hom.hom).toLinearMap.range} ↦
        k.elim (GrpObj.differential iT.hom.hom).toLinearMap.range
          (fun χ ↦ weight T G a χ.val)) ∧
      (GrpObj.differential iB.hom.hom).toLinearMap.range =
        (GrpObj.differential iT.hom.hom).toLinearMap.range ⊔
          ⨆ χ : {χ : Character T // χ ∈ roots T G a ∧
            weight T G a χ ≤ (GrpObj.differential iB.hom.hom).toLinearMap.range},
            weight T G a χ.val ∧
      ∀ α ∈ roots T G a,
        Set.ncard {χ : Character T | χ ∈ roots T G a ∧
          weight T G a χ ≤ (GrpObj.differential iB.hom.hom).toLinearMap.range ∧
          (χ = α ∨ χ.hom.hom = α.hom.hom⁻¹)} = 1 := by
  sorry

end AlgebraicGeometry.RankOneRoots
