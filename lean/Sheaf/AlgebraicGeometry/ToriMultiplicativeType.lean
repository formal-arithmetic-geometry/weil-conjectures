module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Tori and groups of multiplicative type

Source: Milne, Algebraic Groups (2017), Definitions 12.14 and 12.17, and Notation 12.29,
printed pp.236, 241 (blueprint: def-sfb-tori-multiplicative-type).

The split torus is an actual finite product of the recorded multiplicative group.
Scalar extension uses the finite-product-preserving pullback functor on group objects.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry
namespace MultiplicativeType

/-- Scalar extension of group schemes, with the pulled-back group law.
Source: Milne, Section 12(g), pp.239--240
(blueprint: def-sfb-tori-multiplicative-type). -/
noncomputable def baseChange {k K : Type u} [Field k] [Field K] [Algebra k K] :
    Grp (Over (Spec (.of k))) ⥤ Grp (Over (Spec (.of K))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp

/-- The rank-n split torus, including the trivial group in rank zero.
Source: Milne, Definition 12.14, p.236
(blueprint: def-sfb-tori-multiplicative-type). -/
noncomputable def splitTorus (k : Type u) [Field k] : ℕ → Grp (Over (Spec (.of k)))
  | 0 => 𝟙_ _
  | n + 1 => Grp.mk (StandardGroupSchemes.multiplicative k) ⊗ splitTorus k n

/-- A torus becomes a finite product of G_m over the algebraic closure.
Source: Milne, Definition 12.14, p.236
(blueprint: def-sfb-tori-multiplicative-type). -/
def IsTorus {k : Type u} [Field k] (G : Grp (Over (Spec (.of k)))) : Prop :=
  ∃ n : ℕ, Nonempty ((baseChange (K := AlgebraicClosure k)).obj G ≅
    splitTorus (AlgebraicClosure k) n)

/-- Multiplicative type means a closed subgroup of a split torus over the algebraic closure.
Source: Milne, Theorem 12.9(c) and Definition 12.17, pp.233, 236
(blueprint: def-sfb-tori-multiplicative-type). -/
def IsMultiplicativeType {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) : Prop :=
  ∃ (n : ℕ) (i : (baseChange (K := AlgebraicClosure k)).obj G ⟶
    splitTorus (AlgebraicClosure k) n), IsClosedSubgroupScheme i.hom.hom

/-- A largest subtorus is a closed torus through which every closed torus inclusion factors.
The factorization is in group schemes and commutes with the inclusions into G.
Source: Milne, Notation 12.29, p.241
(blueprint: def-sfb-tori-multiplicative-type). -/
def IsLargestSubtorus {k : Type u} [Field k] {T G : Grp (Over (Spec (.of k)))}
    (i : T ⟶ G) : Prop :=
  IsClosedSubgroupScheme i.hom.hom ∧ IsTorus T ∧
    ∀ (S : Grp (Over (Spec (.of k)))) (j : S ⟶ G),
      IsClosedSubgroupScheme j.hom.hom → IsTorus S →
        ∃ f : S ⟶ T, f ≫ i = j

end MultiplicativeType
end AlgebraicGeometry
