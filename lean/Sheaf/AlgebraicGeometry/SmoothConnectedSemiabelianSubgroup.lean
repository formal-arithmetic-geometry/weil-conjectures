module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus

/-! # Smooth connected closed subgroups of semiabelian groups

Source: Conrad, Semistable Reduction for Abelian Varieties, Corollaries 3.2 and 3.3,
printed p.8 (blueprint: lem-sfb-smooth-connected-semiabelian-subgroup).

The conclusion uses the shared split torus, the actual kernel square, and local
surjectivity on the big fppf site. In particular, rank zero is included.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A smooth connected closed subgroup of a semiabelian group over an algebraically
closed field is an extension of an abelian variety by a split torus.

Source: Conrad, Corollaries 3.2 and 3.3, printed p.8; the structural ingredients are
Milne, Algebraic Groups (2017), Theorem 8.27, Proposition 8.1(b), Example 8.4 and
Definition 12.14 (blueprint: lem-sfb-smooth-connected-semiabelian-subgroup).

Proof:
1. Apply def-sfb-semiabelian-geometric-fibres to the identity geometric point.
Identify its identity base change with G by the pullback universal property, obtaining
an abelian quotient v : G → A₀ with split torus kernel u : T₀ → G.
2. By lem-weil-pbc-proper-fp-permanence, j is proper, hence separated and finite type.
Its composition with G's structure map is separated; finite type follows from
lem-sfb-finite-type-composition-base-change. Apply lem-sfb-barsotti-chevalley-decomposition
to B, obtaining a smooth connected affine kernel a : L → B of finite type and an abelian
quotient p : B → C which is fppf-locally surjective.
3. By lem-sfb-affine-to-abelian-hom-vanishing, the composite L → B → G → A₀ is zero.
The kernel universal property gives h : L → T₀ with h ≫ u = a ≫ j. Cancel the
monomorphism u to verify compatibility with multiplication, so h is a homomorphism.
4. The square exhibiting h as the pullback of a ≫ j along u is Cartesian: any compatible
pair (l,t) has t = h(l), since u is a monomorphism. The two closed-immersion lemmas
lem-weil-pbc-closed-immersion-comp and lem-weil-pbc-closed-immersion-base-change imply
that h is a closed immersion. By lem-sfb-multiplicative-type-largest-subtorus, L is a
torus. Over the algebraically closed field it admits an isomorphism b from a split torus.
5. Take A = C, q = p, and i = b ≫ a. The kernel square transports along b, and local
surjectivity of p gives that of q. When L is trivial choose rank zero; this also handles
the trivial subgroup B. -/
theorem smooth_connected_semiabelian_subgroup
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSemiabelianGeometricFibres G)
    (B : Grp (Over (Spec (.of k)))) (j : B ⟶ G)
    [IsClosedSubgroupScheme j.hom.hom]
    [Smooth B.X.hom] [ConnectedSpace B.X.left] :
    ∃ (r : ℕ) (A : Grp (Over (Spec (.of k))))
      (i : MultiplicativeType.splitTorus k r ⟶ B) (q : B ⟶ A),
      IsAbelianVariety A.X ∧
      IsPullback i.hom.hom (toUnit (MultiplicativeType.splitTorus k r).X)
        q.hom.hom η[A.X] ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
        (yoneda.map q.hom.hom) := by
  sorry

end AlgebraicGeometry
