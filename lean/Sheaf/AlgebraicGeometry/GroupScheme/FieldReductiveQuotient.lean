module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomRationalPoints
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.SmoothAmbientNormalityGeometric
import Sheaf.AlgebraicGeometry.GroupScheme.ConnectedNormalSubgroupReductive
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Faithfully flat quotients of reductive groups over an algebraically closed field

Source: Conrad, Reductive group schemes, Section 1.1, printed pp.10--11,
Definition 1.1.11 and the adjacent discussion of images and nonsmooth kernels
(blueprint: lem-sfb-field-reductive-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A faithfully flat homomorphism between smooth connected affine finite type groups
preserves reductivity. There is no hypothesis on the scheme-theoretic kernel.
Source: Conrad, Reductive group schemes, Section 1.1, printed pp.10--11,
Definition 1.1.11 and the discussion of images, including nonsmooth kernels
(blueprint: lem-sfb-field-reductive-quotient).

Proof:
1. For a smooth connected normal unipotent closed subgroup U of J, form
   P = H ×_J U (def-pc-fibre-product). Its inclusion in H is closed by
   lem-weil-pbc-closed-immersion-base-change, so it is affine of finite type
   (def-weil-closed-immersion). On every algebra it is the inverse image of U,
   hence a normal subgroup (def-sc-group-scheme-subgroup). Faithful flatness and
   lem-sfb-affine-group-homomorphism-image make H(k) -> J(k) surjective; lifting
   a point of U(k) gives a point of P(k). Thus P(k) -> U(k) is surjective.
2. Put C = P⁰ and M = C_red. The node
   lem-sfb-locally-algebraic-group-identity-component makes M smooth, connected,
   integral and finite type, with the same underlying space as C. The successive
   closed inclusions make M affine and closed in H (def-weil-closed-immersion).
   Conjugation by H(k) preserves P, its identity component, and its nilradical,
   hence M scheme-theoretically. Apply lem-sfb-smooth-ambient-normality-geometric
   with k as its own algebraic closure to make M normal on all test algebras.
3. By lem-sfb-connected-normal-subgroup-reductive, M is reductive. Restrict
   P -> U to f : M -> U. Use lem-sfb-geometric-unipotence-unitriangular-embedding
   to embed U in a unitriangular group. Each maximal torus T of M is split,
   hence diagonalizable; lem-sfb-diagonalizable-to-unipotent-trivial gives f|_T = 1
   as a group-scheme homomorphism.
4. The closed kernel K of f (lem-sc-kernel-subgroup) contains every maximal torus.
   Each such torus is its own centralizer by lem-sfb-reductive-torus-self-centralizer.
   The algebraically closed field k is infinite: otherwise 1 + ∏ a∈k, (X-a)
   would be a nonconstant polynomial without a root. Apply
   lem-sfb-cartan-subgroups-generate to obtain K = M, so f is trivial on all algebras.
5. By lem-sfb-group-neutral-component-translates, P has finitely many components,
   each a rational translate of C. Every k-point of C factors through its reduction,
   so C(k) = M(k). Since f is trivial, P(k) -> U(k) is constant on every component.
   It is surjective by step 1, so U(k) is finite, even when P is nonreduced.
6. Smoothness gives reducedness (sbc-lem-smooth-geometrically-reduced,
   def-pc-reduced-scheme). The identity-component result and connectedness make U
   integral. For a ∈ k[U], the function ∏ s∈U(k), (a-a(s)) vanishes at every k-point,
   hence is zero by lem-wf-affine-nullstellensatz-vanishing. In a domain a factor
   must vanish, so every a is scalar. The identity point splits k -> k[U], giving
   k[U] = k and U = 1. This proves reductivity. The recorded predicate uses the
   canonical algebraic closure of k; since k is already algebraically closed,
   its structure embedding is an isomorphism, so scalar transport gives exactly
   the same connectedness and trivial-subgroup condition. -/
theorem isReductive_of_faithfullyFlat
    {k : Type u} [Field k] [IsAlgClosed k]
    (H J : Grp (Over (Spec (.of k))))
    [Smooth H.X.hom] [ConnectedSpace H.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [Smooth J.X.hom] [ConnectedSpace J.X.left] [IsAffine J.X.left]
    [LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom]
    (q : H ⟶ J) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hH : ReductiveTorusCentralizer.IsReductive H) :
    ReductiveTorusCentralizer.IsReductive J := by
  sorry

end AlgebraicGeometry
