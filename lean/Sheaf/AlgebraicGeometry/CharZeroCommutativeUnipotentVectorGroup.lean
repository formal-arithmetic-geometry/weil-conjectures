module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace

/-!
# Commutative unipotent groups in characteristic zero are vector groups

Source: Milne, Algebraic Groups (2017), Proposition 14.32 and Corollary 14.33,
printed p.289 (blueprint: lem-sfb-char-zero-commutative-unipotent-vector-group).

The unitriangular embedding is expressed as a closed group-scheme embedding in
GL_n whose matrices have diagonal entries one and entries below the diagonal zero,
over every test algebra. The conclusion uses the categorical finite product of
the recorded additive group scheme, including its empty product.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth connected commutative affine group of finite type over a characteristic-zero
field, admitting a closed unitriangular embedding, is a finite power of the additive group.
Source: Milne, Algebraic Groups (2017), Proposition 14.32 and Corollary 14.33, printed p.289
(blueprint: lem-sfb-char-zero-commutative-unipotent-vector-group).

Proof:
1. For every group V satisfying the hypotheses, use
`lem-sfb-unipotent-exponential-construction` to construct exp from its finite-dimensional
identity tangent space. Prove exp is an isomorphism by strong induction on tangent dimension.
2. Intersect V with the coordinate filtration of its unitriangular ambient group
(`lem-sfb-unitriangular-coordinate-filtration`). The last nontrivial intersection H maps
to Ga with trivial scheme-theoretic kernel. Factor through its faithfully flat image I
(`lem-sfb-affine-homomorphism-flat-image`). Injectivity on all algebra points makes the
coordinate-ring map an epimorphism. A faithfully flat ring epimorphism is an isomorphism
(`lem-sfb-faithfully-flat-ring-epimorphism-isomorphism`), so H is isomorphic to I.
3. If I is proper, its monic additive defining polynomial P has positive degree a
(`lem-sfb-additive-subgroup-polynomial-quotient`). For a > 1 the coefficient of X^(a-1)Y
in P(X+Y) is a, whereas in P(X)+P(Y) it is zero. Characteristic zero forces a = 1,
then P(T) = T and I is trivial, a contradiction. Thus H is Ga. Call it N; it is central.
The exponential of Ga is the identity, since its standard tangent matrices square to zero.
Naturality identifies the exponential of N with Ga -> N and gives tangent dimension one.
4. The identity rational point makes V geometrically connected
(`lem-sbc-connected-rational-point-geometrically-connected`). The quotient Q = V/N is
smooth affine, finite type and geometrically connected; its quotient map q is fppf with
kernel N and the standard torsor square (`lem-sfb-affine-normal-quotient-geometry`).
Commutativity descends along q. The N-torsor q is smooth because N is smooth
(`lem-sfb-smooth-affine-group-torsor-representability`).
5. After algebraic closure, the unipotent normal quotient image lemma gives unipotence of Q.
Field-extension detection in `lem-sfb-unipotent-to-multiplicative-trivial` descends this to k.
The trivial-kernel representation of `lem-sfb-normal-subgroup-representation-kernel` has
unipotent geometric matrices by `lem-sfb-rational-representation-unipotent-point`.
Then `lem-sfb-geometric-unipotence-unitriangular-embedding` gives the required embedding of Q.
6. The tangent kernel sequence for N -> V -> Q is exact. The kernel assertion follows
from the fibre square defining N. Surjectivity follows by lifting a dual-number point
through the smooth map q with its given identity lift on the closed point. Hence Q has
tangent dimension one less; this also excludes a nontrivial V of tangent dimension zero.
Choose a linear section s of dq, giving a direct-sum decomposition after every scalar change.
7. By induction exp_Q is an isomorphism. Naturality gives q exp_V = exp_Q dq and
exp_V di = i exp_N. In R[epsilon,eta]/(epsilon^2,eta^2), the commutator of
1+epsilon X and 1+eta Y is 1+epsilon eta (XY-YX). Commutativity forces XY = YX.
The commuting-vector exponential identity therefore makes exp_V additive.
8. For v in V(R), set y = exp_Q^(-1)(q(v)), t = exp_V(s(y)), and
z = exp_N^(-1)(t^(-1)v), which exists uniquely in the closed kernel N(R).
The formula v -> s(y)+di(z) is a scheme morphism, by the kernel fibre square.
The preceding identities show both composites with exp_V are identities, on all R-points.
This proves exp_V is a group-scheme isomorphism and completes the induction.
9. Choose a basis of the tangent space of G, of size d. Its coordinate isomorphism
identifies the additive tangent scheme with Ga^d. Compose with exp_G. For d = 0 the
induction gives the trivial group, so the empty-product conclusion is included. -/
theorem charZero_commutative_unipotent_vectorGroup {k : Type u} [Field k] [CharZero k]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsCommMonObj G.X]
    (hunitriangular : ∃ (n : ℕ), 0 < n ∧
      ∃ r : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
        IsClosedSubgroupScheme r ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R]
          (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ G.X),
          (∀ i : Fin n,
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
              ⟨i⟩ ⟨i⟩ = 1) ∧
          (∀ i j : Fin n, j < i →
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
              ⟨i⟩ ⟨j⟩ = 0)) :
    ∃ d : ℕ, Nonempty ((∏ᶜ (fun _ : Fin d ↦ Grp.mk (StandardGroupSchemes.additive k))) ≅ G) := by
  sorry

end AlgebraicGeometry
