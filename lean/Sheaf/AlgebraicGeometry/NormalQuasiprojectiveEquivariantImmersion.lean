/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.StandardLinearProjectiveAction
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.RelativelyVeryAmple
import Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple
import Sheaf.AlgebraicGeometry.NormalLineBundlePowerLinearization
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import Sheaf.RingTheory.FiniteSubcomodule
import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry

/-! # Equivariant projective immersions of normal quasi-projective schemes

Source: Sumihiro, Equivariant completion (1974), Theorem 1 and Lemma 8 (WANTED);
Brion, Algebraic group actions on normal varieties, Corollary 2.14 and Section 2.5;
the accepted DAG's finite-disjoint-union extension.
(blueprint: lem-sfb-normal-quasiprojective-equivariant-immersion).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

/-- A normal quasi-projective scheme with an action of a smooth connected affine group
admits an equivariant immersion into the projective space of a nonzero representation.
The representation is written in a basis as k^(n+1). This loses no existential case:
every nonzero finite-dimensional vector space has such a basis. Projective space here
parametrizes lines, and the standard action uses the matrix itself, not inverse transpose.
Source: Sumihiro, Equivariant completion (1974), Theorem 1 and Lemma 8 (WANTED);
Brion, Algebraic group actions on normal varieties, Corollary 2.14 and Section 2.5;
finite-disjoint-union extension and six-step construction in the accepted DAG.
(blueprint: lem-sfb-normal-quasiprojective-equivariant-immersion).

Proof (accepted DAG, with dependency ids retained):
1. If $X=\varnothing$, take $V=k$, the trivial homomorphism, and the unique map to $\mathbf
P^0_k$. The empty subscheme is open, hence this is an immersion, and both equivariance composites
are the unique map from the empty scheme. Assume henceforth $X\ne\varnothing$. Choose the
immersion $i:X\to\mathbf P^n_k$ in the hypothesis and put $A=i^*\mathcal O(1)$. By [def-trf-
relatively-very-ample] this is relatively very ample over $k$. Apply the equivalence of [lem-trf-
relative-ample-very-ample], with exponent $1$, to conclude that $A$ is ample. Its finite-type
hypothesis is precisely the hypothesis on $X\to\operatorname{Spec}k$; its quasi-compact base
hypothesis holds for the one-point affine base. Over that base relative ampleness is absolute
ampleness by the definition in that cited statement.
Uses: def-trf-relatively-very-ample, lem-trf-relative-ample-very-ample.
2. Apply [lem-sfb-normal-line-bundle-power-linearization] to $A$, obtaining $m\geq1$ and a
linearization of $L=A^{\otimes m}$. The group is smooth, affine, connected and finite type, the
field is algebraically closed, and $X$ is normal, separated and finite type, exactly as required;
integrality of $X$ is not required. By [lem-sc-ample-positive-tensor-power], $L$ is still ample.
By [lem-weil-pbc-ample-very-ample-immersion-affine-base], choose $d\geq1$ and an immersion
$u:X\to\mathbf P^r_k$ with $B:=L^{\otimes d}\cong u^*\mathcal O(1)$. The base is affine and the
structure morphism is finite type, hence locally finite type. The tensor power of the
linearization of $L$ gives a linearization of $B$: tensor its structure isomorphism $d$ times.
Its identity and cocycle follow by tensoring the identity and cocycle of $L$. By the
identification of $(\operatorname{Proj}k[x_0,\ldots,x_r],\mathcal O(1))$ with the projective
bundle of $\mathcal O^{\oplus(r+1)}$ and its canonical twist in [lem-trf-projective-bundle-
quotient-geometry], $u$ exhibits $B$ as relatively very ample over $\operatorname{Spec}k$ in the
sense of [def-trf-relatively-very-ample]. Thus $B$ is a linearized relatively very ample line
bundle.
Uses: lem-sfb-normal-line-bundle-power-linearization, lem-sc-ample-positive-tensor-power, lem-
weil-pbc-ample-very-ample-immersion-affine-base, def-trf-relatively-very-ample, lem-trf-
projective-bundle-quotient-geometry.
3. Apply [lem-sfb-very-ample-affine-finite-sections] to $B$ over $\operatorname{Spec}k$. Obtain
finitely many generating sections $s_0,\ldots,s_N$ whose morphism $j_0:X\to\mathbf P^N_k$ is an
immersion. Apply [lem-sfb-linearized-qcoherent-cohomology-coaction] in degree zero to the same
linearized $B$. Its hypotheses hold because $X$ is quasi-compact and separated and an invertible
module is quasi-coherent. We get a $k[G]$-coaction on $H=\Gamma(X,B)$; after every commutative
$k$-algebra extension $R$, its section action satisfies $(g
s)(y)=\theta_{g,g^{-1}y}(s(g^{-1}y))$. The base-change comparison and this formula are clauses of
the cited statement, so no finite-dimensionality or properness of $H$ or $X$ is being assumed.
Uses: lem-sfb-very-ample-affine-finite-sections, lem-sfb-linearized-qcoherent-cohomology-
coaction.
4. The Hopf maps of $k[G]$ satisfy the coalgebra identities by [lem-sfb-affine-group-coordinate-
hopf]. Apply [lem-sfb-comodule-finite-subcomodule] to the finite subset
$\{s_0,\ldots,s_N\}\subset H$. It yields a finite-dimensional subcomodule $E\subset H$ containing
these sections. By [lem-sfb-rational-representation-comodule-dictionary], $E$ carries a rational
representation $r:G\to\operatorname{GL}(E)$ and its inclusion into $H$ intertwines all algebra-
valued actions. Since $X$ is nonempty and the $s_i$ generate an invertible module, at least one
$s_i$ is nonzero, so $E\ne0$. Put $V=E^\vee$. For every algebra $R$, define the dual action by
$r_R^\vee(g)(\lambda)=\lambda\circ r_R(g^{-1})$. In bases this is inverse transpose, with inverse
$r_R^\vee(g^{-1})$, and the equality $r_R(gh)=r_R(g)r_R(h)$ gives the group law after reversing
the order twice. These matrices commute with algebra homomorphisms. The finite-dimensional clause
of the dictionary therefore gives a group-scheme homomorphism $\rho:G\to\operatorname{GL}(V)$.
Uses: lem-sfb-affine-group-coordinate-hopf, lem-sfb-comodule-finite-subcomodule, lem-sfb-
rational-representation-comodule-dictionary.
5. The evaluation $q:E\otimes_k\mathcal O_X\to B$ is surjective because it contains the
generating sections $s_i$. The quotient classification [lem-trf-projective-bundle-quotient-
geometry] gives a morphism $j:X\to\mathbf P(V)$, with the convention that $\mathbf P(V)$
parametrizes lines in $V=E^\vee$, equivalently invertible quotients of $E$. Let $E_0\subset E$ be
the span of the $s_i$. In $\mathbf P(V)$ let $U$ be the open where the restriction of the
tautological quotient to $E_0$ is surjective. In bases it is the union of the standard opens on
which at least one of the $s_i$-coordinates is nonzero. Restricting that quotient to the ordered
family $(s_i)$ defines a morphism $p:U\to\mathbf P^N_k$ by the same quotient classification. The
image of $j$ lies in $U$, since the $s_i$ generate $B$, and $p\circ j=j_0$ by uniqueness for the
quotient $(B,(s_i))$. Apply [lem-zl-immersion-cancellation] to conclude that $j:X\to U$ is an
immersion. Its factorization as a closed immersion into an open of $U$ is also a factorization
into an open of $\mathbf P(V)$, so $j$ is the desired immersion into $\mathbf P(V)$.
Uses: lem-trf-projective-bundle-quotient-geometry, lem-zl-immersion-cancellation.
6. It remains to check equivariance as morphisms. The section formula from [lem-sfb-linearized-
qcoherent-cohomology-coaction], applied to $g$ and $gx$, says $(r_R(g)e)(gx)=\theta_{g,x}(e(x))$
for every commutative $k$-algebra $R$, every $g\in G(R)$, every $x\in X(R)$, and $e\in E_R$. This
denotes equality of the pulled-back sheaf maps; the coaction inclusion identifies $r_R$ with the
action on sections. Equivalently the evaluation quotient at $gx$ is isomorphic, by
$\theta_{g,x}^{-1}$, to $q_x\circ r_R(g)^{-1}$. Acting by $\rho_R(g)$ on a line in $E_R^\vee$
transforms its quotient precisely to $q_x\circ r_R(g)^{-1}$, by the definition of inverse
transpose. By the natural quotient bijection of [lem-trf-projective-bundle-quotient-geometry],
the two composites from $G\times_kX$ to $\mathbf P(V)$ therefore agree on every affine test
scheme. In particular this equality can be applied to the universal pair on each affine open of
$G\times_kX$, giving equality of the morphisms there, hence globally. This proves the asserted
identity and all its base changes, including nonreduced ones.
Uses: lem-sfb-linearized-qcoherent-cohomology-coaction, lem-trf-projective-bundle-quotient-
geometry.
-/
theorem exists_normal_quasiprojective_equivariant_immersion
    (k : Type u) [Field k] [IsAlgClosed k]
    (G X : Over (Spec (.of k))) [GrpObj G] [ModObj G X]
    [Smooth G.hom] [IsAffine G.left] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (hnormal : ∀ x : X.left,
      IsDomain (X.left.presheaf.stalk x) ∧ IsIntegrallyClosed (X.left.presheaf.stalk x))
    (hquasiprojective : ∃ (N : ℕ)
      (i : X ⟶ Over.mk (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (N + 1))) k)),
      IsImmersion i.left) :
    ∃ (n : ℕ) (ρ : G ⟶ GeneralLinearGroup (ULift.{u} (Fin (n + 1))) k)
      (a : ModObj (GeneralLinearGroup (ULift.{u} (Fin (n + 1))) k)
        (Over.mk (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) k)))
      (j : X ⟶ Over.mk (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) k)),
      IsMonHom ρ ∧ StandardLinearProjectiveAction.IsStandard k (ULift.{u} (Fin (n + 1))) a ∧
        IsImmersion j.left ∧
        ModObj.smul (M := G) (X := X) ≫ j = (ρ ▷ X) ≫
          (GeneralLinearGroup (ULift.{u} (Fin (n + 1))) k ◁ j) ≫ a.smul ∧
        (IsEmpty X.left → n = 0 ∧
          ρ = CategoryTheory.CartesianMonoidalCategory.toUnit G ≫ MonObj.one) := by
  sorry

end AlgebraicGeometry
