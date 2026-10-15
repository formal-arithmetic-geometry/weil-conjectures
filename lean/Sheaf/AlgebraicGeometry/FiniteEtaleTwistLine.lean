/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Finite torsion Tate twists are étale locally free lines

Source: Stacks Project, Étale Cohomology, Section 03PK; Groupoids, Example 040M;
Étale Cohomology, Lemma 03RV (blueprint: lem-asd-finite-etale-twist-line).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Nonnegative finite torsion Tate twists admit étale local bases of one element, are
locally constant, and tensoring with them is exact. The displayed local isomorphisms are
in the category of module-valued sheaves on the localized site, so they assert local
freeness of rank one including the module action. Preservation of finite limits and
colimits is exactness in this abelian category.

Source: Stacks, Section 03PK, Example 040M and Lemma 03RV
(blueprint: lem-asd-finite-etale-twist-line).

Proof:
1. Cover $T$ by affine opens $V=\operatorname{Spec}R$. The integer $N$ is a unit in $R$: its local
inverses exist by the local-ring hypothesis and agree on overlaps, so glue. Set $B=R[z]/(z^N-1)$
and $P=\operatorname{Spec}B$. Apply [lem-sbc-root-split-away-cover-etale] with $g=1,n=N$; its open
$D(1)$ is all of $P$, so $P\to V$ is etale. Put $\Delta=\prod_{0\le a<b<N}(z^a-z^b)$ and
$W=D(\Delta)\subset P$. For every point $t$ of $V$, choose an algebraic closure $\Omega$ of its
residue field. Since $N$ is a unit, its characteristic does not divide $N$. By
[lem-sc-primitive-root] choose a primitive $N$th root $\zeta\in\Omega$. The map $B\to\Omega$
sending $z$ to $\zeta$ defines a geometric point over $t$; its value on $\Delta$ is nonzero, so it
lies in $W$. Thus both $P\to V$ and $W\to V$ are surjective. The inclusions $W\to P$ and $V\to T$
are etale by [lem-weil-pbc-open-immersion-etale]. To see that $W\to V$ is etale using exactly the
covering-composition statement, compose the cover $\{P\to V\}$ with the cover $\{W\to
P,\operatorname{id}_P\}$; [lem-weil-pbc-etale-covering-composition] says each composite is etale.
Now compose the affine-open cover of $T$ with the surjective etale maps $W\to V$ by the same
lemma. These $W$ give an etale cover of $T$ with a unit $z$, $z^N=1$, and all differences
$z^a-z^b$ invertible. Uses: lem-sbc-root-split-away-cover-etale, lem-sc-primitive-root,
lem-weil-pbc-open-immersion-etale, lem-weil-pbc-etale-covering-composition.

2. On one $W$ write $r_j=z^j$ for $0\le j<N$. The constant-presheaf homomorphism $a\mapsto z^a$
extends to $\theta:(\mathbf Z/N)_W\to\mu_{N,W}$ by the defining universal property of the constant
sheaf [def-weil-pbc-constant-sheaf]. We verify it is an isomorphism directly, without assuming
that a set-sheaf trivialization preserves the group law. For any ring of sections over $W$, monic
division gives $X^N-1=\prod_j(X-r_j)$: after division by the first $k$ factors, evaluate at the
next $r_k$; the earlier differences are units, so the remaining quotient vanishes at $r_k$,
permitting the next division. After $N$ divisions the quotient is the constant $1$. The Lagrange
polynomials $L_j(X)=\prod_{k\ne j}(X-r_k)/\prod_{k\ne j}(r_j-r_k)$ satisfy $\sum_jL_j(X)=1$.
Indeed the difference has degree less than $N$ and vanishes at all $r_j$; the same successive
monic-division argument makes it zero. If $x^N=1$ is a section on an etale $U\to W$, set
$e_j=L_j(x)$. Then $\sum_j e_j=1$ and $e_j(x-r_j)=(x^N-1)/\prod_{k\ne j}(r_j-r_k)=0$. Hence the
opens $D(e_j)$ cover $U$, and on $D(e_j)$, $x=r_j$. Thus every root is locally a power of $z$. If
two constant residues $a\ne b$ give equal powers on a nonempty object, the unit $r_a-r_b$ vanishes
there, which is impossible. Locally represented sections of the constant sheaf therefore have
equal image only when they agree locally. The local inverses just constructed are unique on
overlaps and glue by the sheaf axiom; they give an inverse of $\theta$. Finally $z^{a+b}=z^az^b$
and $(z^a)^b=z^{ab}$ show that $\theta$ is an isomorphism of $(\mathbf Z/N)_W$-module sheaves.
Uses: def-weil-pbc-constant-sheaf.

3. Restriction to an etale object is localization of [def-weil-pbc-etale-site]: for an object
$U\to W$, its coverings and their intersections are exactly its coverings and intersections on
$T$. Local section representatives and their local equality relations in sheafification are
consequently identical on these two sites. In particular, sheafifying the constant presheaf
[def-weil-pbc-constant-sheaf] gives $A_T|_W=A_W$ and $(\mathbf Z/N)_T|_W=(\mathbf Z/N)_W$;
sheafifying the section tensor presheaf gives the restricted tensor product. By
[def-pur-sheaf-tensor-product], tensoring the module isomorphism of step 2 with $A_W$ therefore
identifies $A_T(1)|_W$ with $(\mathbf Z/N)_W\otimes_{(\mathbf Z/N)_W}A_W$. The multiplication map
$b\otimes a\mapsto ba$ has inverse $a\mapsto1\otimes a$; the balancing relation gives $b\otimes
a=1\otimes ba$. These are mutually inverse sheaf morphisms, so $A_T(1)|_W\cong A_W$. The scalar
map $\mathbf Z/N\to A$ exists precisely because $NA=0$. No freeness or flatness of $A$ over
$\mathbf Z/N$ is needed. Uses: def-pur-sheaf-tensor-product, def-weil-pbc-etale-site,
def-weil-pbc-constant-sheaf.

4. The same covering works for every tensor power. For $r=0$ use the identity $A_T(0)|_W=A_W$. For
$r=1$ use step 3. If $A_T(r)|_W\cong A_W$, the recursive tensor-power definition
[def-pur-sheaf-tensor-product] and multiplication $A_W\otimes_{A_W}A_W\cong A_W$ identify
$A_T(r+1)|_W$ with $A_W$. This proves the induction for all $r\ge0$. The resulting cover is a
trivialising datum in [def-constructible-locally-constant], so each twist is locally constant. On
every $W$ its single generator is a basis over $A_W$, exactly the local-freeness-of-rank-one
assertion. Uses: def-pur-sheaf-tensor-product, def-constructible-locally-constant.

5. Fix $r$ and put $L=A_T(r)$. By [lem-weil-pbc-etale-cover-geometric-point-lift], every geometric
point has a lift to one member $W$ of the cover in step 1. The stalk definition
[def-weil-pbc-geometric-stalks] gives the same stalk on $T$ and on the localized site at this
pointed $W$: replace any pointed neighbourhood $U$ by $U\times_TW$ with its specified pair of
lifts, a pointed refinement, and do the same for equalities of germs. These fibre products exist
in [def-weil-pbc-etale-site]. Thus the local basis of step 4 and
[lem-weil-pbc-constant-sheaf-geometric-stalk] give $L_{\bar t}\cong A$, as $A$-modules since the
germ comparison respects multiplication. By [def-weil-sheaf-of-modules-category], the forgetful
functor from module sheaves to abelian sheaves is exact. For any short exact sequence $0\to F'\to
F\to F''\to0$ of $A_T$-module sheaves, [prop-weil-pbc-geometric-stalks-exact] gives a short exact
sequence of underlying abelian stalks, with $A$-linear maps. By the natural tensor-stalk
isomorphism in clause (1) of [lem-pod-etale-stalk-tensor-scalar], the stalk sequence after
tensoring with $L$ identifies with the original sequence tensor $A$, hence with the original
sequence via $m\otimes a\mapsto am$. Here the tensor over the constant ring sheaf agrees with the
sheafification of tensors over $A$: locally each coefficient section is constant, so the balancing
relations for a section of $A_T$ are locally exactly those for elements of $A$. Thus the cited
comparison applies to precisely the tensor of the statement. Exact stalks imply exactness of the
tensor sequence: its kernel at the first term, middle homology, and cokernel at the last term have
zero stalks by exactness of the stalk functor; apply [lemma-weil-pbc-geometric-stalk-conservative]
to their maps to the zero sheaf. They vanish. Tensoring with $L$ preserves short exact sequences,
and hence exact sequences by factoring through images. This is the claimed flatness. Uses:
prop-weil-pbc-geometric-stalks-exact, lem-pod-etale-stalk-tensor-scalar,
lemma-weil-pbc-geometric-stalk-conservative, lem-weil-pbc-etale-cover-geometric-point-lift,
lem-weil-pbc-constant-sheaf-geometric-stalk, def-weil-pbc-geometric-stalks,
def-weil-pbc-etale-site, def-weil-sheaf-of-modules-category. -/
theorem finite_etale_torsion_twist_line
    (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hInvertible : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) (r : ℕ) :
    (∃ cover : Cover.{u} etalePrecoverage T, ∀ i : cover.I₀,
      Nonempty
        ((finiteEtaleTateTwist T N A hA r).over (cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    IsLocallyConstantSheaf (finiteEtaleTateTwist T N A hA r) ∧
    PreservesFiniteLimits
      (@MonoidalCategory.tensorLeft _ _
        (Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (finiteEtaleTateTwist T N A hA r)) ∧
    PreservesFiniteColimits
      (@MonoidalCategory.tensorLeft _ _
        (Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (finiteEtaleTateTwist T N A hA r)) := by
  sorry

end AlgebraicGeometry.Scheme
