/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Sheaf.CategoryTheory.GrothendieckAbelian.AcyclicQuotientComplexesBoundedSize
import Sheaf.CategoryTheory.BoundedSubobjectSize
import Sheaf.CategoryTheory.InjectiveIffExtendsSubobjectGenerator
import Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveCriterion
import Sheaf.CategoryTheory.GrothendieckAbelian.ObjectsSmall
import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Sheaf.CategoryTheory.PreaisleTransfiniteMonomorphismClosure

/-!
# Set-generated aisles of derived module sheaves

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XVII 5.2, abstract aisle input;
the agent-formulated auxiliary construction is recorded in the DAG proof
(blueprint: lem-per-set-generated-sheaf-aisle).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- A small set of derived module sheaves generates an aisle, with the stated orthogonal test.
Source: ILO, Travaux de Gabber, XVII 5.2, abstract set-generated-aisle input
(blueprint: lem-per-set-generated-sheaf-aisle).

The predicate `U` is specified by its universal intersection property, so this statement
uses no additional definition of a generated preaisle. `Small S` expresses that the
set of generators belongs to the fixed indexing universe. The second conjunct identifies
both halves of the t-structure; `ge 1` is the unshifted right orthogonal, so `ge 0`
is its image under the shift `[1]`.

Proof (the detailed cellular argument of the DAG):
1. By [lem-weil-pbc-ring-sheaves-grothendieck], $\mathcal A=\operatorname{Mod}(R)$ is Grothendieck
abelian, without requiring $R$ commutative. Choose a generator $U$. Use
[lem-kun-grothendieck-derived-coproducts] for the small coproducts in $D(\mathcal A)$; these are
the images of termwise coproducts. All sets, ordinals and Hom sets below are in the fixed indexing
universe. Choose a representing complex $P_G$ for each $G\in S$, possible because derived
localization has complexes as its objects [def-weil-abstract-derived-category].

2. Choose $\kappa$ from [lem-pur-kinjective-acyclic-quotient-complexes-bounded-size]. By
[lem-pur-kinjective-set-iso-classes-bounded-size], representatives of objects having
subobject-size at most $\kappa$ form a set. Integer-indexed choices of these representatives and
choices of their differentials form a set, since every Hom is a set. Taking those satisfying the
complex, bounded-above and acyclicity conditions gives a set $\mathcal M$ representing every
bounded-above acyclic complex with term sizes at most $\kappa$. The subobjects $N\subseteq U$
likewise form a set by [lem-pur-kinjective-set-of-subobjects]. For an object $V$ define $D^n(V)$
to have $V$ in degrees $n,n+1$, differential $1_V$, and zero elsewhere. Define a set $J$ of
monomorphisms of complexes consisting of $D^n(N)\hookrightarrow D^n(U)$ for all these $N,n$, and
$M\hookrightarrow\operatorname{Cone}(1_M)$ for $M\in\mathcal M$. The latter is the inclusion of
the unshifted summand under the cone convention [def-weil-abstract-derived-category]. Each
cokernel of a map in $J$ is acyclic: it is respectively the contractible disk $D^n(U/N)$, or
$M[1]$.

3. Suppose a complex $I$ has the extension property against $J$: every chain map from a domain in
$J$ to $I$ extends across its codomain. A chain map $D^n(V)\to I$ is uniquely a map $V\to I^n$,
with its degree $n+1$ component forced to be $d_I^n$ times that map. The disk tests therefore say
that every $N\to I^n$ extends to $U$. By [lem-pur-kinjective-characterize-injective], all $I^n$
are injective. The other tests make every map $M\to I$ extend over $\operatorname{Cone}(1_M)$,
hence nullhomotopic, because the identity cone is contractible (the off-diagonal identity gives
its contracting homotopy). Transporting across the chosen complex isomorphisms gives this for
every bounded-above acyclic complex of term size at most $\kappa$. Thus
[lem-pur-kinjective-characterize-K-injective], with both bounded-size hypotheses supplied by the
choice of $\kappa$, makes $I$ K-injective.

4. Enlarge $J$ to a set $I_S$ by adjoining $P_G[k]\hookrightarrow\operatorname{Cone}(1_{P_G[k]})$
for every $G\in S$ and integer $k\geq0$. All are monomorphisms. Choose an uncountable regular
cardinal $\mu$ greater than the subobject-size of every degree of every domain in $I_S$; there are
only a set of such degrees. For a continuous $\mu$-chain of monomorphisms of complexes,
[prop-pur-kinjective-objects-small] factors each component of a map from one of these domains
through a stage. The supremum of the countably many stages is below $\mu$; at a common stage the
components commute with the differentials because the maps from that stage to the colimit are
monic. The same monicity makes two chain maps equal at a common stage whenever they have equal
colimit images. Thus Hom from every domain preserves these chain colimits. Coproducts of
monomorphisms are monic: finite sums are exact, and the arbitrary sum is their filtered colimit,
exact by AB5. Pushouts preserve monomorphisms in an abelian category, and AB5 preserves
monomorphisms at limit stages. Consequently all $I_S$-cell chains meet this smallness hypothesis.

5. Represent the given $K$ by a complex $K_0$. Complexes have small colimits computed degreewise:
take the colimit of the terms and induce the differentials from their compatible structure maps,
obtaining $d^2=0$ and the colimit universal property degreewise. Hence
[lem-coef-small-object-cell-factorization] applies to $I_S$ with the regular cardinal just chosen.
Factor $K_0\to0$ as $K_0\hookrightarrow I\to0$, with the first map an $I_S$-cell map and the
second having right lifting against $I_S$. Write the cell chain as $(K_\beta)_{\beta\leq\theta}$,
starting at $K_0$ and ending at $I$. All its maps are degreewise monic by the preceding step. Its
successor cokernels are coproducts of the cokernels of the attached maps: pushout of a
monomorphism preserves its cokernel, and coproducts preserve cokernels by their universal
property. Thus they are coproducts of acyclic complexes and complexes $P_G[k+1]$, $k\geq0$.

6. Put $E_\beta=(K_\beta/K_0)[-1]$ as a complex. These form a continuous chain of monomorphisms
with $E_0=0$; quotient by the fixed subcomplex commutes with the limit colimits since cokernels
are colimits. Its successor quotients are the preceding successor cokernels shifted by $[-1]$.
Their derived images lie in $\mathcal U$: the shifted acyclic summands become zero, and
$Q(P_G[k+1][-1])\cong G[k]\in\mathcal U$. Termwise coproducts give derived coproducts by
[lem-kun-grothendieck-derived-coproducts]. Apply
[lem-per-preaisle-transfinite-monomorphism-closure] to this filtration and $\mathcal U$, which has
exactly its required zero, extension, positive-shift and coproduct closure. We get
$A:=Q((I/K_0)[-1])\in\mathcal U$. Applying the lemma to this shifted quotient filtration is
essential: it does not assume that $\mathcal U$ is closed under $[-1]$.

7. Right lifting of $I\to0$ against $J$ is exactly the extension property of Step 3, so $I$ is
K-injective. Right lifting against the additional identity-cone inclusions says every chain map
$P_G[k]\to I$ extends across its contractible identity cone, and is therefore nullhomotopic. By
[lem-weil-pbc-kinjective-hom-derived], the homotopy-to-derived Hom map with target $I$ is
bijective, with no boundedness hypothesis on $P_G[k]$. Thus $B:=QI$ satisfies
$\operatorname{Hom}(G[k],B)=0$ for all $G\in S$, $k\geq0$.

8. For any $B$ satisfying the generator vanishing, define $\mathcal
W_B=\{X:\operatorname{Hom}(X[k],B)=0\text{ for all }k\geq0\}$. It contains zero and $S$, is
strictly full, and is closed under $[1]$. It is closed under small coproducts since shifting
commutes with coproducts (the shift has its inverse as an adjoint) and Hom out of a coproduct is
the product of Hom sets. It is closed under summands by composing with the splitting maps. For a
distinguished $X\to Y\to Z\to X[1]$ with $X,Z\in\mathcal W_B$, any $Y[k]\to B$ restricts to zero
on $X[k]$, so factors through $Z[k]$ by [lem-weil-pbc-hom-out-of-triangle-exact], and is zero.
Therefore $\mathcal U\subseteq\mathcal W_B$ by the defining minimality of $\mathcal U$, and
$B\in\mathcal U^\perp$. Conversely, $G[k]\in\mathcal U$ for $G\in S$, $k\geq0$, so every
$B\in\mathcal U^\perp$ satisfies the generator vanishing. This proves the full stated generator
test and applies in particular to the $B$ constructed above.

9. The short exact sequence of complexes $0\to K_0\to I\to I/K_0\to0$ gives a quasi-isomorphism
$\operatorname{Cone}(K_0\to I)\to I/K_0$ by [lem-pc-cone-short-exact-quasi-iso]. The cone-triangle
convention of [def-weil-abstract-derived-category] and its inverse rotation therefore give a
distinguished triangle $A\to K\to B\to A[1]$, with the $A$ of Step 6 and the $B$ of Step 7. We
have proved $A\in\mathcal U$ and $B\in\mathcal U^\perp$. Finally $\mathcal U[1]\subseteq\mathcal
U$ by definition, and $\mathcal U^\perp[-1]\subseteq\mathcal U^\perp$ since
$\operatorname{Hom}(X,B[-1])\cong\operatorname{Hom}(X[1],B)=0$ for $X\in\mathcal U$. Hence
$\mathcal U^\perp\subseteq\mathcal U^\perp[1]$, the required lower-class shift condition.
Orthogonality is its defining vanishing, and the constructed triangle is the remaining axiom of
[def-weil-t-structure] for $(\mathcal U,\mathcal U^\perp[1])$. -/
theorem setGenerated_sheaf_aisle
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u}) [HasDerivedCategory.{u} (ringedSiteModules.{u} R)]
    (S : Set (DerivedCategory (ringedSiteModules.{u} R))) [Small.{u} S]
    (U : ObjectProperty (DerivedCategory (ringedSiteModules.{u} R)))
    (hU : ∀ X, U X ↔
      ∀ P : ObjectProperty (DerivedCategory (ringedSiteModules.{u} R)),
        P.IsClosedUnderIsomorphisms → P.ContainsZero → P.IsStableUnderRetracts →
        (∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I)) →
        (∀ Y, P Y → P (Y⟦(1 : ℤ)⟧)) → P.IsTriangulatedClosed₂ →
        (∀ G ∈ S, P G) → P X) :
    (∀ K, ∃ (A B : DerivedCategory (ringedSiteModules.{u} R))
      (f : A ⟶ K) (g : K ⟶ B) (h : B ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang _ ∧ U A ∧ U.rightOrthogonal B) ∧
    (∃ t : CategoryTheory.Triangulated.TStructure
      (DerivedCategory (ringedSiteModules.{u} R)), t.le 0 = U ∧ t.ge 1 = U.rightOrthogonal) ∧
    (∀ B, U.rightOrthogonal B ↔
      ∀ G ∈ S, ∀ k : ℤ, 0 ≤ k → ∀ f : G⟦k⟧ ⟶ B, f = 0) :=
  sorry

end DerivedCategory
