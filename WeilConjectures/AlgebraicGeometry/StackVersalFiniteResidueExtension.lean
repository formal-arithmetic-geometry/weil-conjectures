/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StackVersalRing
public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import WeilConjectures.RingTheory.AdicSmoothFixedResidueLifting
import WeilConjectures.AlgebraicGeometry.AffineClosedPinchingPushout

/-! # Versal rings after finite residue-field extension

Source: Stacks Project, Tags 0DQY, 0DQF and 07WX
(blueprint: lem-sfb-stack-versal-finite-residue-extension).

The marked formal-object and versality definitions are publicly imported from
StackVersalRing, their definition-node module. All objects and arrows retain their
existing names and types. Levels are indexed by n : Nat and mean C / m^(n+1).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.StackVersal

variable {R : Type u} [CommRing R]
variable {k : Type u} [Field k] [Algebra R k]

/-- Extension of a versal ring along any specified finite extension of residue fields.
The arrow xlToX specifies the induced point, with its actual pullback identification.
No compatibility of the new formal object with the old one is asserted by the source.
Source: Stacks, Tags 0DQY, 0DQF and 07WX
(blueprint: lem-sfb-stack-versal-finite-residue-extension).

1. Choose finitely many $k$-algebra generators $a_1,\ldots,a_s$ of $l$: a finite $k$-basis is
such a generating family, since every element is already a $k$-linear combination. Evaluation
gives a surjection $e:P=C[Y_1,\ldots,Y_s]\twoheadrightarrow l$, using $C\twoheadrightarrow
k\hookrightarrow l$ on coefficients [def-weil-pbc-mv-polynomial-ring]. Put $\mathfrak q=\ker(e)$
and $D=\varprojlim_{n\geq1}P/\mathfrak q^n$. Apply [lem-sfb-artin-completed-polynomial-test-
ring] with its base ring $C$, its residue field $l$, and its number $d$ of additional zero-
valued variables equal to zero. It makes $D$ complete Noetherian local, with maximal ideal
$\mathfrak qD$ and residue field canonically $l$, and makes every $B_n=D/\mathfrak m_D^n$
Artinian local with residue $l$. The structure map $j:C\to D$ induces the specified
$k\hookrightarrow l$; its inverse image of $\mathfrak m_D$ is $\mathfrak m_C$, so it is local.
Thus $D$ is a complete Noetherian local $R$-algebra.

2. The lifting clause of [lem-sfb-artin-completed-polynomial-test-ring], again with base $C$ and
residue field $l$, says that every local residue-preserving $C$-map $D\to B$ lifts through every
surjection $B'\twoheadrightarrow B$ of Artinian local $C$-algebras with residue field $l$. Apply
[lem-sfb-adic-smooth-fixed-residue-lifting] with its base ring $C$, its finite residue extension
$l/(C/\mathfrak m_C)=l/k$, and its complete local algebra $D$. Its hypotheses hold by step 1 and
the hypotheses on $C$. This proves that $j:C\to D$ is formally smooth for the $\mathfrak
m_D$-adic topology, in the precise unrestricted square-zero lifting sense required by the item.

3. For any Artinian local $R$-algebra $B$ with residue map $B\twoheadrightarrow l$, put
$A_B=B\times_l k$. By [lem-sfb-artinian-finite-residue-restriction], $A_B$ is Artinian local
with residue $k$, its projection to $B$ is injective, and $B'\twoheadrightarrow B$ induces a
surjection $A_{B'}\twoheadrightarrow A_B$. The construction respects the $R$-structures. Since
$k$ and $l$ are finite over $R/\mathfrak m_R$, each is generated as an $R$-algebra by a finite
vector-space basis. Hence [lem-sfb-artinian-finite-type-residue-criterion] makes
$\operatorname{Spec}A_B$ and $\operatorname{Spec}B$ finite type over $\operatorname{Spec}R$, as
are $\operatorname{Spec}k$ and $\operatorname{Spec}l$. Finally [lem-weil-pbc-artinian-local-
noetherian-nilpotent] makes $\ker(B\to l)=\mathfrak m_B$ nilpotent. These assertions verify all
the Artinian, finite-type, and nilpotence hypotheses needed in the next step.

4. Apply [lem-sfb-affine-closed-pinching-pushout] to $B\twoheadrightarrow l\leftarrow k$. It
identifies $\operatorname{Spec}A_B$ with the scheme pushout
$\operatorname{Spec}k\amalg_{\operatorname{Spec}l}\operatorname{Spec}B$. Here
$\operatorname{Spec}l\to\operatorname{Spec}B$ is the nilpotent closed immersion just checked.
Apply [lem-sfb-algebraic-stack-rim-schlessinger] over the Noetherian base ring $R$ to obtain the
restriction equivalence $$\mathcal X(A_B)\simeq\mathcal X(k)\times_{\mathcal X(l)}\mathcal
X(B).$$ The right side retains the specified isomorphism over $l$. All four schemes satisfy its
finite-type hypothesis by step 3; the item supplies exactly its algebraic-stack hypothesis.

5. Fixing the object $x$ and its marking in the equivalence of step 4 gives an equivalence
$E_B:\mathcal F_x(A_B)\simeq\mathcal F_{x_l}(B)$: send $(w,\alpha)$ to its restriction to $B$,
marked by $\alpha|_l$. Explicitly, a marked object $z$ over $B$ supplies the triple
$(x,z,z|_l\cong x_l)$ and therefore lifts by essential surjectivity in step 4. An arrow between
two images, compatible with their markings, pairs with the identity of $x$ to give an arrow of
triples, and thus lifts uniquely by full faithfulness in step 4. This proves full faithfulness
on marked groupoids as well. Restriction along $B\to B'$ commutes with $E$ up to the canonical
pullback comparisons: both composites restrict the same object along $A_B\to B'$. These
comparisons inherit their coherence from the given pullback functors.

6. Let $(\eta_r)_{r\geq1}$ be the given marked formal object over $C$. For $B_n$ from step 1 put
$A_n=A_{B_n}$. The composite $C\xrightarrow{j}D\to B_n$ has residue image in $k\subset l$, hence
factors uniquely through the subring $A_n=B_n\times_l k$. The resulting map $u_n:C\to A_n$ is
local and residue-preserving. By [lem-weil-pbc-artinian-local-noetherian-nilpotent], $\mathfrak
m_{A_n}^{r_n}=0$ for some $r_n$, so $u_n$ kills $\mathfrak m_C^{r_n}$. Pull back $\eta_{r_n}$ to
$A_n$ and apply $E_{B_n}$ to obtain $\theta_n\in\mathcal F_{x_l}(B_n)$. For $B_{n+1}\to B_n$,
the maps from $C$ to $A_n$ agree. Choose a common larger exponent for the two factorizations
through quotients of $C$; the given transition isomorphisms of $\eta$ identify the two
restrictions. They satisfy the cocycle identities because those of $\eta$ do, and the pullback
comparisons in step 5 are coherent. Thus $(\theta_n)$ is a marked formal object over $D$. In
particular, for any local residue-preserving $b:D\to B$, its pullback $\theta_b$ is canonically
$E_B(\eta_{u_b})$, where $u_b:C\to A_B$ is the factorization of $bj$.

7. We verify versality, retaining the prescribed isomorphism. Take $p:B'\twoheadrightarrow B$, a
local residue-preserving $b:D\to B$, $\zeta'\in\mathcal F_{x_l}(B')$, and an isomorphism
$\gamma:\zeta'|_B\xrightarrow{\sim}\theta_b$. By essential surjectivity of $E_{B'}$ choose
$w'\in\mathcal F_x(A_{B'})$ and an isomorphism $\delta:E_{B'}(w')\xrightarrow{\sim}\zeta'$. By
the naturality and full faithfulness in step 5, the composite $\gamma\circ\delta|_B$ has a
unique preimage $$\beta:w'|_{A_B}\xrightarrow{\sim}\eta_{u_b}.$$ Step 3 makes
$A_{B'}\twoheadrightarrow A_B$ a surjection of the test algebras for $x$. Apply the assumed
versality of $C$ to $u_b,w',\beta$. It supplies a local residue-preserving $u':C\to A_{B'}$
lifting $u_b$ and an isomorphism $\varepsilon:w'\xrightarrow{\sim}\eta_{u'}$ restricting to
$\beta$.

8. Give $B'$ its $C$-algebra structure by $C\xrightarrow{u'}A_{B'}\to B'$ and give $B$ the
compatible one $C\xrightarrow{u_b}A_B\to B$. Both have the specified $C$-algebra residue field
$l$; the latter structure is $bj$, so $b:D\to B$ is a $C$-map for these structures. Apply the
lifting clause of [lem-sfb-artin-completed-polynomial-test-ring] with base $C$ to lift $b$ to a
local residue-preserving $C$-map $b':D\to B'$. Its composite with $j$ is the map just prescribed
by $u'$, so the unique factorization $C\to A_{B'}$ associated to $b'$ is precisely $u'$.
Consequently $E_{B'}(\varepsilon)\circ\delta^{-1}$ identifies $\zeta'$ with $\theta_{b'}$. Its
restriction is $(\gamma\circ\delta|_B)\circ(\delta|_B)^{-1}=\gamma$, by the choice of $\beta$
and the restriction condition on $\varepsilon$. This is exactly the versality lifting property,
including the prescribed isomorphism. Take $C_l=D$ with $(\theta_n)$ and $C\to C_l=j$. Step 1
gives its complete local Noetherian and residue-field clauses, and step 2 gives adic formal
smoothness.
-/
theorem exists_versal_finite_residue_extension
    [IsLocalRing R] [IsNoetherianRing R]
    [Algebra (IsLocalRing.ResidueField R) k]
    [IsScalarTower R (IsLocalRing.ResidueField R) k]
    [Module.Finite (IsLocalRing.ResidueField R) k]
    (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (hF : IsAlgebraicModuliStack F)
    (hft : ∃ (U : Over (Spec (.of R)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ LocallyOfFiniteType U.hom)
    (x : Object F k) (C : CompleteLocalAlgebra R k)
    (eta : FormalObject F x C) (heta : eta.IsVersal)
    (l : Type u) [Field l] [Algebra k l] [Algebra R l] [IsScalarTower R k l]
    [Module.Finite k l] (xl : Object F l)
    (xlToX : Arrow (IsScalarTower.toAlgHom R k l) xl x) :
    ∃ (D : CompleteLocalAlgebra R l) (theta : FormalObject F xl D),
      theta.IsVersal ∧ ∃ j : C.ring →ₐ[R] D.ring,
        IsLocalHom j ∧
        (∀ c : C.ring, D.residueEquiv (IsLocalRing.residue D.ring (j c)) =
          algebraMap k l (C.residueEquiv (IsLocalRing.residue C.ring c))) ∧
        (letI : Algebra C.ring D.ring := j.toRingHom.toAlgebra
         Algebra.FormallySmoothAdic C.ring D.ring (IsLocalRing.maximalIdeal D.ring)) := by
  sorry

end CategoryTheory.StackVersal
