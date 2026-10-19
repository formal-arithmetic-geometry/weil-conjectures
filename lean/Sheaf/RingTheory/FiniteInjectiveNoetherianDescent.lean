/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Order.Zorn

/-!
# Noetherian descent along an injective finite ring extension

Source: P. M. Eakin, Jr., The converse to a well known theorem on Noetherian rings,
Math. Ann. 177 (1968), 278–282, main theorem
(blueprint: lem-per-finite-quotient-noetherian-descent).
-/

@[expose] public section

universe u v

namespace RingHom

/-- Noetherianity descends along an injective finite homomorphism of commutative rings.
The finite-module hypothesis uses exactly the scalar action `b • a = i b * a`.

Source: P. M. Eakin, Jr., The converse to a well known theorem on Noetherian rings,
Math. Ann. 177 (1968), 278–282, main theorem
(blueprint: lem-per-finite-quotient-noetherian-descent).

Proof (the node's complete agent-written Formanek maximal-faithful-quotient argument;
the Eakin paper and Matsumura, Commutative Ring Theory, §3, are WANTED locally):

1. In this proof a module is Noetherian if every submodule is finitely generated, with finite
generation as in [def-weil-finitely-generated-module]. We will use the following elementary
quotient observation. If $V$ is a Noetherian $R$-module and $U\subseteq V$, any submodule
$L\subseteq V/U$ is the image of its inverse image in $V$; images of a finite generating family
generate $L$. Thus $V/U$ is Noetherian. Submodules of $V$ are Noetherian because their submodules
are also submodules of $V$. Finally, if an ideal $J$ annihilates $V$, the $R$-submodules and
$R/J$-submodules coincide, and an $R$-linear combination depends only on coefficient classes in
$R/J$; hence finite generation and Noetherianity over these two scalar rings coincide.

2. Here is the finite evaluation observation used below. For a commutative ring $R$ and a finite
faithful Noetherian $R$-module $V$, choose generators $v_1,\ldots,v_s$. Faithful means that $rv=0$
for every $v\in V$ implies $r=0$. The $R$-linear map $e:R\to V^s$, $r\mapsto(rv_1,\ldots,rv_s)$,
is injective: if all coordinates vanish, $r$ kills every linear combination of the generators. By
[lem-per-noetherian-module-finite-product], $V^s$ is Noetherian. For any ideal $H\subseteq R$,
choose generators of the submodule $e(H)$ and lift them to $H$; injectivity shows that these lifts
generate $H$. Therefore every ideal of $R$ is finitely generated, so $R$ is Noetherian
[def-weil-pbc-noetherian-ring]. This also covers $s=0$, when faithfulness forces $R=0$.

3. Regard $A$ as a finite $B$-module through $i$. We prove it is Noetherian as a $B$-module.
Suppose it is not. For a $B$-ideal $I$ write $IA$ for the ideal generated in $A$ by $i(I)$. The
set of ideals $IA$ for which $A/IA$ is not Noetherian as a $B$-module is nonempty, since $I=0$
belongs to it. Since $A$ is a Noetherian ring, [lem-weil-pbc-noetherian-ideal-set-maximal] gives a
maximal member $I_0A$ of this set. Set $M=A/I_0A$. Its generators are the images of a fixed finite
$B$-generating family of $A$.

4. Put $J=\{b\in B:i(b)A\subseteq I_0A\}$, the annihilator of $M$, and $R=B/J$. We have
$I_0\subseteq J$ and $JA=I_0A$: one inclusion follows from $I_0\subseteq J$, the other from the
defining condition on $J$. Thus $M$ is a finite faithful $R$-module and is not Noetherian, by Step
1. If $H\ne0$ is an ideal of $R$, its inverse image $L\subseteq B$ strictly contains $J$. Then
$LA$ strictly contains $JA$: equality would imply $L\subseteq J$ by the definition of $J$.
Maximality in Step 3 says that $A/LA$ is Noetherian over $B$. The quotient of $A$ by the inverse
image of $HM$ is $A/LA$, since that inverse image is $LA+I_0A=LA$. Hence $M/HM$ is Noetherian over
$R$ by Step 1, for every nonzero ideal $H$ of $R$.

5. Consider the set $\mathcal S$ of $R$-submodules $N\subseteq M$ for which $M/N$ is faithful. It
contains $0$. A nonempty chain has union $N_\infty$, an $R$-submodule. If $rM\subseteq N_\infty$,
finitely many generators $m_1,\ldots,m_s$ of $M$ give finitely many elements $rm_j$ in that union.
Choose one chain member containing all of them; when the family is empty choose any member of the
nonempty chain. This member contains $rM$, so faithfulness of its quotient gives $r=0$. Thus
$M/N_\infty$ is faithful. The empty chain has upper bound $0$. Apply [lem-weil-pbc-zorn-lemma] to
these underlying subsets of $M$, with the indicated chain upper bounds, to obtain a maximal
$N_0\in\mathcal S$. Set $Q=M/N_0$. It is finite and faithful. By maximality, $Q/U$ is not faithful
for every nonzero submodule $U\subseteq Q$: its inverse image in $M$ strictly contains $N_0$.

6. If $Q$ were Noetherian, Step 2 would make $R$ Noetherian. Since $M$ is finite over $R$,
[lem-weil-pbc-noetherian-submodule-finite] would then make every submodule of $M$ finite, contrary
to the choice of $M$. Thus $Q$ is not Noetherian. On the other hand, for every nonzero ideal
$H\subseteq R$, the map $M\to Q$ induces a surjection $M/HM\to Q/HQ$; the image of $HM$ is exactly
$HQ$, by writing elements as finite sums of scalar multiples. Step 4 and the quotient observation
of Step 1 imply that $Q/HQ$ is Noetherian.

7. Let $U\subseteq Q$ be a nonzero $R$-submodule. Since $Q/U$ is not faithful by Step 5, there is
$0\ne a\in R$ with $aQ\subseteq U$. The module $aQ$ is finite: multiply a finite generating family
of $Q$ by $a$. By Step 6, $Q/aQ$ is Noetherian (apply it to the nonzero principal ideal $(a)$), so
its submodule $U/aQ$ has a finite generating family. Lift that family to $u_1,\ldots,u_t\in U$.
Every $u\in U$ differs from an $R$-linear combination of the $u_j$ by an element of $aQ$;
adjoining generators of $aQ$ therefore generates $U$. The zero submodule has the empty generating
family. Every submodule of $Q$ is consequently finite, contradicting Step 6. This contradiction
proves that the original $B$-module $A$ is Noetherian.

8. For a $B$-ideal $H$, the subset $i(H)\subseteq A$ is a $B$-submodule, hence has finitely many
$B$-module generators by the preceding conclusion. Lift these generators to $H$. Since $i$ is
injective, they generate $H$: apply $i$ to any proposed linear combination and use injectivity on
the difference. Thus every ideal of $B$ is finitely generated, which is exactly that $B$ is
Noetherian [def-weil-pbc-noetherian-ring]. If $A=0$, injectivity forces $B=0$, and the same
conclusion holds.
-/
theorem isNoetherianRing_of_injective_of_finite
    {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    (i : B →+* A) (hi : Function.Injective i) [IsNoetherianRing A]
    (hfinite : @Module.Finite B A _ _ (@Algebra.toModule B A _ _ i.toAlgebra)) :
    IsNoetherianRing B := by
  sorry

end RingHom
