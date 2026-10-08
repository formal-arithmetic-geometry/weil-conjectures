+++
id = "thm-weil-karoubian-bounded-t"
kind = "theorem"
title = "Bounded t-structures are Karoubian"
order = 1427
uses = ["def-weil-karoubi-envelope", "def-weil-t-structure", "lem-weil-envelope-tstructure", "lem-weil-karoubi-envelope-fully-faithful", "lem-weil-karoubi-envelope-idempotent-complete", "lem-weil-karoubi-envelope-triangulated", "prop-weil-heart-abelian"]
+++
If a triangulated category $\mathcal T$ has a bounded t-structure, then
$\mathcal T$ is idempotent complete: every idempotent $e:K\to K$ of $\mathcal
T$ splits, and the canonical fully faithful functor $\mathcal T\to\Kar(\mathcal
T)$ of [def-weil-karoubi-envelope] is an exact equivalence.

(*Source note:* no Stacks Project entry states this form: Stacks has no
t-structure (hence no bounded t-structure and no heart) and no idempotent
completion of a triangulated category; its Karoubianity entries are the
definition of the Karoubian property (Definition 12.4.1, Tag
[09SG](https://stacks.math.columbia.edu/tag/09SG)), the splitting criterion
of Lemma 12.4.2 (Tag [09SH](https://stacks.math.columbia.edu/tag/09SH)) and
the criteria of Lemma 12.4.3 (Tag
[05QV](https://stacks.math.columbia.edu/tag/05QV): countable products and
kernels of maps which have a right inverse, or dually countable coproducts
and cokernels of maps which have a left inverse), which are sufficient
conditions of a different kind and are not stated for triangulated
categories. The blueprint adds the Karoubianity of a triangulated category
carrying a bounded t-structure, the input used for the finite-stage and
$\Qlb$ coefficient categories of this manuscript.*)

## Proof

By [lem-weil-karoubi-envelope-triangulated] the envelope $\mathcal
T^\natural=\Kar(\mathcal T)$ of [def-weil-karoubi-envelope] is triangulated
and, by [lem-weil-envelope-tstructure], carries the extended t-structure
$((\mathcal T^\natural)^{\le0},(\mathcal T^\natural)^{\ge0})$, which is
bounded because every object of $\mathcal T^\natural$ is a retract of an
object of $\mathcal T$, of finite t-amplitude in the bounded t-structure of
$\mathcal T$. We show that every $Y\in\mathcal T^\natural$ is isomorphic to
an object of $\mathcal T$; full faithfulness of $\mathcal T\to\mathcal
T^\natural$, which is [lem-weil-karoubi-envelope-fully-faithful], then makes
it an equivalence, and every idempotent of $\mathcal T$ splits because its
image in $\mathcal T^\natural$ splits in the envelope that is idempotent
complete by [lem-weil-karoubi-envelope-idempotent-complete], and a splitting
transported back through the equivalence splits it in $\mathcal T$.

Since the extended t-structure is bounded, replacing $Y$ by a shift (which
preserves the property of being isomorphic to an object of $\mathcal T$), we
may assume $Y\in(\mathcal T^\natural)^{\ge0}$. Let $n\ge0$ be minimal with
$Y\in(\mathcal T^\natural)^{\le n}$, and argue by induction on $n$.

If $n=0$, then $Y$ lies in the heart of $\mathcal T^\natural$, which by
[lem-weil-envelope-tstructure] is equivalent to $\Kar(\mathcal H(\mathcal
T))$; by [prop-weil-heart-abelian] the heart $\mathcal H(\mathcal T)$ is
abelian and hence idempotent complete, so $\Kar(\mathcal H(\mathcal
T))=\mathcal H(\mathcal T)$ via the canonical functor, and $Y$ is isomorphic
to an object of $\mathcal H(\mathcal T)\subset\mathcal T$.

Assume $n>0$. The top truncation triangle of [def-weil-t-structure] in
$\mathcal T^\natural$ is

$$
 A:=\tau^{\le n-1}Y\longrightarrow Y\longrightarrow
 B:=\mathcal H^n(Y)[-n]\longrightarrow A[1],
$$

with $A\in(\mathcal T^\natural)^{\ge0}\cap(\mathcal T^\natural)^{\le n-1}$
(the truncation triangle and $\mathcal T^\natural$'s $\ge0$-part being closed
under kernels in the triangulated sense: $Y,B\in(\mathcal T^\natural)^{\ge0}$
and the connecting morphism argument gives $A\in(\mathcal
T^\natural)^{\ge0}$). By the induction hypothesis $A$ is isomorphic to an
object of $\mathcal T$. By [lem-weil-envelope-tstructure] the object $\mathcal
H^n(Y)$ lies in the heart of $\mathcal T^\natural$, which is equivalent to
$\mathcal H(\mathcal T)$ by the $n=0$ case; hence $B$ is isomorphic to an
object of $\mathcal T$. Since $\mathcal T\to\mathcal T^\natural$ is fully
faithful, the connecting morphism $\delta:B\to A[1]$ is the image of a
morphism of $\mathcal T$. Complete $\delta$ to a distinguished triangle in
$\mathcal T$ and rotate it to obtain

$$
 A\longrightarrow C\longrightarrow B\overset{\delta}{\longrightarrow}A[1]
$$

with the displayed connecting morphism $\delta$. This triangle is
distinguished in $\mathcal T^\natural$ as well. It and the truncation
triangle are cone triangles for the same morphism $\delta$ in $\mathcal
T^\natural$, so by uniqueness of cones (any two cone triangles of a morphism
are isomorphic by a morphism of triangles whose first two components are
identities) there is an isomorphism of triangles fixing $A$ and $B$; in
particular $Y\cong C$ in $\mathcal T^\natural$, with $C\in\mathcal T$. This
completes the induction and the proof.
