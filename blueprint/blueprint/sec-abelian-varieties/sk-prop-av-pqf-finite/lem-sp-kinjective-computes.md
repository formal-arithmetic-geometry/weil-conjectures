+++
id = "lem-sp-kinjective-computes"
kind = "lemma"
title = "K-injective resolutions compute derived functors"
order = 519
uses = ["def-sp-grothendieck-abelian", "def-sp-injective-resolutions", "def-sp-kinjective-bridge", "def-sp-left-exact-additive"]
+++
Let $v:\mathcal A\to\mathcal B$ be a left exact additive
[def-sp-left-exact-additive] functor between Grothendieck abelian categories
[def-sp-grothendieck-abelian] and let $K\in\operatorname{Ch}^+(\mathcal A)$.
Then:

1. **(Well-definedness.)** Any two K-injective resolutions
[def-sp-kinjective-bridge] $f:K\to I$ and $g:K\to J$ are homotopy equivalent
under $K$, by a homotopy equivalence unique up to homotopy. Hence
$v(I)\cong v(J)$ by a canonical isomorphism in the homotopy category, the
object $RvK$ of [def-sp-kinjective-bridge] is well defined up to canonical
isomorphism, and it is functorial in $K$.

2. **(Agreement on objects.)** A bounded-below complex of injective objects
is K-injective. In particular an injective resolution
[def-sp-injective-resolutions] $X\to I^\bullet$ of an object $X$ is a
K-injective resolution of $X[0]$, and

$$
 \mathcal H^p\bigl(Rv(X[0])\bigr)\cong R^pv(X)
$$

for every $p$, the right-hand side being the derived functor of
[def-sp-left-exact-additive].

3. **(Shift.)** $Rv(K[n])\cong(RvK)[n]$ for every $n\in\mathbb Z$.

**Status.** The source proved the agreement in (2) by saying that a
Cartan--Eilenberg resolution refines both routes, which made this lemma and
the Cartan--Eilenberg theorem [thm-sp-if-e1] depend on each other. Nothing
below uses a Cartan--Eilenberg resolution: (1) and (3) are formal
consequences of K-injectivity, and (2) needs only that an injective
resolution of an object is a bounded-below complex of injectives. The
theorem now cites this lemma and not the other way round.

## Proof

*The comparison principle.* Let $I$ be K-injective and let $s:A\to B$ be a
quasi-isomorphism. Then

$$
 s^*:\operatorname{Hom}_{K(\mathcal A)}(B,I)\longrightarrow
 \operatorname{Hom}_{K(\mathcal A)}(A,I)
$$

is bijective. Indeed, complete $s$ to a distinguished triangle $A\to B\to
C(s)\to A[1]$ in the homotopy category; $C(s)$ is acyclic because $s$ is a
quasi-isomorphism. The functor $\operatorname{Hom}_{K(\mathcal A)}(-,I)$ is
homological, so it turns that triangle into a long exact sequence, and

$$
 \operatorname{Hom}_{K(\mathcal A)}(C(s),I[n])
 =\mathcal H^n\bigl(\operatorname{Hom}^\bullet(C(s),I)\bigr)=0
$$

for every $n$, since $C(s)$ is acyclic and $I$ is K-injective
[def-sp-kinjective-bridge]. The two outer terms of the long exact sequence
vanish, so $s^*$ is bijective.

*(1).* Apply the principle to the quasi-isomorphism $f:K\to I$ and the
K-injective complex $J$: there is $u:I\to J$, unique up to homotopy, with
$uf\simeq g$. Symmetrically there is $w:J\to I$, unique up to homotopy, with
$wg\simeq f$. Then $(wu)f\simeq wg\simeq f=\operatorname{id}_I\circ f$, and
the principle applied to $f$ and $I$ says that a morphism $I\to I$ is
determined up to homotopy by its composite with $f$; hence
$wu\simeq\operatorname{id}_I$, and symmetrically
$uw\simeq\operatorname{id}_J$. An additive functor carries homotopies to
homotopies, so $v(u)$ and $v(w)$ are mutually inverse in the homotopy
category and give the canonical isomorphism $v(I)\cong v(J)$. Uniqueness up
to homotopy makes the isomorphism independent of the choices and compatible
with composition. The same principle lifts a morphism $K\to K'$ to a morphism
between chosen resolutions, uniquely up to homotopy, which is functoriality of
$RvK$ in $K$.

*(2).* Let $I^\bullet$ be a bounded-below complex of injectives, say $I^n=0$
for $n<n_0$, let $A$ be acyclic and let $\varphi:A\to I^\bullet$ be a chain
map. We build a homotopy $h^n:A^n\to I^{n-1}$ with
$\varphi^n=d\,h^n+h^{n+1}d_A^{\,n}$ by induction on $n$, taking $h^n=0$ for
$n\leq n_0$, which is legitimate because $I^{n-1}=0$ there and $\varphi^n=0$
for $n<n_0$. Assume $h^m$ is built for $m\leq n$ and the identity holds below
$n$, and put $\psi=\varphi^n-d\,h^n:A^n\to I^n$. Then

$$
 \psi\,d_A^{\,n-1}
 =\varphi^nd_A^{\,n-1}-d\,h^nd_A^{\,n-1}
 =d\,\varphi^{n-1}-d\bigl(\varphi^{n-1}-d\,h^{n-1}\bigr)=0 ,
$$

so $\psi$ kills $\operatorname{im}d_A^{\,n-1}$, which is $\ker d_A^{\,n}$
because $A$ is acyclic. Hence $\psi$ factors through
$A^n/\ker d_A^{\,n}\cong\operatorname{im}d_A^{\,n}$, and since $I^n$ is
injective the resulting map $\operatorname{im}d_A^{\,n}\to I^n$ extends along
the monomorphism $\operatorname{im}d_A^{\,n}\hookrightarrow A^{n+1}$ to a map
$h^{n+1}:A^{n+1}\to I^n$ with $h^{n+1}d_A^{\,n}=\psi$, which is the required
identity in degree $n$. So every chain map from an acyclic complex to
$I^\bullet$ is null-homotopic. A shift $I^\bullet[n]$ is again a
bounded-below complex of injectives, so the same holds for it, and therefore
$\mathcal H^n(\operatorname{Hom}^\bullet(A,I^\bullet))
=\operatorname{Hom}_{K(\mathcal A)}(A,I^\bullet[n])=0$ for every $n$: the
complex $\operatorname{Hom}^\bullet(A,I^\bullet)$ is acyclic and
$I^\bullet$ is K-injective.

An injective resolution $X\to I^\bullet$ of an object is a bounded-below
complex of injectives which is a quasi-isomorphism from $X[0]$
[def-sp-injective-resolutions], so it is a K-injective resolution of $X[0]$.
By part (1) and [def-sp-kinjective-bridge], $Rv(X[0])\cong v(I^\bullet)$, and
$\mathcal H^p(v(I^\bullet))=R^pv(X)$ is the definition of the derived functor
in [def-sp-left-exact-additive].

*(3).* If $I$ is K-injective then so is $I[n]$, because
$\operatorname{Hom}^\bullet(A,I[n])$ is $\operatorname{Hom}^\bullet(A,I)[n]$
and a shift of an acyclic complex is acyclic. So $K[n]\to I[n]$ is a
K-injective resolution of $K[n]$, and $v$, being additive, commutes with the
shift of a complex: $Rv(K[n])=v(I[n])=v(I)[n]=(RvK)[n]$.
