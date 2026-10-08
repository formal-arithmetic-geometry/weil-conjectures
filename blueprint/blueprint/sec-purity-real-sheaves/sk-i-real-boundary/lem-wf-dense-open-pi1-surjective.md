+++
id = "lem-wf-dense-open-pi1-surjective"
kind = "lemma"
title = "Fundamental groups of a dense open surject"
order = 2646
uses = ["cor-galois-lisse-representations", "d-real-setup", "def-galois-fibre-functor", "def-weil-pbc-constructible-complexes", "def-wf-fundamental-representation", "def-wf-middle-extension", "def-wf-weil-group", "lem-a1-lisse-middle-extension", "lem-fet-galois-category", "lem-fin-etale-normal-components", "lem-fin-normal-open-lisse-image", "lem-galois-transitive", "lem-wf-weil-group-exact-sequence", "prop-wf-weil-sheaf-representation-equivalence", "thm-galois-fundamental"]
+++
Let $V$ be a connected normal Noetherian scheme, let
$k:V'\hookrightarrow V$ be a dense open immersion, and let $\bar v$ be a
geometric point of $V'$, with the fundamental groups of
[def-galois-fibre-functor].

1. (*Geometric surjectivity.*) The map
   $\pi_1(V',\bar v)\to\pi_1(V,\bar v)$ induced by pullback of finite
   etale covers is surjective. Equivalently, a connected finite etale
   cover of $V$ stays connected over $V'$.
2. (*Weil groups.*) Let $V_0$ be a separated finite-type $k_0$-scheme
   whose base change $V=V_0\times_{k_0}k$ is connected and normal, let
   $V'_0\subseteq V_0$ be a dense open, and put
   $V'=V'_0\times_{k_0}k$. Then the induced map of Weil groups
   $W(V'_0)\to W(V_0)$ of [def-wf-weil-group] commutes with the degree
   maps, restricts on the geometric subgroups to the surjection of (1),
   and is surjective.
3. (*Lisse sheaves extend uniquely.*) For every lisse sheaf
   $\mathcal N$ on $V$ (at every finite coefficient level, hence for
   lisse $\Qlb$-sheaves in the convention of
   [def-weil-pbc-constructible-complexes]) the adjunction unit
   $\mathcal N\to k_*k^*\mathcal N$ is an isomorphism.
4. (*Restriction on curves.*) Let $U_0$ be a curve in the sense of
   [d-real-setup] and $k:U'_0\hookrightarrow U_0$ a nonempty open.
   Pullback $k^*$ from lisse Weil sheaves on $U_0$ to lisse Weil sheaves
   on $U'_0$ is fully faithful, and it carries irreducible objects (no
   lisse subsheaf other than $0$ and itself) to irreducible objects. The
   same holds for lisse $\Qlb$-sheaves on the geometric curves
   $U'\hookrightarrow U$.
5. (*Constructibility.*) If $j:U_0\hookrightarrow C_0$ is a nonempty
   open in a curve $C_0$ of [d-real-setup] and $\mathcal F$ is lisse on
   $U_0$, then the middle extension $j_*\mathcal F$ of
   [def-wf-middle-extension] is constructible at every finite
   coefficient level.

## Proof

*Step 0 ($V$ is integral).* The local rings of the normal scheme $V$
are domains, so $V$ is reduced and a point lies on only one irreducible
component (two components through it would give two minimal primes of
its local domain). The finitely many components are therefore disjoint
and closed, hence open, and connectedness leaves only one: $V$ is
integral. The same argument applies to every connected normal
Noetherian scheme below.

*(1).* Let $W\to V$ be a connected finite etale cover. Its image is
open (etale) and closed (finite) and nonempty, so $W\to V$ is surjective
since $V$ is connected. The scheme $W$ is Noetherian, being finite over
$V$, so by [lem-fin-etale-normal-components] it is a finite disjoint
union of open-and-closed normal integral schemes; being connected, $W$
is itself integral. Its open subscheme $W':=W\times_VV'$ is nonempty,
because $W\to V$ is surjective and $V'\neq\emptyset$; a nonempty open
of an irreducible scheme is irreducible, so $W'$ is connected. This is
the second formulation.

To get surjectivity, note that pullback along $k$ is compatible with the
fibre functors at $\bar v$, which gives the map of automorphism groups
$\pi_1(V',\bar v)\to\pi_1(V,\bar v)$ of [def-galois-fibre-functor],
continuous for the profinite topologies; under the equivalences of
[thm-galois-fundamental] the fibre of $W'$ is the fibre of $W$ with
$\pi_1(V',\bar v)$ acting through this map. Its image $H$ is compact,
hence closed in $G:=\pi_1(V,\bar v)$. If $H\neq G$, then, a closed
subgroup of a profinite group being the intersection of the open
subgroups containing it, there is an open subgroup $H\subseteq
U\subsetneq G$. The finite continuous $G$-set $G/U$ is transitive, so by
[thm-galois-fundamental] it is the fibre of a finite etale $W\to V$
which is connected: a decomposition $W=W_1\sqcup W_2$ into nonempty
open-and-closed pieces would split $G/U$ into two nonempty $G$-stable
subsets, both pieces being surjective over $V$ as above. On the other
hand, $H\subseteq U$ fixes the coset $U$, and $|G/U|\geq2$, so
$\pi_1(V',\bar v)$ does not act transitively on the fibre of $W'$. Since
$(\mathrm{F\acute Et}(V'),F_{\bar v})$ is a Galois category by
[lem-fet-galois-category], [lem-galois-transitive] shows that $W'$ is
not connected, contradicting the first paragraph. Hence $H=G$. This is
SGA 1, Exp. V, Prop. 8.2.

*(2).* The base change $V\to V_0$ is universally open, so $V'$ is a
dense open of $V$, and (1) applies to $V'\subseteq V$. Choose $\bar v$
in $V'$. The morphism $V'_0\to V_0$ is a $k_0$-morphism, so the map
$\pi_1(V'_0,\bar v)\to\pi_1(V_0,\bar v)$ lies over
$\operatorname{Gal}(k/k_0)$ and hence induces a map of the fibre
products
$W(-)=\pi_1(-,\bar v)\times_{\operatorname{Gal}(k/k_0)}\langle\Phi\rangle$
of [def-wf-fundamental-representation] which is the identity on the
factor $\langle\Phi\rangle$; this is the compatibility with the degree
maps of [def-wf-weil-group]. By [lem-wf-weil-group-exact-sequence] the
kernels of the degree maps are the geometric groups $\pi_1(V')$ and
$\pi_1(V)$, and the induced map between them is the map of (1). Now let
$w\in W(V_0)$ have degree $n$. By [lem-wf-weil-group-exact-sequence]
there is $w'\in W(V'_0)$ of degree $n$; its image $\bar w'$ has degree
$n$, so $w\bar w'^{-1}$ lies in $\pi_1(V)$ and, by (1), is the image of
some $g\in\pi_1(V')$. Then $gw'\mapsto w$.

*(3).* It suffices to work at a finite coefficient level, the
$\Qlb$-statement being assembled from these levels by the conventions of
[def-weil-pbc-constructible-complexes], and to evaluate on affine etale
$T\to V$. Such $T$ is Noetherian, so by
[lem-fin-etale-normal-components] it is a finite disjoint union of
normal integral $T_i$, and it suffices to treat each $T_i$. The open
$T'_i:=T_i\times_VV'$ is nonempty (the image of $T_i$ is a nonempty open
of the integral $V$, hence meets $V'$), hence dense in $T_i$. Pick a
geometric point $\bar t$ of $T'_i$. Sections of $\mathcal N$ over the
connected $T_i$ are morphisms from the constant sheaf, so by
[cor-galois-lisse-representations] they are the invariants
$\mathcal N_{\bar t}^{\pi_1(T_i,\bar t)}$; likewise
$(k_*k^*\mathcal N)(T_i)=\mathcal N(T'_i)
=\mathcal N_{\bar t}^{\pi_1(T'_i,\bar t)}$, and restriction is the
inclusion of invariants. By (1) applied to $T'_i\subseteq T_i$ the two
groups have the same image in $\operatorname{Aut}(\mathcal N_{\bar t})$,
so the invariants agree. For curves this recovers
[lem-a1-lisse-middle-extension].

*(4).* The open $U'_0$ is again a curve in the sense of [d-real-setup]
(a nonempty open of the irreducible smooth $U$ is connected), and $U$,
$U'$ share the geometric generic point $\bar\eta$. By
[prop-wf-weil-sheaf-representation-equivalence] on $U_0$ and on
$U'_0$, lisse Weil sheaves are the representations of the Weil groups
on their generic stalks, and $k^*$ corresponds to restriction along
$W(U'_0)\to W(U_0)$: the stalk at $\bar\eta$ is unchanged and the
fundamental representation of [def-wf-fundamental-representation] is
formed from pullbacks of the same covers. This map is surjective by (2)
(normality of $U$ being smoothness). Hence
$\operatorname{Hom}_{W(U_0)}(V_1,V_2)=\operatorname{Hom}_{W(U'_0)}(V_1,V_2)$,
which is full faithfulness, and the $W(U_0)$-stable and
$W(U'_0)$-stable subspaces of a stalk coincide. Since subobjects match
under the equivalence, lisse subsheaves of $\mathcal N$ and of
$k^*\mathcal N$ correspond, which gives the statement on irreducibility.
The geometric version is the same argument with
[cor-galois-lisse-representations] and (1).

*(5).* The curve $C_0$ is smooth with connected base change, hence
integral of finite type over $k_0$ by Step 0, and its open $U_0$ is
normal. At each finite coefficient level $\mathcal F$ is finite locally
constant, so [lem-fin-normal-open-lisse-image] applies.
