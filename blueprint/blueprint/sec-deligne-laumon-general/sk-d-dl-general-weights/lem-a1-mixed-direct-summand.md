+++
id = "lem-a1-mixed-direct-summand"
kind = "lemma"
title = "Mixedness passes to subobjects, quotients, extensions and direct summands"
order = 2811
uses = ["def-weil-constructible-heart", "def-weil-frobenius-module-weights", "def-weil-punctual-weights", "def-weil-weil-sheaf-complex", "lem-a1-extension-bounds", "lem-a1-subquotient-extension-bounds"]
+++
Fix $\iota:\Qlb\xrightarrow{\sim}\mathbf C$ and $w\in\mathbf R$, and let
$Y_0$ be a finite-type $k_0$-scheme. In the abelian category of
constructible $\Qlb$-Weil sheaves on $Y_0$
([def-weil-weil-sheaf-complex], [def-weil-constructible-heart]):

1. every Weil subsheaf and every Weil quotient sheaf of a sheaf that is
   $\iota$-mixed of weights at most $w$ in the sense of
   [def-weil-punctual-weights] is $\iota$-mixed of weights at most $w$;
2. if $0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0$ is an exact
   sequence of constructible Weil sheaves and $\mathcal G'$,
   $\mathcal G''$ are $\iota$-mixed of weights at most $w$, then so is
   $\mathcal G$;
3. in particular, a direct summand of an $\iota$-mixed constructible
   Weil sheaf of weights at most $w$ is $\iota$-mixed of weights at most
   $w$.

The analogous statements hold for Frobenius modules in the sense of
[def-weil-frobenius-module-weights].

## Proof

Since $g_Y$ is an automorphism, $Lg_Y^*=g_Y^*$ is exact on the
constructible heart, so kernels, images and cokernels of morphisms of
Weil sheaves (morphisms commuting with the structure isomorphisms
$\theta$ of [def-weil-weil-sheaf-complex]) inherit Weil structures; thus
constructible Weil sheaves form an abelian category, and a Weil subsheaf
is a subobject $\mathcal H\subset\mathcal G$ with
$\theta(g_Y^*\mathcal H)=\mathcal H$. For every closed point $y$ with
geometric point $\bar y$ above it, the stalk functor
$\mathcal G\mapsto\mathcal G_{\bar y}$ is exact and carries the local
geometric Frobenius $F_y$; hence it sends exact sequences of Weil sheaves
to exact sequences of $F_y$-modules. We use repeatedly: if $V$ is a
finite-dimensional $F_y$-module all of whose eigenvalues have
$\iota$-modulus $q_y^{u/2}$, then every $F_y$-stable subquotient of $V$
has the same property, because in a basis adapted to a stable subspace
the matrix of $F_y$ is block triangular, so the characteristic
polynomials of the sub and of the quotient divide that of $V$.

Let $0=\mathcal G_0\subset\cdots\subset\mathcal G_m=\mathcal G$ be a
filtration by Weil subsheaves as in [def-weil-punctual-weights], whose
quotients $\mathcal Q_i=\mathcal G_i/\mathcal G_{i-1}$ are punctually
$\iota$-pure of weights $u_i\le w$.

*Subsheaves.* Let $\mathcal H\subset\mathcal G$ be a Weil subsheaf and put
$\mathcal H_i=\mathcal H\cap\mathcal G_i$, the kernel of the Weil morphism
$\mathcal H\to\mathcal G/\mathcal G_i$; these are Weil subsheaves in the
constructible heart. The induced map
$\mathcal H_i/\mathcal H_{i-1}\to\mathcal Q_i$ is injective, since its
kernel is $(\mathcal H\cap\mathcal G_{i-1})/\mathcal H_{i-1}=0$. Taking
stalks at $\bar y$, $(\mathcal H_i/\mathcal H_{i-1})_{\bar y}$ is an
$F_y$-stable subspace of $\mathcal Q_{i,\bar y}$, so all its Frobenius
eigenvalues have $\iota$-modulus $q_y^{u_i/2}$: the quotient is
punctually pure of weight $u_i$ (vacuously so if it is zero). Thus
$(\mathcal H_i)$ is a filtration as required by
[def-weil-punctual-weights], with weights $u_i\le w$.

*Quotients.* Let $\pi:\mathcal G\to\mathcal G''$ be an epimorphism of Weil
sheaves and put $\mathcal G''_i=\pi(\mathcal G_i)$, Weil subsheaves with
$\mathcal G''_0=0$ and $\mathcal G''_m=\mathcal G''$. The composite
$\mathcal G_i\to\mathcal G''_i\to\mathcal G''_i/\mathcal G''_{i-1}$ is
surjective and kills $\mathcal G_{i-1}$, so it factors through an
epimorphism $\mathcal Q_i\to\mathcal G''_i/\mathcal G''_{i-1}$. On stalks
this is an $F_y$-equivariant surjection from $\mathcal Q_{i,\bar y}$, so
the eigenvalues of $F_y$ on the quotient have $\iota$-modulus
$q_y^{u_i/2}$, and $(\mathcal G''_i)$ is a mixed filtration with weights
$u_i\le w$. This proves (1).

*Extensions.* In (2), choose mixed filtrations
$0=\mathcal G'_0\subset\cdots\subset\mathcal G'_a=\mathcal G'$ and
$0=\mathcal G''_0\subset\cdots\subset\mathcal G''_b=\mathcal G''$ with
punctually pure quotients of weights at most $w$. Let
$p:\mathcal G\to\mathcal G''$ be the given epimorphism and consider the
filtration of $\mathcal G$ by Weil subsheaves

$$
0=\mathcal G'_0\subset\cdots\subset\mathcal G'_a=\mathcal G'
=p^{-1}(\mathcal G''_0)\subset p^{-1}(\mathcal G''_1)\subset\cdots
\subset p^{-1}(\mathcal G''_b)=\mathcal G,
$$

where $p^{-1}(\mathcal G''_s)=\ker(\mathcal G\to\mathcal G''/\mathcal
G''_s)$. Its first $a$ quotients are those of $\mathcal G'$, and
$p$ induces isomorphisms of Weil sheaves
$p^{-1}(\mathcal G''_s)/p^{-1}(\mathcal G''_{s-1})\cong\mathcal
G''_s/\mathcal G''_{s-1}$. All quotients are therefore punctually pure of
weights at most $w$, which is (2).

*Direct summands.* If $\mathcal G=\mathcal G'\oplus\mathcal G''$ in the
Weil category, then $\mathcal G'$ is a Weil subsheaf of $\mathcal G$, so
(3) is a special case of (1).

For Frobenius modules in the sense of [def-weil-frobenius-module-weights],
stability under stable subquotients (hence direct summands) is
[lem-a1-subquotient-extension-bounds] and stability under extensions is
[lem-a1-extension-bounds]; alternatively, the three arguments above apply
verbatim with sheaves replaced by modules.
