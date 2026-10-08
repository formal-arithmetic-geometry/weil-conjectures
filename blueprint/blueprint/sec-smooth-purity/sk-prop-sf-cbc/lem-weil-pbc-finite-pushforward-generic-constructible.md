+++
id = "lem-weil-pbc-finite-pushforward-generic-constructible"
kind = "lemma"
title = "Generic finite pushforward is constructible"
order = 1578
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-noetherian-finite-components", "lemma-weil-pbc-finite-exchange", "pqf-lem-finite-integral-lft", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $S$ be an integral Noetherian affine scheme, let $g:Z\to S$ be finite, and
let $E$ be a constructible abelian etale sheaf on $Z$. There is a dense open
$S^\circ\subset S$ on which the direct image $g_*E$ is lisse.

## Proof

Write $S=\operatorname{Spec}A$, with $A$ a Noetherian domain and fraction
field $K$. A finite algebra is integral ([pqf-lem-finite-integral-lft]). Lying over, applied also after every
base change, shows that a finite map is closed: the image of $V(I)$ is the
closed set defined by the contraction of $I$. We use this elementary
finite-algebra fact to shrink the base below.

The nilpotent closed immersion $Z_{\mathrm{red}}\to Z$ is a universal
homeomorphism, so invariance of the etale site under universal homeomorphisms
permits us to replace $Z$ by $Z_{\mathrm{red}}$, pulling back $E$. By
[lem-weil-pbc-noetherian-finite-components], $Z$ has finitely many irreducible
components $C_i$. The points of its generic fibre are exactly the generic
points of the components dominating $S$: in a finite algebra over a domain,
primes over $(0)$ become primes of an Artinian $K$-algebra, hence are minimal.
If there are none, $g(Z)$ is a proper closed subset and $g_*E$ is zero on its
open complement.

For each dominating $C_i$, the finite lisse partition of $E$ has a locally
closed stratum containing its generic point. That stratum contains an open
neighbourhood of the generic point inside $C_i$. Shrink this neighbourhood
further to avoid every other component. It is then open in the reduced scheme
$Z$, and $E$ is lisse there. The union $W$ of these finitely many
neighbourhoods contains the whole generic fibre. The closed subset $g(Z\setminus
W)$ misses the generic point of $S$. Choose a nonempty principal open in its
complement and replace $S$ by it. Now $E$ is lisse on all of $Z$.

Here is the finite-algebra calculation needed for the remaining step. Put
$B=\Gamma(Z,\mathcal O_Z)$. The reduced finite $K$-algebra $B\otimes_AK$ is a
finite product of finite extensions $L_i/K$. In each $L_i$, the elements
separable over $K$ form its maximal separable subextension, over which $L_i$
is purely inseparable. Choose a finite Galois extension $K'/K$ containing
every conjugate of these finitely many separable subextensions. Consequently

$$
 \bigl(B\otimes_AK'\bigr)_{\mathrm{red}}
       =\prod_j L'_j
$$

with each $L'_j/K'$ purely inseparable. Indeed, tensoring each separable
subextension with $K'$ splits it into a product of copies of $K'$; the
remaining purely inseparable extension has, after any field base change and
reduction, a single purely inseparable residue field.

A primitive element for $K'/K$ has a monic separable minimal polynomial $P\in
K[t]$. Invert its finitely many coefficient denominators and its nonzero
discriminant in $A$. Then

$$
 A'=A[t]/(P)\subset K',\qquad \operatorname{Frac}(A')=K'
$$

is a finite free etale domain over $A$, of positive rank. The basis
$1,t,\ldots,t^{\deg P-1}$ proves injectivity into $K'$; invertibility of $P'$
in the quotient proves the etale condition. Positive rank and lying over make
$\operatorname{Spec}A'\to\operatorname{Spec}A$ surjective.

Put $D=(B\otimes_AA')_{\mathrm{red}}$. Its $A'$-torsion is a finitely
generated module, so one nonzero element annihilates it. After inverting that
element,

$$
 D\hookrightarrow D\otimes_{A'}K'=\prod_jL'_j .
$$

Each idempotent of this finite product is a fraction $d/c$ with $d\in D$ and
$0\neq c\in A'$. Inverting these finitely many denominators places all the
idempotents in $D$; their relations hold because of the displayed injection.
Hence $D=\prod_jD_j$, with each $D_j$ a finite $A'$-algebra embedded in
$L'_j$, and thus a domain.

In characteristic $p>0$, choose finite algebra generators of the $D_j$. Pure
inseparability supplies one common $q=p^e$ such that every generator $b$ has
$b^q\in K'$. Clear these finitely many denominators to put all $b^q$ in $A'$.
In a field of characteristic $p$, a $q$-th root is unique if it exists. Thus
at most one homomorphism from each $D_j$ to any field can extend a given
homomorphism from $A'$. This is precisely the radicial condition. Each $A'\to
D_j$ is injective and integral, so lying over gives surjectivity, also after
base change. After any base change the map is therefore a bijective finite
closed map, hence a homeomorphism. In characteristic zero the fields $L'_j$
equal $K'$; clearing denominators in the finite generators directly gives
$D_j=A'$. In both cases every $\operatorname{Spec}D_j\to\operatorname{Spec}A'$
is a finite surjective universal homeomorphism.

All the localizations just made in $A'$ come from shrinking
$\operatorname{Spec}A$. Combine their denominators into a single nonzero $c$
in the original finite free algebra $A'$, clearing any previous denominators
first. The determinant $N(c)\in A$ of multiplication by $c$ is nonzero, as is
seen after tensoring with $K$. The adjugate matrix shows that inverting $N(c)$
makes $c$ a unit in $A'$. Thus the final cover
$S'=\operatorname{Spec}A'\to S^\circ$ is still finite surjective etale. Only
the reduction of $Z\times_SS'$ has been decomposed into the
$\operatorname{Spec}D_j$; its nilpotent thickening is handled by invariance
under universal homeomorphisms.

Under that same site equivalence, a finite locally constant sheaf descends to
a finite locally constant sheaf: a trivializing etale covering descends and
the equivalence identifies constant sheaves. Therefore the direct image on
$S'$ is a finite product of lisse sheaves, hence lisse by a common refinement
of their finitely many trivializing covers. [lemma-weil-pbc-finite-exchange]
identifies it with the pullback of $g_*E|_{S^\circ}$. The cover $S'\to
S^\circ$ is itself etale and surjective, so its trivializing covers form a
trivializing etale cover of $S^\circ$, proving the assertion.
