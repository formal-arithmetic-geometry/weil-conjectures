+++
id = "lem-sp-derived-well-defined"
kind = "lemma"
title = "Well-definedness of right derived functors"
order = 502
uses = ["def-sp-grothendieck-abelian", "def-sp-injective-resolutions", "def-sp-left-exact-additive", "lem-sp-grothendieck-enough-injectives"]
+++
Let $v$ be a left exact additive [def-sp-left-exact-additive] functor and let
$X$ be an object of a Grothendieck abelian category
[def-sp-grothendieck-abelian]. Then $R^nv(X)$ is well defined, independent of
the chosen injective resolution [def-sp-injective-resolutions], and
$R^0v(X)\cong v(X)$ naturally in $X$.

## Proof

Step 1: choose resolutions. By the Grothendieck-abelian hypothesis
([def-sp-grothendieck-abelian], enough injectives by [lem-sp-grothendieck-enough-injectives]) and
[def-sp-injective-resolutions], $X$ admits an injective resolution
$I^{\bullet}$: $0\to X\to I^0\to I^1\to\cdots$, and $R^nv(X)$ is defined as
$H^n(v(I^{\bullet}))$, by [def-sp-left-exact-additive].

Step 2: independence. Let $J^{\bullet}$ be a second injective resolution of
$X$. The identity of $X$ extends to a cochain map $\varphi:I^{\bullet}\to
J^{\bullet}$ (inductively: $X\to J^0$ extends to $I^0\to J^0$ because $J^0$
is injective, and the induction step raises the degree, the maps of
$I^{\bullet}$ being inductively extended through the injectivity of the
$J^q$), and any two such extensions $\varphi,\psi$ are cochain homotopic
(their difference is a cochain map extending the zero map $X\to J^{\bullet}$
with the source $I^{\bullet}$ acyclic in positive degrees and the $J^q$
injective, so the standard lifting argument gives a homotopy). Hence
$v(\varphi):v(I^{\bullet})\to v(J^{\bullet})$ is a cochain map whose homotopy
class is independent of the choices, and since a cochain homotopy becomes an
equality in the homotopy category, the cochain maps $v(\varphi)$, $v(\psi)$
induce the same map of the homology; the composite of the maps induced by
$\varphi$ and by a map $\psi':J^{\bullet}\to I^{\bullet}$ extending the
identity of $X$ is the map induced by a chain map extending the identity,
i.e. the identity, by the same uniqueness of the homotopy class; so the
$H^n(v(I^{\bullet}))\cong H^n(v(J^{\bullet}))$ is a canonical isomorphism,
natural in $X$ (the comparison being natural by Step 2 applied functorially).

Step 3: degree zero. By left exactness of $v$
([def-sp-left-exact-additive]), the sequence

$$
 0\longrightarrow v(X)\longrightarrow v(I^0)\longrightarrow v(I^1)
$$

is exact, so $H^0(v(I^{\bullet}))=v(X)$, naturally.
