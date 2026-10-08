+++
id = "lem-coef-integral-finite-extension"
kind = "lemma"
title = "Integral duality and a finite extension of coefficient fields"
order = 2150
uses = ["cor-coef-integral-internal-hom", "lem-coef-finite-free-extension", "lem-coef-integral-residue-tor", "lem-coef-normalized-dvr-effectivity", "prop-coef-integral-dualizing", "thm-coef-integral-verdier"]
+++
Let $E\subset L$ be finite extensions of $\Ql$, put
$R=\mathcal O_E$, $S=\mathcal O_L$, and write
$T_{S/R}K=S\widehat\otimes_R^LK$. This exact functor preserves
the integral bounded constructible categories. There are canonical
isomorphisms

$$
u_{L/E}:T_{S/R}\omega_{X,R}\xrightarrow{\sim}\omega_{X,S},
\qquad
v_{K,M}:T_{S/R}R\mathcal Hom_R(K,M)
\xrightarrow{\sim}R\mathcal Hom_S(T_{S/R}K,T_{S/R}M),
$$

and consequently

$$
\beta_{L/E,K}:T_{S/R}D_{X,R}K
\xrightarrow{\sim}D_{X,S}(T_{S/R}K)
\qquad(K,M\in D^b_c(X,R)).
$$

They commute with evaluation and with the canonical map
$K\to D_{X,R}D_{X,R}K$. They are compatible with finite
coefficient quotients, the identity extension, and composition of
finite field extensions, including the tensor associators.

## Proof

The $R$-module $S$ is finite free. On completed coefficient
sheaves it is therefore still finite free; its tensor functor is
exact and commutes with derived inverse limits. In particular the
completed tensor of a derived-complete complex is the ordinary
derived tensor with this finite free coefficient sheaf. If $e$
is the ramification index, the ideals
$\varpi_E^nS=\varpi_L^{en}S$ are a cofinal system of powers of
the maximal ideal of $S$. The reductions of $T_{S/R}K$ along
this system are

$$
(S/\varpi_E^nS)\otimes_{R/\varpi_E^n}^LK_n,
\qquad K_n=K\otimes_R^L R/\varpi_E^n.
$$

They are constructible and have a uniform Tor interval, since
[lem-coef-integral-residue-tor] supplies that interval for
$K_n$ and finite free extension preserves it. The normalized
tower reconstruction of [lem-coef-normalized-dvr-effectivity]
therefore gives an object of $D^b_c(X,S)$. The intervening
$\varpi_L$-reductions are recovered by derived tensor from
any larger cofinal level, so they have the same Tor bound.

By [prop-coef-integral-dualizing], the reductions of the
integral dualizing objects are the finite dualizing objects.
At the cofinal levels [lem-coef-finite-free-extension] gives
the specified maps

$$
(S/\varpi_E^nS)\otimes_{R/\varpi_E^n}^L\omega_{X,R/\varpi_E^n}
\xrightarrow{\sim}\omega_{X,S/\varpi_E^nS}.
$$

Their quotient compatibility makes them a map of normalized
derived towers. Taking the derived limit, and using the
finite-free tensor comparison above, gives
$u_{L/E}$, including its naturality and compatibility with the
dualizing counit. This argument uses coherent maps of towers,
not just isomorphism classes of their terms.

The map $v_{K,M}$ is the transpose of scalar-extended
evaluation. To prove it is an isomorphism, forget the
$S$-action. Extension–restriction adjunction identifies its
target with
$R\mathcal Hom_R(K,S\otimes_RM)$. Locally choose a finite
free $R$-basis of $S$. Both this object and the source
identify with the corresponding finite sum of
$R\mathcal Hom_R(K,M)$, and $v_{K,M}$ becomes the identity
comparison of these sums. Forgetting coefficients is conservative,
so the comparison is an isomorphism. This reasoning uses finite
freeness of the coefficient extension, with no perfectness
assumption on $K$ on the whole space. All these internal Hom
objects are integral bounded constructible objects by
[cor-coef-integral-internal-hom].

Compose $v_{K,\omega_{X,R}}$ with internal Hom into
$u_{L/E}$ to obtain $\beta_{L/E,K}$. It identifies the
ambient integral duals of [thm-coef-integral-verdier].
Evaluation compatibility follows from the definition by
transposition. Transposing evaluation once more gives compatibility
with the double-dual map. For nested rings $R\subset S\subset U$,
the associator being used is

$$
U\otimes_S^L(S\otimes_R^LK)\xrightarrow{\sim}U\otimes_R^LK.
$$

For $u$, the unit and composition equations are the equations
of the finite comparisons, transported through derived inverse
limit. For $v$, both composites transpose to the
same evaluation after this associator; hence they are equal.
The same is true for $\beta$. These arguments also prove
compatibility with finite quotients and involve no chosen basis
in the definition of any comparison.
