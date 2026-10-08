+++
id = "prop-weil-proet-finite-proper-base-change"
kind = "theorem"
title = "Finite-torsion proper base change"
order = 1321
tags = ["latex:proposition"]
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-derived-categories", "def-weil-pbc-derived-exchange", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-derived-exchange-coherence", "lemma-weil-pbc-torsion-assembly", "thm-weil-pbc-bounded-below"]
+++
Let

$$
\begin{CD}
X'@>{g'}>>X\\
@V{f'}VV @VV{f}V\\
Y'@>{g}>>Y
\end{CD}
$$

be Cartesian with $f$ proper. For every torsion sheaf $F$ on
$X_{\mathrm{et}}$, the canonical exchange map

$$
g^{-1}Rf_*F\xrightarrow{\sim}Rf'_*g'^{-1}F
$$

is an isomorphism. These isomorphisms are natural in $F$, equal the identity
for identity squares, and commute with horizontal and vertical pasting.

## Proof

The torsion assembly proves the isomorphism in every cohomological degree for
the map constructed in S0. A morphism in $D^+$ is an isomorphism exactly when
all its cohomology sheaf maps are isomorphisms. Naturality, identity, and
pasting are the corresponding S0 coherence equations and survive each
devissage step. This is the expanded endpoint whose source locator is Tag
`095T`; that tag is not used as a proof leaf.

## Detailed form

Let

$$
 \begin{array}{ccc}
 X'&\xrightarrow{g'}&X\\
 f'\downarrow&&\downarrow f\\
 Y'&\xrightarrow{g}&Y
 \end{array}
$$

be cartesian [def-weil-pbc-cartesian-square] with $f$ proper. For every
torsion sheaf $F$ on $X_{\Et}$,

$$
 \Ex_{\square,F}:g^{-1}Rf_*F
 \xrightarrow{\sim}Rf'_*g'^{-1}F
$$

is an isomorphism in $\Dplus(Y'_{\Et})$, where $\Ex_{\square,F}$ is the
derived exchange morphism [def-weil-pbc-derived-exchange].

## Proof

View $F$ as the complex $F[0]$; its only cohomology sheaf is the torsion sheaf
$F$, so $F[0]$ has torsion cohomology. [thm-weil-pbc-bounded-below] applied to
$K=F[0]$ makes the derived exchange morphism $\Ex_{\square,F[0]}$ an
isomorphism in $\Dplus(Y'_{\Et})$; by [def-weil-pbc-derived-exchange] that
morphism for a complex concentrated in degree zero is the exchange morphism
$\Ex_{\square,F}$ of the sheaf $F$, giving the assertion.
