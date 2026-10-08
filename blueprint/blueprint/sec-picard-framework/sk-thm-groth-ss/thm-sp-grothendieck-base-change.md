+++
id = "thm-sp-grothendieck-base-change"
kind = "theorem"
title = "Base-change naturality of the Grothendieck spectral sequence"
order = 604
uses = ["def-sp-composite-acyclicity", "def-sp-injective-resolutions", "lem-sp-couple-morphism", "thm-sp-grothendieck", "thm-sp-spectral-object-yields"]
+++
Let $(F,G)$ and $(F',G')$ be composable pairs
[def-sp-composite-acyclicity] in Grothendieck abelian categories $\mathcal
A,\mathcal B,\mathcal C$ and $\mathcal A',\mathcal B',\mathcal C'$, and let

$$
 \alpha:\mathcal A\to\mathcal A',\qquad
 \beta:\mathcal B\to\mathcal B',\qquad
 \gamma:\mathcal C\to\mathcal C'
$$

be additive *exact* functors making the squares

$$
\begin{array}{ccc}
\mathcal A&\xrightarrow{F}&\mathcal B\\
\downarrow\alpha&&\downarrow\beta\\
\mathcal A'&\xrightarrow{F'}&\mathcal B'
\end{array}
\qquad
\begin{array}{ccc}
\mathcal B&\xrightarrow{G}&\mathcal C\\
\downarrow\beta&&\downarrow\gamma\\
\mathcal B'&\xrightarrow{G'}&\mathcal C'
\end{array}
$$

commute up to fixed natural isomorphisms, and suppose that $F$ sends
injectives to $G$-acyclics and $F'$ sends injectives to $G'$-acyclics. Then
the Grothendieck spectral sequences of [thm-sp-grothendieck] for $(F,G)$ and
$(F',G')$ are related by a morphism of spectral sequences natural in all the
data. In the base-change situation of the proper-base-change chapter, where
the functors are inverse images along the maps of a cartesian square, this
says that the spectral sequence is compatible with inverse image along a base
change.

**Status.** The vertical maps were formerly called "natural transformations
$\alpha:A\to A'$", a type the proof cannot use; they are now specified as
additive exact functors, and their exactness is exactly what transports
resolutions. The proof is written out through the double complexes of
[thm-sp-grothendieck] and the couple morphisms of
[lem-sp-couple-morphism].

## Proof

*Step 1: the map of double complexes.* By the proof of
[thm-sp-grothendieck] the two spectral sequences are those of the double
complexes $C^{\bullet,\bullet}$ and $C'^{\bullet,\bullet}$ obtained from
injective resolutions $X\to I^\bullet$, $X'\to I'^\bullet$ and
Cartan--Eilenberg resolutions of $F(I^\bullet)$ and $F'(I'^\bullet)$.
Exactness of $\alpha$ and of $\beta$ carries an injective resolution of $X$
to a resolution of $\alpha X$ with acyclic terms, and the commutativity of
the squares identifies $\beta F(I^\bullet)$ with $F'\alpha(I^\bullet)$ up to
the fixed natural isomorphism; applying $\beta$ termwise to the
Cartan--Eilenberg resolution and using exactness and the acyclicity
hypotheses therefore produces a morphism of double complexes
$C^{\bullet,\bullet}\to C'^{\bullet,\bullet}$ over $X\to\alpha X$. Exactness
of $\gamma$ is used in the same way to compare the total complexes after
applying the two functors.

*Step 2: the map of spectral sequences.* A morphism of double complexes
induces a morphism of the filtered total complexes and hence, by
[thm-sp-spectral-object-yields], a morphism of the associated exact couples;
by [lem-sp-couple-morphism] it induces a morphism of the spectral sequences,
commuting with the differentials and with the page identifications, and
natural in the resolutions and hence in $X\to\alpha X$. The acyclicity
hypotheses of [def-sp-composite-acyclicity] are what identify the
$E_2$-pages of the two sequences with $R^pG(R^qF(X))$ and
$R^pG'(R^qF'(\alpha X))$, and they are preserved by exactness of the vertical
functors.

*Step 3: base change.* In the base-change situation of the
proper-base-change chapter the vertical functors are the inverse images
$g'^{-1}$, $g'^{-1}$, $g^{-1}$ along the maps of a cartesian square; these
are exact, since inverse image of sheaves is exact, and the two squares
commute by the base-change identification of the inverse images in a
cartesian square. Step 1 and Step 2 therefore apply and give the
compatibility of the Grothendieck spectral sequence with inverse image along
a base change.
