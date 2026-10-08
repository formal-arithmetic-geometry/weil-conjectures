+++
id = "lem-pc-flat-base-change-cohom"
kind = "lemma"
title = "Cohomology and flat base change"
order = 668
uses = ["def-pc-base-change", "def-pc-morphism-conventions", "def-pc-scheme", "lem-pc-affine-morphism-hi", "lem-pc-affine-vanishing", "lem-pc-cech-computes", "lem-pc-finite-support-hi", "lem-sc-cech-spectral"]
+++
Let

$$
\begin{array}{ccc}
X' & \xrightarrow{g'} & X\\[-2pt]
\downarrow{\scriptstyle f'} & & \downarrow{\scriptstyle f}\\[-2pt]
S' & \xrightarrow{g} & S
\end{array}
$$

be a cartesian diagram of schemes, let $\mathcal{F}$ be a quasi-coherent
$\mathcal{O}_X$-module with $\mathcal{F}'=(g')^*\mathcal{F}$, and assume $g$ is flat and $f$
is quasi-compact and quasi-separated. Then the base change map

$$
g^*R^if_*\mathcal{F}\;\longrightarrow\;R^if'_*\mathcal{F}'
$$

is an isomorphism for all $i\ge0$; if $S=\operatorname{Spec}(A)$, $S'=\operatorname{Spec}(B)$,
then

$$
H^i(X,\mathcal{F})\otimes_AB\;\cong\;H^i(X',\mathcal{F}')\qquad\text{for all }i .
$$

## Proof

*The affine case (2), $X$ separated.* Let $A\to B$ be flat and let
$X$ be quasi-compact and separated over $A$; choose a finite affine
open covering $\mathcal U:X=U_1\cup\dots\cup U_t$. The base changes
$(U_i)_B$ are affine and form a cover $\mathcal U_B$ of
$X_B=X\times_{\operatorname{Spec} A}\operatorname{Spec} B$ (open affine subschemes of the base
change; separability of $X_B$ follows from that of $X$), and the
intersections are affine. By [lem-pc-cech-computes],

$$
H^p(X,\mathcal{F})=\check H^p(\mathcal U,\mathcal{F}),\qquad
H^p(X_B,\mathcal{F}_B)=\check H^p(\mathcal U_B,\mathcal{F}_B).
$$

For a multi-index $J$ with $U_J=\operatorname{Spec}(C)$ and $\mathcal{F}|_{U_J}=\widetilde M$,
the base change $(U_J)_B=\operatorname{Spec}(C\otimes_AB)$ carries
$\mathcal{F}_B|=\widetilde{M\otimes_AB}$ and the localization
identifications give
$\mathcal{F}(U_J)\otimes_AB=\mathcal{F}_B((U_J)_B)$; consequently

$$
\check C^\bullet(\mathcal U_B,\mathcal{F}_B)
=\check C^\bullet(\mathcal U,\mathcal{F})\otimes_AB .
$$

For a flat ring map $A\to B$ and any complex $C^\bullet$ of
$A$-modules,

$$
H^i(C^\bullet\otimes_AB)=H^i(C^\bullet)\otimes_AB:
$$

the proof is by induction on the number of terms (via the
truncations $0\to C^{\ge n+1}\to C^{\ge n}\to C^n[-n]\to0$ and the
five-lemma applied to the long exact sequences of the short exact
sequences, both for $C^\bullet$ and for $C^\bullet\otimes_AB$ – the
base changed sequences are exact because $A\to B$ is flat, so no
$\mathrm{Tor}_1$-terms occur). Combining gives (2) for separated $X$.

*The affine case (2), $X$ quasi-separated.* Take a finite affine
open covering $\mathcal U$ of $X$ (quasi-compactness) and use the
Cech-to-cohomology spectral sequence
([lem-sc-cech-spectral]): with
$\underline H^q=\underline H^q(\mathcal{F})$,

$$
E_2^{p,q}=\check H^p(\mathcal U,\underline H^q(\mathcal{F}))
\Longrightarrow H^{p+q}(X,\mathcal{F}).
$$

The intersections $U_{i_0\dots i_p}$ are quasi-compact and separated,
so by the separated case

$$
\check H^p(\mathcal U_B,\underline H^q(\mathcal{F}_B))
=\check H^p(\mathcal U,\underline H^q(\mathcal{F}))\otimes_AB .
$$

The abutment follows from $A\to B$ flat (the spectral sequences and
their base changes are compatible in the sense that the filtration
pieces of $H^n$ base-change and are the base changes of the filtration
pieces of $H^n(X,\mathcal{F})$; the two filtrations have the same lengths and
the identification of the graded pieces gives the identification of
the filtered objects at each degree). This proves (2) in general.

*The sheaf statement (1).* The base change map is local in $S'$,
so we may assume $S'=\operatorname{Spec}(B)$; further base changing (and being
allowed to assume $S$ affine since the statement is local on both $S$
and $S'$ and $g^*R^if_*\mathcal{F}$ is the pullback of a quasi-coherent
sheaf) we may assume $S=\operatorname{Spec}(A)$. By
[lem-pc-finite-support-hi](1) the sheaves $R^if_*\mathcal{F}$ and
$R^if'_*\mathcal{F}'$ are quasi-coherent. On $S$ affine, the quasi-coherent
sheaf $R^if_*\mathcal{F}$ is $\widetilde{H^0(S,R^if_*\mathcal{F})}$ and
$H^0(S,R^if_*\mathcal{F})=H^i(X,\mathcal{F})$: this is the classical identification
(Leray: the spectral sequence
$E_2^{p,q}=H^p(S,R^qf_*\mathcal{F})\Rightarrow H^{p+q}(X,\mathcal{F})$ has
$E_2^{p,q}=0$ for $p>0$ by [lem-pc-affine-vanishing] (affine $S$)
and the quasi-coherence just noted, so it degenerates at $E_2$, giving
$H^i(X,\mathcal{F})=H^0(S,R^if_*\mathcal{F})$; this is Cohomology of Schemes,
Lemma 30.4.6, Tag [01XK](https://stacks.math.columbia.edu/tag/01XK)).
Pullback of quasi-coherent modules corresponds to $\otimes_AB$; by
(2) the two quasi-coherent $\mathcal{O}_{S'}$-modules are associated with the
same $B$-module, so the canonical base change map
(Cohomology of Schemes, Lemma 30.5.2, Tag
[02KH](https://stacks.math.columbia.edu/tag/02KH); the canonical
map of Cohomology, Lemma 20.17.1, Tag
[02N7](https://stacks.math.columbia.edu/tag/02N7)) is an
isomorphism.
