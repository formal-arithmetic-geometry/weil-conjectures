+++
id = "thm-a1-fourier-t-exact"
kind = "theorem"
title = "The Fourier transform is perverse t-exact on the line"
order = 2749
uses = ["def-per-perverse-subcategories", "def-per-support-condition", "def-fd-transform", "def-wf-tate-twist", "rem-dl-a1-conventions", "thm-a1-curve-perverse-heart", "thm-fd-fourier-perverse", "thm-fd-transform-well-defined", "lem-fd-base-change", "lem-fd-stalk-formula", "lem-zl-affine-curve-range", "lem-a1-affine-hc2", "lem-fd-as-characters", "lem-fd-cohomology-affine-line-character", "lem-fd-inversion", "prop-base-linear"]
+++
In the conventions of [rem-dl-a1-conventions], let
$\operatorname{FT}_\psi$ be the Fourier–Deligne transform of
[def-fd-transform] from the line $A_0$ to the dual line $A'_0$, and
write $\mathrm{Perv}(A_0)$, $\mathrm{Perv}(A'_0)$ for the hearts of the
perverse t-structure of [thm-a1-curve-perverse-heart], built from the
classes ${}^pD^{\le0}$, ${}^pD^{\ge0}$ of
[def-per-perverse-subcategories]. Then $\operatorname{FT}_\psi$ is
t-exact:

$$
\operatorname{FT}_\psi\bigl({}^pD^{\le0}(A_0)\bigr)\subset{}^pD^{\le0}(A'_0),
\qquad
\operatorname{FT}_\psi\bigl({}^pD^{\ge0}(A_0)\bigr)\subset{}^pD^{\ge0}(A'_0),
$$

so it sends $\mathrm{Perv}(A_0)$ into $\mathrm{Perv}(A'_0)$, and
likewise $\operatorname{FT}_{\psi^{-1}}$ (from $A'_0$ to $A_0$) is
t-exact and sends $\mathrm{Perv}(A'_0)$ into $\mathrm{Perv}(A_0)$. This
sharpens the amplitude bound $[-1,1]$ of [thm-fd-fourier-perverse] to
amplitude $0$. Moreover, with the Tate twist of [def-wf-tate-twist],
the functors

$$
\operatorname{FT}_\psi:\mathrm{Perv}(A_0)\rightleftarrows\mathrm{Perv}(A'_0):
G:=\operatorname{FT}_{\psi^{-1}}(-)(1)
$$

are mutually quasi-inverse exact equivalences of abelian categories.

## Proof

Throughout, a class is tested after the geometric base change to $k$:
cohomology sheaves commute with this pullback, supports and their
dimensions are unchanged, and the transform commutes with it by
[lem-fd-base-change]. By [thm-fd-transform-well-defined] the transform
is an exact triangulated functor with values in $D^b_c$.

*Step 0: the upper class on a curve.* On a curve every support has
dimension $\le1$, so the support condition of
[def-per-support-condition] says exactly: $K\in{}^pD^{\le0}$ if and
only if $\mathcal H^aK=0$ for $a>0$ and $\mathcal H^0K$ has finite
support. This class is stable under the shifts $[n]$, $n\ge0$, and under
extensions: for a triangle $K'\to K\to K''\to$ the long exact sequence
of cohomology sheaves gives
$\operatorname{Supp}\mathcal H^aK\subset
\operatorname{Supp}\mathcal H^aK'\cup\operatorname{Supp}\mathcal H^aK''$.
It is also stable under the twist $(1)$, which is the tensor with a
lisse sheaf of rank one and so preserves each cohomology sheaf's support.

*Step 1: $\operatorname{FT}_\psi$ preserves the upper class.* Let
$K\in{}^pD^{\le0}(A)$. The ordinary truncation triangles exhibit $K$ as
an iterated extension of $\mathcal H^0K$ (finite support, degree $0$)
and of objects $\mathcal G[m]$ with $\mathcal G=\mathcal H^{-m}K$ a
constructible sheaf and $m\ge1$. By Step 0 and exactness of the
transform it suffices to treat (a) $\mathcal G[1]$ for an arbitrary
constructible sheaf $\mathcal G$ (then $\mathcal G[m]=\mathcal G[1][m-1]$
follows), and (b) a sheaf $\mathcal G$ of finite support in degree $0$.

For a geometric point $\xi$ of $A'$ the stalk formula
[lem-fd-stalk-formula] (with $r=1$) gives

$$
\operatorname{FT}_\psi(\mathcal G)_{\xi}\cong
R\Gamma_c\bigl(A,\mathcal G\otimes\mathcal L_{\psi(\xi x)}\bigr)[1].
$$

(b) If $\mathcal G$ has finite support, so has
$\mathcal G\otimes\mathcal L_{\psi(\xi x)}$, whose compact-support
cohomology is the direct sum of its stalks, in degree $0$ (a
zero-dimensional scheme over $k$ has no higher cohomology). So every
stalk of $\operatorname{FT}_\psi(\mathcal G)$ is concentrated in degree
$-1$, and $\operatorname{FT}_\psi(\mathcal G)\in{}^pD^{\le0}(A')$ by
Step 0.

(a) For a constructible sheaf $\mathcal G$ the twisted groups
$H^i_c(A,\mathcal G\otimes\mathcal L_{\psi(\xi x)})$ vanish for
$i\notin\{0,1,2\}$ by [lem-zl-affine-curve-range], so the stalks of
$\operatorname{FT}_\psi(\mathcal G[1])$ live in degrees $-2,-1,0$, and

$$
\mathcal H^0\bigl(\operatorname{FT}_\psi(\mathcal G[1])\bigr)_{\xi}
\cong H^2_c\bigl(A,\mathcal G\otimes\mathcal L_{\psi(\xi x)}\bigr).
$$

It remains to see that this is nonzero for only finitely many $\xi$ (the
sheaf $\mathcal H^0$ being constructible, its support is then finite).
Let $j:U\hookrightarrow A$ be a dense open on which $\mathcal G$ is
lisse, with finite complement $Z$. In the sequence
$0\to j_!j^*\mathcal G\to\mathcal G\to i_*i^*\mathcal G\to0$, tensored
with the lisse $\mathcal L_{\psi(\xi x)}$, the third term has no
$H^1_c$ or $H^2_c$ (finite support, as in (b)), so

$$
H^2_c\bigl(A,\mathcal G\otimes\mathcal L_{\psi(\xi x)}\bigr)\cong
H^2_c\bigl(U,\mathcal G|_U\otimes\mathcal L_{\psi(\xi x)}|_U\bigr)
\cong\bigl(V\otimes\chi_\xi\bigr)_{\pi_1(U)}(-1)
$$

by [lem-a1-affine-hc2], where $V=\mathcal G_{\bar\eta}$ and $\chi_\xi$ is
the rank-one character of $\mathcal L_{\psi(\xi x)}|_U$. These
coinvariants are nonzero exactly when $V$ has a quotient isomorphic to
$\chi_\xi^{-1}=\chi_{-\xi}$ ([lem-fd-as-characters]:
$\mathcal L_{\psi(\xi x)}^{-1}\cong\mathcal L_{\psi(-\xi x)}$). The
characters $\chi_a$ are pairwise distinct: if $\chi_a=\chi_b$ with
$a\neq b$, then by [lem-fd-as-characters]
$\mathcal L_{\psi((a-b)x)}$ is trivial on $U$, hence on $A$ (a rank-one
lisse sheaf on the normal connected $A$ that is trivial on a dense open
is trivial, its global section extending), contradicting
$H^0(A,\mathcal L_{\psi((a-b)x)})=0$ from
[lem-fd-cohomology-affine-line-character]. If $\chi_{a_1},\dots,\chi_{a_n}$
are pairwise distinct quotients of $V$, the combined map
$V\to\bigoplus_i\chi_{a_i}$ is surjective (its image is a submodule of a
sum of pairwise non-isomorphic simple modules projecting onto each
summand, hence the whole sum), so $n\le\dim V=\operatorname{rank}\mathcal G|_U$.
Hence $\mathcal H^0\operatorname{FT}_\psi(\mathcal G[1])$ has finite
support, and $\operatorname{FT}_\psi(\mathcal G[1])\in{}^pD^{\le0}(A')$ by
Step 0. This proves
$\operatorname{FT}_\psi({}^pD^{\le0}(A))\subset{}^pD^{\le0}(A')$. The
argument uses nothing about $\psi$ beyond its nontriviality, so it
applies equally to $\operatorname{FT}_{\psi^{-1}}$ from $A'$ to $A$, and
by Step 0 also to $G=\operatorname{FT}_{\psi^{-1}}(-)(1)$.

*Step 2: $\operatorname{FT}_\psi$ is an equivalence with quasi-inverse
$G$.* Fourier inversion [lem-fd-inversion] with $r=1$ gives
$\operatorname{FT}_{\psi^{-1}}\operatorname{FT}_\psi(K)\cong K(-1)$, hence
$G\circ\operatorname{FT}_\psi\cong\mathrm{id}$; applied to the character
$\psi^{-1}$ it gives
$\operatorname{FT}_\psi\operatorname{FT}_{\psi^{-1}}(M)\cong M(-1)$, and
since the twist is the pullback of a sheaf on the base, linearity over the
base [prop-base-linear] gives
$\operatorname{FT}_\psi(M(1))\cong\operatorname{FT}_\psi(M)(1)$, so
$\operatorname{FT}_\psi\circ G\cong\mathrm{id}$.

*Step 3: the lower class.* In a t-structure, as provided by
[thm-a1-curve-perverse-heart], one has
${}^pD^{\ge0}=\{K:\operatorname{Hom}(M,K)=0\ \text{for all}\ M\in{}^pD^{\le-1}\}$.
Indeed $\subset$ is the orthogonality axiom; conversely, if $K$ is
right orthogonal to ${}^pD^{\le-1}$, the map
$\tau^{\le-1}K\to K$ in the truncation triangle
$\tau^{\le-1}K\to K\to\tau^{\ge0}K\to$ vanishes, so the triangle splits
and $\tau^{\le-1}K[1]$ is a direct summand of $\tau^{\ge0}K$; it
therefore lies in ${}^pD^{\le-2}\cap{}^pD^{\ge0}$, which is zero by
orthogonality, so $K\cong\tau^{\ge0}K$. Now let $K\in{}^pD^{\ge0}(A)$
and $M\in{}^pD^{\le-1}(A')$. By Step 2,

$$
\operatorname{Hom}\bigl(M,\operatorname{FT}_\psi K\bigr)\cong
\operatorname{Hom}\bigl(GM,K\bigr),
$$

and $GM=G(M[-1])[1]\in{}^pD^{\le-1}(A)$ by Step 1 (the classes are
compatible with shifts), so the right-hand side vanishes. Hence
$\operatorname{FT}_\psi K\in{}^pD^{\ge0}(A')$. The same argument with
the roles of $\psi,\psi^{-1}$ and of the two lines exchanged (and the
twist, which preserves ${}^pD^{\ge0}$ by the same orthogonality since
$(-1)$ is its inverse) shows that $\operatorname{FT}_{\psi^{-1}}$ and $G$
preserve ${}^pD^{\ge0}$.

*Step 4: the hearts.* By Steps 1 and 3, $\operatorname{FT}_\psi$ and $G$
are t-exact, hence restrict to functors between $\mathrm{Perv}(A_0)$ and
$\mathrm{Perv}(A'_0)$, which are quasi-inverse by Step 2. A t-exact
triangulated functor induces an exact functor on the abelian hearts of
[thm-a1-curve-perverse-heart], the short exact sequences of a heart
being the distinguished triangles with all three vertices in it. So
$\operatorname{FT}_\psi$ is an exact equivalence
$\mathrm{Perv}(A_0)\simeq\mathrm{Perv}(A'_0)$ with quasi-inverse $G$.
