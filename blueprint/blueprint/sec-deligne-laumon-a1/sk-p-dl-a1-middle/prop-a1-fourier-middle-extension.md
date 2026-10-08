+++
id = "prop-a1-fourier-middle-extension"
kind = "theorem"
tags = ["latex:proposition"]
title = "Fourier transform of an irreducible middle extension"
order = 2755
uses = ["def-a1-constituent-nonexceptional", "def-fd-kernel", "def-fd-transform", "def-per-perverse-subcategories", "def-wf-middle-extension", "def-wf-tate-twist", "lem-fd-as-characters", "lem-fd-base-change", "lem-fd-first-formula", "lem-fd-inversion", "prop-a1-curve-perverse-simples", "prop-base-linear", "rem-dl-a1-conventions", "thm-a1-curve-perverse-heart", "thm-a1-fourier-t-exact"]
lean = ["AlgebraicGeometry.exists_middleExtension_fourierTransform"]
+++
In the conventions of [rem-dl-a1-conventions], let
$j:U_0\hookrightarrow A_0$ be a dense open immersion and let
$\mathcal M$ be a nonzero irreducible lisse Weil sheaf on $U_0$ which is
constituent-nonexceptional in the sense of
[def-a1-constituent-nonexceptional]. Then there are a dense open
immersion $j':U'_0\hookrightarrow A'_0$ into the dual line and a nonzero
irreducible lisse Weil sheaf $\mathcal M'$ on $U'_0$ such that the
Fourier–Deligne transform of [def-fd-transform] of the middle extension
of [def-wf-middle-extension] satisfies

$$
\operatorname{FT}_\psi\bigl((j_*\mathcal M)[1]\bigr)\cong
(j'_*\mathcal M')[1].
$$

## Proof

Write $\mathrm{Perv}(A_0)$ and $\mathrm{Perv}(A'_0)$ for the perverse
hearts of [def-per-perverse-subcategories] on the two lines. We use three
facts about these hearts.

- **(H1)** The two perverse classes form a t-structure whose heart is
  abelian, with the sheaf-level description on a curve
  ([thm-a1-curve-perverse-heart]).
- **(H2)** $\operatorname{FT}_\psi$ is t-exact: it sends
  $\mathrm{Perv}(A_0)$ into $\mathrm{Perv}(A'_0)$, and
  $\operatorname{FT}_{\psi^{-1}}$ sends $\mathrm{Perv}(A'_0)$ into
  $\mathrm{Perv}(A_0)$ ([thm-a1-fourier-t-exact]).
- **(H3)** The simple objects of the curve heart are the punctual
  $i_{x*}E$, with $x$ a closed point and $E$ an irreducible Weil module
  at $x$ placed in degree $0$, and the $(j_*\mathcal N)[1]$, with
  $\mathcal N$ a nonzero irreducible lisse Weil sheaf on a dense open;
  each of these is simple ([prop-a1-curve-perverse-simples]).

*Step 1: the transform is simple.* By (H3),
$P:=(j_*\mathcal M)[1]$ is a simple object of $\mathrm{Perv}(A_0)$, and
by (H2) $\operatorname{FT}_\psi(P)$ lies in $\mathrm{Perv}(A'_0)$. Put
$G:=\operatorname{FT}_{\psi^{-1}}(-)(1)$, using the Tate twist of
[def-wf-tate-twist]. Fourier inversion [lem-fd-inversion] with $r=1$
gives $\operatorname{FT}_{\psi^{-1}}\operatorname{FT}_\psi(K)\cong K(-1)$,
hence $G\circ\operatorname{FT}_\psi\cong\operatorname{id}$. Applied to the
character $\psi^{-1}$ it gives
$\operatorname{FT}_\psi\operatorname{FT}_{\psi^{-1}}(M)\cong M(-1)$, and
the Tate-twist clause of base linearity [prop-base-linear] (the twist
being the pullback of the twisting object of the base) gives
$\operatorname{FT}_\psi\bigl(\operatorname{FT}_{\psi^{-1}}(M)(1)\bigr)\cong
\operatorname{FT}_\psi\operatorname{FT}_{\psi^{-1}}(M)(1)\cong M$, i.e.
$\operatorname{FT}_\psi\circ G\cong\operatorname{id}$. Hence
$\operatorname{FT}_\psi(P)\neq0$.

By (H2) both functors are exact functors between the abelian hearts of
(H1). Let $0\neq Q\subsetneq\operatorname{FT}_\psi(P)$ be a proper
nonzero subobject. Then $G(Q)\to G\operatorname{FT}_\psi(P)\cong P$ is a
monomorphism. Its source $G(Q)$ is nonzero, and its cokernel
$G\bigl(\operatorname{FT}_\psi(P)/Q\bigr)$ is nonzero, because
$\operatorname{FT}_\psi\circ G\cong\operatorname{id}$ detects zero
objects. This contradicts the simplicity of $P$. So
$\operatorname{FT}_\psi(P)$ is simple, and by (H3) it is either
punctual or of the form $(j'_*\mathcal M')[1]$, with $\mathcal M'$
nonzero, irreducible and lisse on a dense open $U'_0$.

*Step 2: transforms of punctual objects.* Let $\xi\in k$ and let
$\delta_\xi$ be the skyscraper sheaf $\overline{\mathbf Q}_\ell$ at
$\xi$ on the geometric dual line $A'$, in degree $0$. We claim

$$
\operatorname{FT}_{\psi^{-1}}(\delta_\xi)\cong\mathcal L_{\psi(-\xi x)}[1]
\quad\text{on }A.
$$

The case $\xi=0$ is the second formula of [lem-fd-first-formula], and
the general case uses the same computation. In the transform from $A'$
to $A$, the pullback of $\delta_\xi$ along the first projection is
supported on $\{\xi\}\times A$. The second projection restricts to an
isomorphism from this line onto $A$. On the line, the kernel of
[def-fd-kernel] for the character $\psi^{-1}$ restricts to
$\mathcal L_{\psi^{-1}(\xi x)}$. By [lem-fd-as-characters] this is
$\mathcal L_{\psi^{-1},\xi x}\cong\mathcal L_{\psi,-\xi x}
=\mathcal L_{\psi(-\xi x)}$. The compactly supported direct image
along an isomorphism is the sheaf itself, and the shift $[1]$ of
[def-fd-transform] gives the claim.

*Step 3: the punctual case is excluded.* Suppose
$\operatorname{FT}_\psi(P)\cong i_{x*}E$ is punctual. Apply $G$ and use
Step 1:

$$
(j_*\mathcal M)[1]\cong\operatorname{FT}_{\psi^{-1}}(i_{x*}E)(1).
$$

Pass to the geometric base change, which commutes with the transform by
[lem-fd-base-change]. After this base change, $i_{x*}E$ becomes a
finite direct sum of copies of skyscrapers $\delta_\xi$ at the geometric
points $\xi$ over $x$. The Tate twist becomes trivial. So Step 2 gives

$$
(j_*\mathcal M)_{\bar k}[1]\cong
\bigoplus_{\xi}\mathcal L_{\psi(-\xi x)}^{\oplus n_\xi}[1],
\qquad\text{hence}\qquad
\mathcal M_{\bar k}\cong\bigoplus_\xi
\bigl(\mathcal L_{\psi(-\xi x)}|_U\bigr)^{\oplus n_\xi}
$$

after restriction to $U$, using $j^*j_*\mathcal M=\mathcal M$. Since
$\mathcal M\neq0$, some $n_\xi>0$. Every geometric irreducible
constituent of $\mathcal M$ is then some $\mathcal L_{\psi(ax)}|_U$
with $a=-\xi\in k$, where $a=0$ is allowed. This contradicts
constituent-nonexceptionality in [def-a1-constituent-nonexceptional].

Therefore $\operatorname{FT}_\psi\bigl((j_*\mathcal M)[1]\bigr)$ is a
simple object of the second kind in (H3), which is the assertion.

The hypothesis is needed. Conversely, the transform of a linear
character is punctual: for $a=0$, $\operatorname{FT}_\psi$ of the
constant sheaf is $\delta_0(-1)[-1]$ by [lem-fd-first-formula]. Hence
an input with an exceptional geometric constituent can have a punctual
simple constituent in its transform.
