+++
id = "lem-fd-constituent-nonexceptional-concentration"
kind = "lemma"
title = "Concentration of the zero-extension transform for a constituent-nonexceptional input"
order = 2775
uses = ["def-a1-constituent-nonexceptional", "def-fd-kernel", "def-fd-transform", "def-wf-constant-weil-twist", "def-wf-fundamental-representation", "lem-a1-affine-hc0", "lem-a1-affine-hc2", "lem-fd-as-characters", "lem-fd-realified-kernel-real", "lem-fd-stalk-formula", "lem-zl-affine-curve-range", "prop-functor-package", "rem-dl-a1-conventions"]
+++
In the conventions of [rem-dl-a1-conventions], let
$j:U_0\hookrightarrow\mathbf A^1_{k_0}$ be a dense open immersion with
$U_0=\mathbf A^1_{k_0}\setminus S_0$, and let $\mathcal M$ be a nonzero
irreducible lisse Weil sheaf on $U_0$ which is
constituent-nonexceptional in the sense of
[def-a1-constituent-nonexceptional]. No unramifiedness at infinity and
no geometric irreducibility is assumed.

1. For every $a\in k$ the twisted compact-support cohomology is
   concentrated in degree one:
   $$
   H^q_c\bigl(U,\,\mathcal M\otimes\mathcal L_{\psi(ax)}|_U\bigr)=0
   \qquad(q\neq1).
   $$
2. For every $b\in\Qlb^\times$ the twisted dual
   $\mathcal M^\dagger:=\mathcal M^\vee\otimes\mathcal B_b$, with the
   constant Weil twist of [def-wf-constant-weil-twist], is again a
   nonzero irreducible lisse Weil sheaf on $U_0$ which is
   constituent-nonexceptional.
3. The Fourier–Deligne transforms $\operatorname{FT}_\psi(j_!\mathcal M)$
   and $\operatorname{FT}_{\psi^{-1}}(j_!\mathcal M^\dagger)$ of
   [def-fd-transform] are concentrated in degree $0$. If moreover
   $\mathcal M$ is punctually $\iota$-pure of weight $w$ and
   $\mathcal K$ is the realified kernel of [lem-fd-realified-kernel-real]
   (formed with $\iota(b)=q^w$), then
   $$
   R^\nu p_{2,!}\mathcal K=0\qquad(\nu\neq1),
   $$
   and $\operatorname{FT}_\psi(j_!\mathcal M)$ is a direct summand of the
   sheaf $R^1p_{2,!}\mathcal K$.

## Proof

(1) Fix $a\in k$ and put
$\mathcal F_a:=\mathcal M\otimes\mathcal L_{\psi(ax)}|_U$, a lisse sheaf
on the smooth geometrically connected affine curve
$U=U_0\otimes_{k_0}k$; it is defined, with its Weil structure, over the
finite extension $k_0(a)$ of $k_0$, and we apply the following curve
results over that finite field. By [lem-zl-affine-curve-range] only
$q\in\{0,1,2\}$ can contribute. By [lem-a1-affine-hc0],
$H^0_c(U,\mathcal F_a)=0$. By [lem-a1-affine-hc2],

$$
H^2_c(U,\mathcal F_a)\simeq
\bigl(V\otimes L_a\bigr)_{\pi_1(U)}(-1),
\qquad V=\mathcal M_{\bar\eta},\quad
L_a=\bigl(\mathcal L_{\psi(ax)}\bigr)_{\bar\eta},
$$

the coinvariants for the geometric monodromy of
[def-wf-fundamental-representation]. Suppose these coinvariants are
nonzero. Then there is a nonzero $\pi_1(U)$-equivariant linear map
$V\otimes L_a\to\Qlb$ to the trivial module. Tensoring with the
rank-one module $L_a^{-1}$, which is the generic fibre of
$\mathcal L_{\psi(-ax)}$ by
$(\mathcal L_{\psi,f})^{-1}\cong\mathcal L_{\psi,-f}$ of
[lem-fd-as-characters], gives a nonzero equivariant map
$V\to L_a^{-1}$. Its target is one-dimensional, so the map is
surjective, and refining $0\subset\ker\subset V$ to a composition
series shows that $\mathcal L_{\psi(-ax)}|_U$ is a geometric irreducible
constituent of $\mathcal M$. This is excluded by
[def-a1-constituent-nonexceptional] (with $-a\in k$; the case $a=0$ is
the trivial constituent). Hence $H^2_c(U,\mathcal F_a)=0$, and only
$q=1$ survives.

(2) The dual of an irreducible representation of the Weil group of
$U_0$ is irreducible, and twisting by the character through which the
constant twist $\mathcal B_b$ acts preserves irreducibility; so
$\mathcal M^\dagger$ is a nonzero irreducible lisse Weil sheaf. After
geometric base change $\mathcal B_b$ becomes trivial, so the geometric
fundamental representation of $\mathcal M^\dagger$ is the
$\pi_1(U)$-module $V^\vee$. If
$0=V_0\subset V_1\subset\cdots\subset V_n=V$ is a composition series,
the annihilators
$V_{n-i}^\perp\subset V^\vee$ form a composition series of $V^\vee$
with graded pieces $(V_{n-i+1}/V_{n-i})^\vee$; so the geometric
irreducible constituents of $\mathcal M^\dagger$ are the duals of those
of $\mathcal M$. If one of them were
$\mathcal L_{\psi(ax)}|_U$, its dual
$\mathcal L_{\psi(-ax)}|_U$ ([lem-fd-as-characters]) would be a
geometric constituent of $\mathcal M$, which is excluded. So
$\mathcal M^\dagger$ is constituent-nonexceptional.

(3) Let $\bar\xi$ be a geometric point of the dual line, i.e.
$\xi\in k$. The stalk formula [lem-fd-stalk-formula] (with $r=1$)
gives

$$
\bigl(\operatorname{FT}_\psi(j_!\mathcal M)\bigr)_{\bar\xi}
\cong H^*_c\bigl(\mathbf A^1_k,\,j_!\mathcal M\otimes\mathcal L_{\psi(\xi x)}\bigr)[1]
=H^*_c\bigl(U,\,\mathcal M\otimes\mathcal L_{\psi(\xi x)}|_U\bigr)[1],
$$

the tensor product with the lisse rank-one kernel being exact and the
compact-support cohomology of an extension by zero being that of the
open curve. By (1) with $a=\xi$ this is concentrated in degree
$1-1=0$. The same formula for the character $\psi^{-1}$, whose
Artin–Schreier sheaf is
$\mathcal L_{\psi^{-1}(\xi x)}=\mathcal L_{\psi(-\xi x)}$ by
[lem-fd-as-characters], together with (1) applied to
$\mathcal M^\dagger$ (legitimate by (2)) with $a=-\xi$, shows that
$\operatorname{FT}_{\psi^{-1}}(j_!\mathcal M^\dagger)$ is concentrated
in degree $0$. Since this holds at every geometric point, both
transforms are sheaves.

Now let $\mathcal M$ be pure of weight $w$ and let $\mathcal K$ be the
realified kernel of [lem-fd-realified-kernel-real], the direct sum of
$p_1^*(j_!\mathcal M)\otimes^L\mathcal K_\psi$ and
$p_1^*(j_!\mathcal M^\dagger)\otimes^L\mathcal K_{\psi^{-1}}$ with the
kernels of [def-fd-kernel]. By [def-fd-transform] the direct images
under $p_{2,!}$ of the two summands are
$\operatorname{FT}_\psi(j_!\mathcal M)[-1]$ and
$\operatorname{FT}_{\psi^{-1}}(j_!\mathcal M^\dagger)[-1]$, which by
what was just shown are concentrated in degree $1$. The
compact-support direct image is an exact triangulated functor by
[prop-functor-package], hence additive, so
$R^\nu p_{2,!}\mathcal K=0$ for $\nu\neq1$ and

$$
R^1p_{2,!}\mathcal K\cong\operatorname{FT}_\psi(j_!\mathcal M)\oplus
\operatorname{FT}_{\psi^{-1}}(j_!\mathcal M^\dagger),
$$

exhibiting $\operatorname{FT}_\psi(j_!\mathcal M)$ as a direct summand.
