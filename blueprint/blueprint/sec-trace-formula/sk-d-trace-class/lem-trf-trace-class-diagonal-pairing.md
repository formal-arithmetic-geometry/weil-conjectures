+++
id = "lem-trf-trace-class-diagonal-pairing"
kind = "lemma"
title = "The trace class is the diagonal supported pairing"
order = 2318
uses = ["def-sf-kv-maps", "def-trf-admissibility", "def-trf-correspondence", "def-trf-dualizing-complex", "def-trf-fixed-scheme", "def-trf-supported-pairing", "def-trf-trace-class", "def-trf-trace-class-source", "def-weil-derived-pullback-tensor-hom", "lem-trf-correspondence-class", "lem-trf-exceptional-internal-hom-exchange", "lem-trf-trace-map-from-external-duality", "prop-functor-package", "prop-trf-exceptional-kunneth", "thm-trf-dualizing-complex-composition", "thm-trf-fixed-point-base-change", "thm-trf-kunneth-verdier", "thm-trf-verdier-duality"]
+++
Fix the coefficient conventions, $A=A_{E,n}$, $s=\Spec k$, let
$c=(c_1,c_2):C\to X\times_sX$ be an admissible correspondence
([def-trf-correspondence]) with fixed scheme $F=\Fix(c)$ and fixed-square
maps $i_F:F\to C$, $d:F\to X$ ([def-trf-fixed-scheme]), let
$K\in D^b_{ctf}(X,A)$ and $u:Lc_2^*K\to Rc_1^!K$. Assume the exceptional
admissibility ([def-trf-admissibility]) required by
[def-trf-supported-pairing] for the diagonal opposite pair
$(C,c,u)$, $(X,\Delta_X,1_K)$ and by
[lem-trf-trace-map-from-external-duality]. Then the Borel–Moore section
of the diagonal pair ([def-trf-supported-pairing]) is the Verdier trace
class of [def-trf-trace-class]:

$$
\langle u,1_K\rangle_{\mathrm{LV}}=\Tr_c(u)
\qquad\text{in }\Hom_{D(F,A)}(A_F,\omega_{F,A}).
$$

The equality holds exactly, with no sign and no twist: both sides are
the exceptional adjoint, along $d$, of the class of $u$ read through the
Künneth–Verdier isomorphism, base changed to the diagonal and evaluated.

## Proof

*Notation.* Put $Z=X\times_sX$ with projections $p_1,p_2$, diagonal
$\Delta=\Delta_X$ (a closed immersion, $X$ being separated), factor
exchange $\tau$ (so $\tau\Delta=\Delta$, $p_i\tau=p_{3-i}$), and
$e:=c\,i_F=\Delta d:F\to Z$. All pullbacks and tensor products are
derived ([def-weil-derived-pullback-tensor-hom]). Put $D:=D_XK$,
$\omega=\omega_{X,A}$, and

$$
P:=K\boxtimes_A^{\mathrm L}D=Lp_1^*K\otimes_A^{\mathrm L}Lp_2^*D,
\qquad
e':L\Delta^*P=K\otimes_A^{\mathrm L}D\xrightarrow{\ \mathrm{sym}\ }
D\otimes_A^{\mathrm L}K\xrightarrow{\operatorname{ev}_K}\omega ,
$$

with $\operatorname{ev}_K$ the evaluation of [def-trf-dualizing-complex]
and $\mathrm{sym}$ the symmetry with its Koszul signs; the map
$e_K:P\to R\Delta_*\omega$ of
[lem-trf-trace-map-from-external-duality] is the
$L\Delta^*\dashv R\Delta_*$ adjoint of $e'$. For an exceptionally
admissible $f$ write
$\operatorname{adj}_f:\Hom(Rf_!M,N)\cong\Hom(M,Rf^!N)$. The
identifications $\omega\cong R\Delta^!\omega_Z$,
$\omega_{F,A}\cong Rd^!\omega$ and $\omega_{F,A}\cong Re^!\omega_Z$ are
those of [thm-trf-dualizing-complex-composition]; by its compatibility
with further compositions, the last is the composite of the first two
with $Re^!\cong Rd^!R\Delta^!$. In the diagonal case of
[def-trf-supported-pairing] one has $(Y,L)=(X,K)$, $\bar d=\Delta$,
$E=F$, $e_C=i_F$, $e_D=d$, and the Künneth–Verdier isomorphism used there
is $\kappa:=\kappa_{K,K}:P\xrightarrow{\sim}\RHom_A(Lp_2^*K,Rp_1^!K)$ of
[thm-trf-kunneth-verdier]. Let

$$
\widetilde u:=\kappa^{-1}\circ[u]:Rc_!A_C\longrightarrow P
$$

be the supported class of $u$ (Step 1 there, with $[u]$ from
[lem-trf-correspondence-class]), and let $\widetilde u_{\mathrm{tr}}:A_C\to
\mathcal H_c(K)$ be the mate of $u$ from
[def-trf-trace-class-source].

*Step 1 (both constructions start from $\widetilde u$).* Let
$\xi:\mathcal H_c(K)\xrightarrow{\sim}Rc^!P$ be the comparison of
[thm-trf-verdier-duality]: the exchange
$\mathcal H_c(K)=\RHom_A(Lc^*Lp_2^*K,Rc^!Rp_1^!K)\cong
Rc^!\RHom_A(Lp_2^*K,Rp_1^!K)$ of
[lem-trf-exceptional-internal-hom-exchange], followed by
$Rc^!\kappa^{-1}$. We claim

$$
\xi\circ\widetilde u_{\mathrm{tr}}=\operatorname{adj}_c(\widetilde u).
\tag{1}
$$

The exchange is defined by the Yoneda chain of
[lem-trf-exceptional-internal-hom-exchange]; evaluated on the test
object $A_C$ that chain reads
$\Hom_C(A_C,\mathcal H_c(K))\cong\Hom_C(Lc^*M,Rc^!N)\cong
\Hom_Z(Rc_!A_C\otimes M,N)\cong\Hom_Z(Rc_!A_C,\RHom_A(M,N))\cong
\Hom_C(A_C,Rc^!\RHom_A(M,N))$ with $M=Lp_2^*K$, $N=Rp_1^!K$, using
$A_C\otimes Lc^*M=Lc^*M$. Its first arrow is the mate bijection of
[def-trf-trace-class-source], and its middle arrows are, in reverse,
exactly the tensor–Hom, projection-formula and exceptional-adjunction
steps whose composite defines $[u]$ in [lem-trf-correspondence-class]
(with the same identifications $Lc_2^*=Lc^*Lp_2^*$,
$Rc_1^!=Rc^!Rp_1^!$). Hence the exchange sends $\widetilde u_{\mathrm{tr}}$
to $\operatorname{adj}_c([u])$, and by naturality of $\operatorname{adj}_c$
in its target, $Rc^!\kappa^{-1}\circ\operatorname{adj}_c([u])
=\operatorname{adj}_c(\kappa^{-1}[u])$, which is (1).

*Step 2 (the trace class).* Let
$bc:L\Delta^*Rc_!\xrightarrow{\sim}Rd_!Li_F^*$ be the base change of
[thm-trf-fixed-point-base-change] (2), and put

$$
h:\;Rd_!A_F=Rd_!Li_F^*A_C\xrightarrow{\ bc^{-1}\ }
L\Delta^*Rc_!A_C\xrightarrow{\ L\Delta^*\widetilde u\ }L\Delta^*P
\xrightarrow{\ e'\ }\omega .
$$

We claim $\Tr_c(u)=\operatorname{adj}_d(h)$, read through
$Rd^!\omega\cong\omega_{F,A}$. By [def-trf-trace-class] and naturality of
the global-sections adjunction (with
$R\Gamma(C,Ri_{F*}-)=R\Gamma(F,-)$), $\Tr_c(u)$ is the
$Li_F^*\dashv Ri_{F*}$ adjoint of $\varphi\circ\widetilde u_{\mathrm{tr}}:
A_C\to Ri_{F*}\omega_{F,A}$, where $\varphi$ is the objectwise map of
[lem-trf-trace-map-from-external-duality]:
$\varphi=(\text{composition})\circ BC\circ Rc^!e_K\circ\xi$, with
$BC:Rc^!R\Delta_*\cong Ri_{F*}Rd^!$ the right-adjoint form of $bc$. By
(1), $Rc^!e_K\circ\xi\circ\widetilde u_{\mathrm{tr}}
=\operatorname{adj}_c(g)$ with $g:=e_K\circ\widetilde u:Rc_!A_C\to
R\Delta_*\omega$. That $BC$ is the right-adjoint form of $bc$ (its
compatibility with the adjunction data, [thm-trf-fixed-point-base-change])
means precisely: for every $g:Rc_!M\to R\Delta_*N$, the $i_F$-adjoint of
$BC\circ\operatorname{adj}_c(g)$ is
$\operatorname{adj}_d(g^\flat\circ bc^{-1}):Li_F^*M\to Rd^!N$, where
$g^\flat:L\Delta^*Rc_!M\to N$ is the $L\Delta^*\dashv R\Delta_*$ adjoint
of $g$. Here $g^\flat=e'\circ L\Delta^*\widetilde u$, since $e_K$ is the
adjoint of $e'$; so $g^\flat\circ bc^{-1}=h$, which is the claim.

*Step 3 (pairing with the diagonal class).* Let
$\widetilde v:R\Delta_!A_X\to Q=D\boxtimes_A^{\mathrm L}K$ be the
supported class of $(X,\Delta,1_K)$ in [def-trf-supported-pairing]: it is
$\widetilde v=s\circ\tau_*\widetilde v'$ with
$\widetilde v':=\kappa^{-1}\circ[1_K]:R\Delta_!A_X\to P$ and
$s:\tau_*P\cong Q$ the symmetry. Let
$\gamma=\alpha\circ(\operatorname{ev}_K\boxtimes\operatorname{ev}_K)\circ
\mathrm{rearr}:P\otimes Q\to\omega_Z$ be the contraction of Step 3 there.
We claim

$$
\gamma\circ(1_P\otimes\widetilde v)
=\varepsilon_\Delta\circ R\Delta_!(e')\circ\pi_P,
\tag{2}
$$

where $\pi_P:P\otimes R\Delta_!A_X\cong R\Delta_!L\Delta^*P$ is the
projection formula ([prop-functor-package] (5), after the symmetry, which
is sign-free because $R\Delta_!A_X$ is a sheaf in degree $0$) and
$\varepsilon_\Delta:R\Delta_!\omega\cong R\Delta_!R\Delta^!\omega_Z\to
\omega_Z$ is the counit. Equivalently (by projection formula and
$\operatorname{adj}_\Delta$), the $\Delta$-adjoint
$L\Delta^*P\to R\Delta^!\omega_Z\cong\omega$ of the left side is $e'$.

(3a) By [lem-trf-correspondence-class] for $c=\Delta$ (both legs
$\operatorname{id}_X$), the tensor–Hom transpose
$[1_K]^T:R\Delta_!A_X\otimes Lp_2^*K\to Rp_1^!K$ is, after
$R\Delta_!A_X\otimes Lp_2^*K\cong R\Delta_!K$, the $\Delta$-adjoint of the
composition isomorphism $K\cong R\Delta^!Rp_1^!K$; equivalently, under
the adjunction for $p_1\Delta=\operatorname{id}_X$, it corresponds to
$1_K$, i.e. $\varepsilon_{p_1}\circ Rp_{1!}[1_K]^T=1_K$ on
$Rp_{1!}R\Delta_!K=K$.

(3b) By [def-sf-kv-maps] (iii), (iv), the transpose
$\kappa^T:P\otimes Lp_2^*K\to Rp_1^!K$ of $\kappa$ is
$Lp_1^*K\otimes Lp_2^*(D\otimes K)\xrightarrow{1\otimes Lp_2^*\operatorname{ev}_K}
K\boxtimes\omega\xrightarrow{\alpha_{\operatorname{id},a_X}}Rp_1^!K$ (the
other evaluation is the unit identification $\RHom_A(A_X,K)=K$, and moving
the unit $A_X$ costs no sign), with $\alpha_{\operatorname{id},a_X}$ the
exceptional Künneth map of [prop-trf-exceptional-kunneth] for
$p_1=\operatorname{id}_X\times a_X$. So $\kappa\circ\widetilde v'=[1_K]$
transposes to

$$
\alpha_{\operatorname{id},a_X}\circ(1\otimes Lp_2^*\operatorname{ev}_K)
\circ(\widetilde v'\otimes 1_{Lp_2^*K})=[1_K]^T .
\tag{3}
$$

(3c) Let $\varpi:Lp_1^*D\otimes Rp_1^!K\to Rp_1^!\omega\cong\omega_Z$ be
the $p_1$-adjoint of
$Rp_{1!}(Lp_1^*D\otimes Rp_1^!K)\cong D\otimes Rp_{1!}Rp_1^!K
\xrightarrow{1\otimes\varepsilon_{p_1}}D\otimes K
\xrightarrow{\operatorname{ev}_K}\omega$. Apply the autoequivalence
$\tau^*$ ($\tau^*R\Delta_!A_X=R\Delta_!A_X$,
$\tau^*\omega_Z\cong\omega_Z$): the left side of (2) becomes
$\gamma^\tau\circ(1\otimes\widetilde v')$ with
$\gamma^\tau:=\tau^*\gamma\circ(1\otimes\tau^*s):\tau^*P\otimes P\to
\omega_Z$, where $\tau^*P=Lp_2^*K\otimes Lp_1^*D$. Then

$$
\gamma^\tau=\varpi\circ(1_{Lp_1^*D}\otimes\kappa^T)\circ r,
\qquad
r:\tau^*P\otimes P\cong Lp_1^*D\otimes(P\otimes Lp_2^*K)
$$

the symmetry-constraint permutation. Both sides contract the factor-one
$D$ with the factor-one $K$ and the factor-two $D$ with the factor-two
$K$ by $\operatorname{ev}_K$, and then identify the result with
$\omega_Z$; they agree because $\alpha_{a_X,a_X}$ factors as
$\alpha_{\operatorname{id},a_X}$ (for $L_1=\omega$) followed by
$Rp_1^!\omega=Rp_1^!Ra_X^!A_s\cong Ra_Z^!A_s$ (both are exceptional
adjoints of $\mathrm{Ku}_!$ followed by counits, [def-sf-kv-maps] (i),
(ii), and $\mathrm{Ku}_!$ is compatible with composition and with the
exchange of factors), because $\alpha_{\operatorname{id},a_X}$ is natural
in $L_1$ and compatible with $Lp_1^*D\otimes(-)$ through the projection
formula (which is how $\varpi$ is built), and because all permutations
used are symmetry constraints with Koszul signs, so two composites
inducing the same permutation of the same factors coincide (coherence of
the symmetric monoidal structure, [prop-functor-package], final clause).

(3d) By (3c), naturality of $r$, and (3),

$$
\gamma^\tau\circ(1\otimes\widetilde v')
=\varpi\circ(1_{Lp_1^*D}\otimes[1_K]^T)\circ r',
\qquad
r':\tau^*P\otimes R\Delta_!A_X\cong
Lp_1^*D\otimes(R\Delta_!A_X\otimes Lp_2^*K).
$$

Take $\Delta$-adjoints. Since $\tau\Delta=\Delta$ and $p_i\Delta=\operatorname{id}$,
$L\Delta^*\tau^*P=K\otimes D$ and $L\Delta^*r'$ is $\mathrm{sym}:K\otimes
D\cong D\otimes K$. The map
$\varpi\circ(1\otimes[1_K]^T):R\Delta_!(D\otimes K)\cong
Lp_1^*D\otimes R\Delta_!K\to\omega_Z\cong Rp_1^!\omega$ corresponds, under
the adjunction for $p_1\Delta=\operatorname{id}_X$, to
$D\otimes K\xrightarrow{1\otimes\varepsilon_{p_1}Rp_{1!}[1_K]^T}D\otimes K
\xrightarrow{\operatorname{ev}_K}\omega$ (definition of $\varpi$ and
naturality of the projection formula), which is $\operatorname{ev}_K$ by
(3a). Hence the $\Delta$-adjoint of $\tau^*$ of the left side of (2) is
$\operatorname{ev}_K\circ\mathrm{sym}=e'$; as $\tau^*$ commutes with the
$\Delta$-adjunction ($\tau$ an automorphism with $\tau\Delta=\Delta$), so
is that of the left side itself. This proves (2).

*Step 4 (the supported pairing).* By [def-trf-supported-pairing], with
$\mu:Re_!A_F\cong Rc_!A_C\otimes R\Delta_!A_X$,

$$
\sigma_{u,1_K}=\gamma\circ(\widetilde u\otimes\widetilde v)\circ\mu
=\gamma\circ(1_P\otimes\widetilde v)\circ(\widetilde u\otimes1)\circ\mu
=\varepsilon_\Delta\circ R\Delta_!\bigl(e'\circ L\Delta^*\widetilde u\bigr)
\circ\pi_{Rc_!A_C}\circ\mu
$$

by (2) and naturality of the projection formula. The isomorphism $\mu$
is built from the projection formula for $c$ and the base change along
$c$ in the fixed square; the isomorphism
$R\Delta_!(bc^{-1})\circ(Re_!\cong R\Delta_!Rd_!):Re_!A_F\cong
R\Delta_!L\Delta^*Rc_!A_C$ is built from the base change along $\Delta$
in the same Cartesian square. By the coherence of the composition,
base-change and projection-formula isomorphisms ([prop-functor-package]
(3)–(5) and its final clause) the isomorphism
$Re_!A_F\cong Rc_!A_C\otimes R\Delta_!A_X$ does not depend on which leg
of the square is used, i.e.
$\pi_{Rc_!A_C}\circ\mu=R\Delta_!(bc^{-1})\circ(Re_!\cong R\Delta_!Rd_!)$.
Therefore

$$
\sigma_{u,1_K}=\varepsilon_\Delta\circ R\Delta_!(h)\circ
(Re_!A_F\cong R\Delta_!Rd_!A_F).
$$

The adjunction $Re_!\dashv Re^!$ is the composite of those for $\Delta$
and $d$ (this is how $Re^!\cong Rd^!R\Delta^!$ is defined), and
$\operatorname{adj}_\Delta(\varepsilon_\Delta\circ R\Delta_!h)=h$
(followed by $\omega\cong R\Delta^!\omega_Z$). Hence
$\operatorname{adj}_e(\sigma_{u,1_K})=\operatorname{adj}_d(h)$ under
$Re^!\omega_Z\cong Rd^!R\Delta^!\omega_Z\cong Rd^!\omega$, and by the
compatibility recalled in the notation paragraph,
$\langle u,1_K\rangle_{\mathrm{LV}}=\operatorname{adj}_d(h)$ read through
$Rd^!\omega\cong\omega_{F,A}$. By Step 2 this is $\Tr_c(u)$.
