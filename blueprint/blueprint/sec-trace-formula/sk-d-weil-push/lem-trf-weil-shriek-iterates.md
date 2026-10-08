+++
id = "lem-trf-weil-shriek-iterates"
kind = "lemma"
title = "Iterates of the Weil $!$-pushforward"
order = 2365
uses = ["d-relative-frob", "def-exchange-projection", "def-trf-frobenius-coefficient-morphism", "def-trf-weil-shriek-pushforward", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "fix-lem-exchanges", "prop-functor-package"]
+++
In the setting of [def-trf-weil-shriek-pushforward], let
$K\in D^b_{ctf}(X,A)$ and $m,n\geq1$.

1. *Base-change composition.* After the pullback composition
identifications $L\Phi^{(m+n)*}\simeq L\Phi^{m*}L\Phi^{n*}$ on $X$
and on $Y$,
$$
\theta_{f,m+n,K}=\theta_{f,m,L\Phi_X^{n*}K}\circ
L\Phi_Y^{m*}\theta_{f,n,K}:
L\Phi_Y^{(m+n)*}Rf_!K\longrightarrow Rf_!L\Phi_X^{(m+n)*}K .
$$
1. *Iterates.* Let $u:L\Phi_X^*K\to K$ be a Frobenius coefficient
morphism, with iterates $u_m$ of
[def-trf-frobenius-coefficient-morphism], and let
$\psi=Rf_!u\circ\theta_{f,1}$ be the Weil $!$-pushforward. Then the
iterates $\psi_m$ of the Frobenius coefficient morphism $\psi$ on
$Rf_!K$ satisfy
$$
\psi_m=Rf_!u_m\circ\theta_{f,m}\qquad(m\geq1).
$$

Neither statement uses invertibility of $u$.

## Proof

*Step 1: factorizing the relative Frobenius.* Paste the Cartesian
square defining $X'_n$ of [d-relative-frob] with the Cartesian
square obtained by pulling $f'_n:X'_n\to Y$ back along $\Phi_Y^m$.
Since $\Phi_Y^n\Phi_Y^m=\Phi_Y^{m+n}$, the outer rectangle identifies
$$
X'_{m+n}=Y\times_{\Phi_Y^m,Y,f'_n}X'_n,
\qquad f'_{m+n}=\text{first projection},\qquad
p_{m+n}=p_nq,
$$
where $q:X'_{m+n}\to X'_n$ is the second projection. On test points,
$(y,x)\in X'_m$ means $\Phi_Y^my=f(x)$, and
$t(y,x)=(y,r_n(x))=(y,(f(x),\Phi_X^nx))$ defines a map
$t:X'_m\to X'_{m+n}$. The square
$$
\begin{array}{ccc}
X'_m&\xrightarrow{\ p_m\ }&X\\
{\scriptstyle t}\downarrow&&\downarrow{\scriptstyle r_n}\\
X'_{m+n}&\xrightarrow{\ q\ }&X'_n
\end{array}
$$
is Cartesian: a point of the fiber product is $(y,(y',x'),x)$ with
$(y',x')=(f(x),\Phi_X^nx)$, which is exactly a point $(y,x)$ of
$X'_m$. Moreover $f'_{m+n}t=f'_m$, and
$$
tr_m(x)=(f(x),(f(x),\Phi_X^{m+n}x))=r_{m+n}(x),
$$
so $r_{m+n}=t\circ r_m$, with $t$ finite as a base change of $r_n$.

*Step 2: the comparison.* Put $M=L\Phi_X^{n*}K=Lr_n^*Lp_n^*K$.
Expand the right-hand side of (1) using the three arrows of
[def-trf-weil-shriek-pushforward]. The second factor is
$L\Phi_Y^{m*}$ of $\operatorname{Ex}_!$ for the $\Phi_Y^n$-square,
followed by $L\Phi_Y^{m*}Rf'_{n!}(\eta_{r_n})$ and the composition
identification $Rf'_{n!}Rr_{n*}\simeq Rf_!$. For the first factor,
write the Cartesian square of $f$ along $\Phi_Y^m$ as the vertical
pasting of the $t$-square above and the square of $f'_n$ along
$\Phi_Y^m$. By the pasting identity and the compatibility with the
composition law of [fix-lem-exchanges], clauses (2) and (4), its
$\operatorname{Ex}_!$ is the $\operatorname{Ex}_!$ for $f'_n$ followed
by the exchange for $r_n$ along $q$. The latter is the ordinary
exchange $\operatorname{Ex}_*:Lq^*Rr_{n*}\to Rt_*Lp_m^*$ of
[def-exchange-projection], because $r_n$ is proper and one may use
the trivial compactification; it is invertible by proper base change
([prop-functor-package], clause (4)).

By naturality of $\operatorname{Ex}_!$ in the coefficient complex
([fix-lem-exchanges], clause (1)), move
$\operatorname{Ex}_!$ for $f'_n$ past $\eta_{r_n}$. The two
exchanges for the $\Phi_Y^n$- and $\Phi_Y^m$-squares then paste, by
[fix-lem-exchanges], clause (2), to the exchange for the outer
rectangle, which is the first arrow of $\theta_{f,m+n}$. What remains
on $N=Lp_{m+n}^*K=Lq^*Lp_n^*K$ is
$$
N\xrightarrow{Lq^*\eta_{r_n}}Lq^*Rr_{n*}Lr_n^*Lp_n^*K
\xrightarrow{\operatorname{Ex}_*}Rt_*Lp_m^*Lr_n^*Lp_n^*K
\simeq Rt_*Lt^*N
\xrightarrow{Rt_*\eta_{r_m}Lt^*}Rt_*Rr_{m*}Lr_m^*Lt^*N .
$$
By the definition of $\operatorname{Ex}_*$ as the adjoint of the
counit composite in [def-exchange-projection], and the triangle
identities of $Lr_n^*\dashv Rr_{n*}$ of
[def-weil-derived-direct-image], the composite of the first two
arrows is the unit $\eta_t$ at $N$, after $Lp_m^*Lr_n^*\simeq
Lt^*Lq^*$ from $r_np_m=qt$
([def-weil-derived-pullback-tensor-hom]). The unit of the composite
adjunction for $r_{m+n}=tr_m$ is $Rt_*\eta_{r_m}Lt^*\circ\eta_t$.
Hence the displayed composite is $\eta_{r_{m+n}}$ at $N$. Finally,
all remaining arrows are composition identifications for $Rh_!$ and
$Lh^*$ ([prop-functor-package], clause (3), and
[def-weil-derived-pullback-tensor-hom]), which are coherent for
$f'_{m+n}tr_m=f$ and $p_nqtr_m=\Phi_X^{m+n}$. Therefore the
right-hand side of (1) equals the defining composite of
$\theta_{f,m+n,K}$, proving (1).

*Step 3: iterates.* For $m=1$, $\psi_1=\psi=Rf_!u\circ\theta_{f,1}$
is the definition. Assume the formula for $m$. By
[def-trf-frobenius-coefficient-morphism],
$\psi_{m+1}=\psi\circ L\Phi_Y^*\psi_m$ after the pullback
composition identification. Thus
$$
\psi_{m+1}=Rf_!u\circ\theta_{f,1,K}\circ L\Phi_Y^*Rf_!u_m
\circ L\Phi_Y^*\theta_{f,m,K}.
$$
Naturality of $\theta_{f,1}$ in $K$
([def-trf-weil-shriek-pushforward]) gives
$\theta_{f,1,K}\circ L\Phi_Y^*Rf_!u_m
=Rf_!L\Phi_X^*u_m\circ\theta_{f,1,L\Phi_X^{m*}K}$. Hence
$$
\psi_{m+1}=Rf_!(u\circ L\Phi_X^*u_m)\circ
\theta_{f,1,L\Phi_X^{m*}K}\circ L\Phi_Y^*\theta_{f,m,K}
=Rf_!u_{m+1}\circ\theta_{f,m+1,K},
$$
using the recursive definition of $u_{m+1}$ in
[def-trf-frobenius-coefficient-morphism] and (1) with the pair
$(1,m)$. This proves (2) by induction.
