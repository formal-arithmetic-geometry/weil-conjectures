+++
id = "thm-trf-coefficient-morphism-trace-formula"
kind = "theorem"
title = "Trace formula for Frobenius coefficient morphisms over a finite ring"
order = 2379
uses = ["d-lines", "d-relative-frob", "def-trf-admissibility", "def-trf-categorical-trace", "def-trf-coefficient-conventions", "def-trf-frobenius-coefficient-morphism", "def-trf-weil-shriek-pushforward", "def-weil-finite-field-fiber", "def-weil-pbc-etale-origin-witness", "def-weil-scheme-morphism-properties", "fix-lem-finite-tor-perfect", "i-relative-frob", "i-topology", "lem-sf-proetale-constructible-origin", "lem-trf-chain-supertrace", "lem-trf-compactification-cohomology", "lem-trf-compactification-graph-operator", "lem-trf-global-operator-perfect", "lem-trf-weil-shriek-operator-fibres", "prop-trf-graph-operator", "prop-trf-trace-additivity-open-closed", "prop-trf-trace-formal-laws", "rem-ptr-trf-admissibility-12", "thm-sf-preservation-class", "thm-trf-frobenius-fixed-points", "thm-trf-frobenius-local-term", "thm-trf-lefschetz-verdier"]
+++
Fix the global finite-field datum $p,a,q,k_0,k$, where $q=p^a$, and
the coefficient conventions, $A=A_{E,n}$. Let $X_0$ be a separated
finite-type $k_0$-scheme, put $X=X_0\times_{k_0}k$, let
$K\in D^b_{ctf}(X,A)$ have an explicit etale-origin witness, and let
$\psi:L\Phi^*K\to K$ be a Frobenius coefficient morphism of
[def-trf-frobenius-coefficient-morphism], with iterates $\psi_m$ and
global operators $F_{c,m}(\psi)$; no invertibility of $\psi$ is
assumed. Assume the exceptional-adjoint admissibility hypotheses of
[def-trf-admissibility] for the graph correspondences and fixed-point
base changes on a chosen compactification defined over $k_0$, as in
the Grothendieck–Lefschetz formula over a finite ring below (at the
finite stage these hold automatically, and the proof does not use
them). For
$y\in X_0(\mathbf F_{q^m})$ with geometric point $\bar y$ one has
$\Phi^m\bar y=\bar y$ (the fixed points of
[thm-trf-frobenius-fixed-points]), and $\psi_m$ induces a stalk
endomorphism
$\psi_{m,\bar y}:K_{\bar y}\cong(L\Phi^{m*}K)_{\bar y}\to K_{\bar y}$.
Then for every $m\geq1$

$$
\boxed{
\operatorname{tr}_A\bigl(F_{c,m}(\psi)\mid R\Gamma_c(X,K)\bigr)
=\sum_{y\in X_0(\mathbf F_{q^m})}
\operatorname{tr}_A\bigl(\psi_{m,\bar y}\mid K_{\bar y}\bigr)
}
$$

in $A$, both sides being categorical traces of endomorphisms of
perfect complexes. This is the coefficient-morphism variant of the
finite-coefficient trace formula; for the scheme-Frobenius map
$\psi=u_1$ of a strict Weil complex it gives the
Grothendieck–Lefschetz formula over a finite ring, which is deduced from
it below. It is the form needed
when an integral lift of a field-stage Weil isomorphism is not itself
invertible.

## Proof

The traces are defined: $R\Gamma_c(X,K)$ is perfect and
$F_{c,m}(\psi)$ is a morphism of $D^b_{\mathrm{fin}}(A)$ by
[lem-trf-global-operator-perfect], and the stalks are perfect by
[fix-lem-finite-tor-perfect].

The proof reduces to curves, as in the sketch: closed subschemes of
the affine line first, then affine schemes by fibring over an affine
space with the Weil $!$-pushforward, then general schemes by
localization. No compactification of $X_0$ is used, and the
admissibility hypothesis of the statement is not needed.

*Step 0: conventions.* For $r\geq1$ the finite-field datum
$(p,a,q,k_0,k)$ may be replaced by $(p,ar,q^r,\mathbf F_{q^r},k)$
([def-weil-finite-field-fiber]); every result cited below is stated for
an arbitrary datum. For a finite field $F$ of characteristic $p$, a
separated finite-type $F$-scheme $S_0$ with $S=S_0\times_Fk$, a complex
$K\in D^b_{ctf}(S,A)$ and a Frobenius coefficient morphism $\psi$ on
$K$ for the $|F|$-power scheme Frobenius $\Phi_S$, and $m\geq1$, write
$\mathrm{TF}(S_0,K,\psi,m)$ for the identity
$$
\operatorname{tr}_A\bigl(F_{c,m}(\psi)\mid R\Gamma_c(S,K)\bigr)
=\sum_{s\in S_0(F_m)}\operatorname{tr}_A\bigl(\psi_{m,\bar s}\mid K_{\bar s}\bigr),
$$
where $F_m\subseteq k$ is the extension of degree $m$ of $F$. Every
complex in $D^b_{ctf}$ has an explicit étale-origin witness
([lem-sf-proetale-constructible-origin]), and every separated
finite-type morphism between separated finite-type $k$-schemes is
exceptionally admissible at the finite stage
([rem-ptr-trf-admissibility-12], [thm-sf-preservation-class]). We prove
$\mathrm{TF}$ for all such data; the theorem is the case
$(F,S_0)=(k_0,X_0)$.

*Step 1: finite schemes.* Let $S_0$ be finite over $F$. Then $S$ is
finite over $k$, hence a finite disjoint union
$S=\coprod_{\bar s\in S(k)}S_{\bar s}$ of spectra of local Artinian
$k$-algebras with residue field $k$. The inclusion
$\iota_{\bar s}:\operatorname{Spec}k\to S_{\bar s}$ is a finite
universal homeomorphism, so by [i-topology]
$K|_{S_{\bar s}}\simeq R\iota_{\bar s*}K_{\bar s}$ and
$R\Gamma_c(S,K)=R\Gamma(S,K)\simeq\bigoplus_{\bar s}K_{\bar s}$, a finite
sum of perfect complexes ([fix-lem-finite-tor-perfect]). Put
$\Phi=\Phi_S^m$; it is a universal homeomorphism, so it permutes the
points $\bar s$, and $(L\Phi^*K)_{\bar s}=K_{\Phi(\bar s)}$. By
[prop-trf-graph-operator],
$F_{c,m}(\psi)=R\Gamma(S,\psi_m)\circ\Phi^\sharp$, where $\Phi^\sharp$ is
induced by the unit of $L\Phi^*\dashv R\Phi_*$; on these decompositions
$\Phi^\sharp$ maps the summand $K_{\Phi(\bar s)}$ identically onto the
summand $(L\Phi^*K)_{\bar s}$, and $R\Gamma(S,\psi_m)$ is the sum of
the stalk maps. Hence $F_{c,m}(\psi)$ is the block matrix whose only
nonzero blocks are $\psi_{m,\bar s}:K_{\Phi(\bar s)}\to K_{\bar s}$. Choosing
bounded complexes of finite projective $A$-modules for the $K_{\bar s}$
and chain representatives of the blocks, the chain-level supertrace of
[lem-trf-chain-supertrace] only sees the diagonal blocks, those with
$\Phi(\bar s)=\bar s$. By [thm-trf-frobenius-fixed-points] these are the
geometric points of $S_0(F_m)$, and there the block is the stalk map
$\psi_{m,\bar s}$. This is $\mathrm{TF}(S_0,K,\psi,m)$.

*Step 2: the affine line.* Let $S_0=\mathbf A^1_F$ and let
$j_0:\mathbf A^1_F\hookrightarrow\mathbf P^1_F$ be the compactification of
[d-lines], proper ([Stacks, Tag 0FMG](https://stacks.math.columbia.edu/tag/0FMG))
and smooth of pure dimension one
([Stacks, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)), with complement
the rational point $\infty$. Let $\bar\psi$ be the extension of $\psi$ to
$j_!K$ of [lem-trf-compactification-graph-operator], with iterates
$\bar\psi_m=\overline{\psi_m}$ (item (1)). By item (3) of that lemma the
isomorphism $C_{j,K}$ of [lem-trf-compactification-cohomology] conjugates
$F_{c,m}(\psi)$ into $T_{\bar c}(\bar\psi_m)$ on
$R\Gamma(\mathbf P^1,j_!K)$, where $\bar c=(\operatorname{id},\bar\Phi^m)$ is the
graph on $\mathbf P^1$, so the traces agree by conjugacy invariance
([prop-trf-trace-formal-laws], item (1)). On the proper curve
$\mathbf P^1$ the ordinary leg $\bar\Phi^m$ is finite and, by
[thm-trf-frobenius-fixed-points], the fixed scheme is finite over $k$
with one reduced point component for each point of
$\mathbf P^1_F(F_m)$. The Lefschetz–Verdier comparison
[thm-trf-lefschetz-verdier], which assembles the proper global
comparison and the decomposition into local terms, gives
$$
\operatorname{tr}_A\bigl(T_{\bar c}(\bar\psi_m)\mid R\Gamma(\mathbf P^1,j_!K)\bigr)
=\sum_{y\in\mathbf P^1_F(F_m)}\operatorname{LT}_y(\bar\psi_m).
$$
By the coefficient-morphism form of [thm-trf-frobenius-local-term] on the
smooth curve $\mathbf P^1$ (proved there through the curve pieces),
$\operatorname{LT}_y(\bar\psi_m)=\operatorname{tr}_A(\bar\psi_{m,\bar y}\mid(j_!K)_{\bar y})$.
By [lem-trf-compactification-graph-operator], item (2), the stalk at
$\infty$ is zero, so its local term is zero, and for
$y\in\mathbf A^1_F(F_m)$ one has $(j_!K)_{\bar y}=K_{\bar y}$ and
$\bar\psi_{m,\bar y}=\psi_{m,\bar y}$. This is
$\mathrm{TF}(\mathbf A^1_F,K,\psi,m)$.

*Step 3: closed subschemes of the affine line.* A closed subscheme of
$\mathbf A^1_F$ is $\operatorname{Spec}F[t]/I$. If $I=0$ it is the line,
Step 2. Otherwise a nonzero polynomial in $I$ makes $F[t]/I$
finite-dimensional over $F$, and Step 1 applies. This includes
nonreduced schemes.

*Step 4: affine schemes.* We prove $\mathrm{TF}$ for all closed
subschemes $S_0\subseteq\mathbf A^d_F$, by induction on $d$,
simultaneously for all finite fields $F$, all $K$, all $\psi$ and all
$m$. The cases $d\leq1$ are Steps 1 and 3. Let $d\geq2$ and let
$f_0:S_0\to Y_0=\mathbf A^{d-1}_F$ forget the last coordinate, a
separated morphism. Let $(L,\psi')=(Rf_!K,Rf_!\psi\circ\theta_{f,1})$
be the Weil $!$-pushforward of [def-trf-weil-shriek-pushforward]; its
comparison $\theta_{f,1}$ is built from the relative Frobenius
factorization [d-relative-frob] and is invertible because $r_1$ is a
finite universal homeomorphism ([i-relative-frob], [i-topology]), and
$L\in D^b_{ctf}(Y,A)$. By [lem-trf-weil-shriek-operator-fibres],
item (1), the compact global operator $F_{c,m}(\psi')$ is conjugate to
$F_{c,m}(\psi)$, and the induction hypothesis for $Y_0$ gives
$$
\operatorname{tr}_A\bigl(F_{c,m}(\psi)\mid R\Gamma_c(S,K)\bigr)
=\sum_{y\in Y_0(F_m)}\operatorname{tr}_A\bigl(\psi'_{m,\bar y}\mid L_{\bar y}\bigr).
$$
By item (2) of that lemma, $\psi'_{m,\bar y}$ is conjugate to the
degree-one compact Frobenius operator $F_{c,1}(\psi_m|_{\bar y})$ of the
fibre $S_{0,y}$, considered over $F_m$ with the one-step coefficient
morphism $\psi_m|_{\bar y}$. The fibre is a closed subscheme of
$\mathbf A^1_{F_m}$, so Step 3 over $F_m$ gives
$$
\operatorname{tr}_A\bigl(\psi'_{m,\bar y}\mid L_{\bar y}\bigr)
=\sum_{s\in S_{0,y}(F_m)}\operatorname{tr}_A\bigl(\psi_{m,\bar s}\mid K_{\bar s}\bigr),
$$
using item (3) for the stalk maps. Summing over $y$ and using the
disjoint union of item (3) gives $\mathrm{TF}(S_0,K,\psi,m)$.

*Step 5: general schemes.* Let $S_0$ be separated of finite type over
$F$, choose a finite affine open cover $U_1,\ldots,U_N$, and put
$W_i=U_1\cup\cdots\cup U_i$, $V_i=W_i\setminus W_{i-1}$. Each $V_i$ is
closed in the affine $U_i$, hence affine of finite type and a closed
subscheme of some $\mathbf A^d_F$, and $V_i$ is the closed complement of
the open $W_{i-1}$ in $W_i$. By item (3) of
[prop-trf-trace-additivity-open-closed], applied to
$W_{i-1}\subseteq W_i$ with the restricted coefficient morphisms, whose
iterates and stalk maps are the restrictions of those of $\psi$,
$$
\operatorname{tr}_A\bigl(F_{c,m}\mid R\Gamma_c(W_i)\bigr)
=\operatorname{tr}_A\bigl(F_{c,m}\mid R\Gamma_c(W_{i-1})\bigr)
+\operatorname{tr}_A\bigl(F_{c,m}\mid R\Gamma_c(V_i)\bigr).
$$
By induction on $i$ and Step 4 for the $V_i$, the trace on
$R\Gamma_c(S,K)$ is the sum over $i$ of the point sums over
$V_i(F_m)$. These sets partition $S_0(F_m)$, which gives
$\mathrm{TF}(S_0,K,\psi,m)$ and proves the theorem.
