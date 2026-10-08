+++
id = "sk-thm-frobenius"
kind = "section"
title = "Frobenius: equivariance, similitudine, reciprocity"
order = 2445
uses = ["sk-def-pairing", "sk-def-sf-orientation", "sk-def-weil", "sk-thm-derived-duality"]
+++
*Theorem (sketch).*

In the setting of [sk-def-weil] ($X_0$ need not be proper),
for a strict Weil complex $K$ perfect over $\Lambda_X$:

**(a)** *Equivariance and similitude, at every coefficient stage.* At every
stage $\Lambda\in\{\AEn,\Oe,E,\Qlb\}$ the derived pairing $\beta_K$ of
[sk-def-pairing] is a morphism of Weil objects, so the induced degreewise
pairing satisfies
$\langle F_{c,K}x,F_{K^\vee(d)}y\rangle_i=\langle x,y\rangle_i$, and the
untwisted line-valued pairing satisfies

$$
\langle F_{c,K}x,F_{K^\vee}y\rangle_i^{\mathrm{untw}}
=q^d\langle x,y\rangle_i^{\mathrm{untw}}.
$$

These are identities between bilinear maps and use no nondegeneracy.

**(b)** *Reciprocity, at the field stages.* If moreover $\Lambda$ is a field
coefficient stage in the sense of [sk-thm-derived-duality] (in practice
$\Lambda\in\{E,\Qlb\}$), so that the degreewise pairings are perfect, then
$F_{K^\vee}$ is conjugate to $q^d(F_{c,K}^{-1})^{\mathsf t}$ on the
finite-dimensional space $H^{2d-i}(X,K^\vee)$, so the eigenvalues of $F$ on
$H^{2d-i}(X,K^\vee)$ are the $q^d/\alpha$ with the multiplicities of the
eigenvalues $\alpha$ on $H^i_c(X,K)$ (for proper $X$, $H^i_c=H^i$).

Clause (b) is false at the integral stage $\Lambda=\Oe$: for
$X_0=\Spec\Fq$, $d=0$, and the perfect complex
$K=[\Oe\xrightarrow{\varpi_E}\Oe]$ in degrees $-1,0$ with the identity
Weil datum, $H^0(K)=\Oe/\varpi_E$ while $H^0(K^\vee)=0$ and
$H^1(K^\vee)=\Oe/\varpi_E$; the degreewise form of the duality is not
perfect there ([sk-thm-sf-identification]), the missing information being
carried by an $\operatorname{Ext}^1$ term.
(Blueprint 15, thm:pod-equivariance-of-the-twisted-pairing,
cor:pod-untwisted-similitude,
cor:pod-reciprocal-eigenvalues.)

## Proof

*Step 1 (each ingredient is equivariant).* The mixed-support cup
product is induced by the tensor product of complexes and its
$\Gamma_c$-realization, both of which are lifted to Weil complexes by the
functoriality built into [sk-def-weil]; the evaluation is a morphism of
Weil objects; and the orientation of [sk-def-sf-orientation] is
Frobenius-equivariant, by the Weil equivariance of purity and trace
(thm:pur-weil-equivariance-of-purity-and-trace, whose target datum on
the coefficient ring is the canonical one).
*Step 2 (the pairing is a morphism of Weil objects).* Composing, the
triple $\bigl(\RGammac(X,K),\RGamma(X,K^\vee(d))[2d],\Lambda\bigr)$ carries
the Weil data $\varphi_{c,K}$, $\varphi_{K^\vee(d)}$ and the canonical
data, and $\beta_K$ is a morphism of Weil objects from the tensor of the
first two to the last. Evaluated on the tensor of two vectors this reads
$\langle F_{c,K}x,F_{K^\vee(d)}y\rangle_i=F(\langle x,y\rangle_i)$; the
target datum is the canonical one, so $F$ acts on $\Lambda$ as the
identity by [sk-def-weil], which is the equivariance clause. Nothing
here depends on the coefficient stage: the identity holds for the
$\Lambda$-bilinear map induced by $\beta_K$ on cohomology at every
$\Lambda\in\{\AEn,\Oe,E,\Qlb\}$.
*Step 3 (eliminating the twist).* The second factor is
$H^{2d-i}(X,K^\vee)\otimes\Lambda(d)$, and
$\varphi_{K^\vee(d)}=\varphi_{K^\vee}\otimes\tau_d$, where $\tau_d$ is
the scalar $q^{-d}$ on the twist line; writing $y=y_0\otimes\xi_d$ under
that identification turns the identity of Step 2 into

$$
\langle F_{c,K}x,F_{K^\vee}y_0\rangle_i^{\mathrm{untw}}
=q^d\,\langle x,y_0\rangle_i^{\mathrm{untw}},
$$

because the untwisted pairing is a morphism into the value line
$\Lambda(-d)$ and $F$ acts on $\Lambda(-d)$ by $q^d$ by the
normalization of [sk-def-weil].
*Step 4 (reciprocity, field stages only).* This is the one step that
needs a field stage. Over a field coefficient stage the degreewise pairing is
perfect by [sk-thm-derived-duality], so the adjoint
$\Phi:H^{2d-i}(X,K^\vee)\to H^i_c(X,K)^\vee$, $\Phi(y)(x)=\langle
x,y\rangle_i^{\mathrm{untw}}$, is an isomorphism of finite-dimensional
vector spaces, and the similitude of Step 3 reads
$\Phi\circ F_{K^\vee}=q^d(F_{c,K}^{-1})^{\mathsf t}\circ\Phi$; hence
$F_{K^\vee}$ is conjugate to $q^d(F_{c,K}^{-1})^{\mathsf t}$. The
characteristic polynomial is invariant under transposition, so the
eigenvalues of $F$ on $H^{2d-i}(X,K^\vee)$ are the $q^d/\alpha$, with the
multiplicities of the eigenvalues $\alpha$ of $F$ on $H^i_c(X,K)$.
Over $\Oe$ the adjoint $\Phi$ is not an isomorphism in general (only the
derived duality holds, [sk-thm-sf-identification]), and the example in the
statement shows that (b) genuinely fails there; the derived equivariance of
Step 2 is all that survives at that stage. (The conjugacy alone holds
whenever the degreewise pairing is perfect, e.g. over $\AEn$ for proper
$X$ by [sk-thm-sf-identification], since $\Phi$ is then an
isomorphism of $\Lambda$-modules.) No step uses properness. These are
thm:pod-equivariance-of-the-twisted-pairing,
cor:pod-untwisted-similitude and cor:pod-reciprocal-eigenvalues.

Uses: [sk-def-pairing], [sk-def-sf-orientation], [sk-def-weil], [sk-thm-derived-duality]
