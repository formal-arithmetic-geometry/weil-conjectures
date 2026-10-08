+++
id = "lem-fd-stalk-formula"
kind = "lemma"
title = "Stalks of the transform are fibre integrals"
order = 2699
lean = ["AlgebraicGeometry.Etale.fourierTransformStalkIso"]
uses = ["def-fd-kernel", "def-fd-transform", "def-weil-pbc-qbar-category", "thm-cbc-finite-extension", "thm-cbc-qbar"]
+++
Let $S=\operatorname{Spec}k$, $V\cong\mathbf A^r_k$, let $\bar\xi:\operatorname{Spec}\Omega\to V^\vee$ be a geometric point of $V^\vee$ with $\Omega$ algebraically closed, and let $K\in D^b_c(V,E)$. Write $V_{\bar\xi}=(V\times_kV^\vee)\times_{p_2,V^\vee}\bar\xi=V\times_k\Omega$ for the fibre of $p_2$ over $\bar\xi$ (it is $V_{\bar k}$ when $\bar\xi$ is a $\bar k$-point of $V^\vee$; for $\bar\xi$ over a non-closed point it is the affine $r$-space over $\Omega\supset\kappa(\bar\xi)$). Then

$$
(\operatorname{FT}_\psi(K))_{\bar\xi}\cong H^*_c\bigl(V_{\bar\xi},\,K|_{V_{\bar\xi}}\otimes^L\mathcal L_{\psi(\langle x,\xi\rangle)}\bigr)[r],
$$

where $\langle x,\xi\rangle:V_{\bar\xi}\to\mathbf A^1$ is the pairing with the point $\xi$.

## Proof

Form the cartesian square with $g=\bar\xi:\operatorname{Spec}\Omega\to V^\vee$ and $p_2:V\times_kV^\vee\to V^\vee$. Its base change $p_2':V_{\bar\xi}\to\operatorname{Spec}\Omega$ is the structure morphism of $V_{\bar\xi}\cong\mathbf A^r_\Omega$, and $g':V_{\bar\xi}\to V\times_kV^\vee$ is $(\mathrm{pr}_V,\bar\xi)$. The stalk at $\bar\xi$ of a complex on $V^\vee$ is its inverse image along $g$, so the compact-support base change of [thm-cbc-finite-extension] at the $E$-stage (or of [thm-cbc-qbar] in the $\overline{\mathbf Q}_\ell$-form of the coefficient category of [def-weil-pbc-qbar-category]), applied to this square and to $p_1^*K\otimes^L\mathcal K_\psi\in D^b_c(V\times_kV^\vee,E)$, gives

$$
\bigl(Rp_{2!}(p_1^*K\otimes^L\mathcal K_\psi)\bigr)_{\bar\xi}
=Lg^*Rp_{2!}(p_1^*K\otimes^L\mathcal K_\psi)
\cong Rp'_{2!}\,Lg'^*(p_1^*K\otimes^L\mathcal K_\psi)
=R\Gamma_c\bigl(V_{\bar\xi},\,g'^*(p_1^*K\otimes^L\mathcal K_\psi)\bigr).
$$

Here $g'^*p_1^*K=K|_{V_{\bar\xi}}$, and $g'^*\mathcal K_\psi=g'^*b^*\mathcal L_\psi$ is the Artin–Schreier sheaf of the function $b\circ g'=\langle x,\xi\rangle$ on $V_{\bar\xi}$, because the base change of the twist is the twist by the base-changed function ([def-fd-kernel]): the inverse image of $\mathcal L_{\psi,f}$ along a morphism $h$ is $\mathcal L_{\psi,f\circ h}$, the Artin–Schreier covering being compatible with base change. With the shift $[r]$ of [def-fd-transform], this is the displayed formula. (The base change used is the proper, compact-support one along $\bar\xi\to V^\vee$, not smooth base change. If one passes instead through the strict henselization $\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{V^\vee,\bar\xi}$, the kernel on $V\times_k\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{V^\vee,\bar\xi}$ is $\mathcal L_{\psi(\langle x,\xi_{\mathrm{univ}}\rangle)}$ for the tautological point $\xi_{\mathrm{univ}}$, not the pullback of $\mathcal L_{\psi(\langle x,\xi\rangle)}$ from $V_{\bar\xi}$, and the passage to the closed fibre is again this compact-support base change.)
