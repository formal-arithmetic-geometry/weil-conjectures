+++
id = "sk-thm-fourier-trace-formula"
kind = "section"
title = "P8: the Fourier trace formula"
order = 2706
uses = ["sk-def-ft", "sk-def-trace", "sk-lem-as-properties", "sk-prop-stalk"]
+++
*Theorem (sketch).*

For $y\in\mathbf F_{q^n}$ and a Weil complex $K$ on $\Aone$,

$$
t_{\FT_\psi(K)}(y)
=-\sum_{x\in\mathbf F_{q^n}}t_K(x)\,\psi\bigl(\Tr_{\mathbf F_{q^n}/k_0}(xy)\bigr).
$$

Thus, up to the sign coming from the shift $[1]$, the trace function of the
transform is the classical Fourier transform of the trace function of the
input. (Blueprint thm:fd-fourier-trace.)

## Proof

By P3 the stalk of $\FT_\psi(K)$ at the geometric point over $y$ is
$H^*_c(\Aone,K\otimes^L\mathcal L_{\psi(xy)})[1]$. The
Grothendieck–Lefschetz trace formula over $\mathbf F_{q^n}$
(thm:trf-grothendieck-lefschetz-qbar in the point-counting form
cor:trf-point-counting) computes the trace of the Frobenius on that
complex as the sum of the traces at the geometric points of the fibre, i.e. as $-\sum_xt_{K\otimes^L\mathcal L_{\psi(xy)}}(x)$, the sign being the shift
$[1]$ of [sk-def-ft]. The trace of a tensor product is the product of the
traces, and the trace of the Artin–Schreier factor at $x$ is
$\psi(\Tr_{\mathbf F_{q^n}/k_0}(xy))$ by [sk-lem-as-properties].

Uses: [sk-def-ft], [sk-def-trace], [sk-lem-as-properties], [sk-prop-stalk]
