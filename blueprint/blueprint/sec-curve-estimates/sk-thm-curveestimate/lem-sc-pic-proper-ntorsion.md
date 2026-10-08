+++
id = "lem-sc-pic-proper-ntorsion"
kind = "lemma"
title = "Pic of a proper curve: divisibility, n-torsion, cokernel"
order = 1023
uses = ["def-sc-curves", "def-sc-jacobian", "def-sc-mult-n", "def-sc-pic0", "lem-pc-genus-agrees-sc", "lem-sc-pic-proper-decomposition", "thm-av-final", "thm-sc-jacobian-representability"]
+++
Let $C$ be a proper smooth connected curve of
genus $g$ over algebraically closed $k$, and let $n$ be prime
to $\operatorname{char}k$. Then

$$
\operatorname{Pic}(C)[n]\cong(\mathbf Z/n\mathbf Z)^{2g},
\qquad
\operatorname{coker}\bigl(n:\operatorname{Pic}(C)\to
\operatorname{Pic}(C)\bigr)\cong\mathbf Z/n\mathbf Z,
$$

and $\operatorname{Pic}^0(C)$ is $n$-divisible.

## Proof

By [lem-sc-pic-proper-decomposition],
$\operatorname{Pic}(C)=\mathbf Z\oplus\operatorname{Pic}^0(C)$
with $\operatorname{Pic}^0(C)=J_C(k)$
([def-sc-pic0], [def-sc-jacobian],
[thm-sc-jacobian-representability]). The
group $J_C(k)$ is $n$-divisible by
[thm-av-final](d), and its $n$-torsion is
$J_C[n](k)\cong(\mathbf Z/n\mathbf Z)^{2g}$ by
[thm-av-final](c), since $\dim J_C=g$ for the genus of [def-sc-genus] by [lem-pc-genus-agrees-sc] (with
$J_C(k)[n]=J_C[n](k)$ by the definition of the kernel,
[def-sc-mult-n]). Hence

$$
\operatorname{Pic}(C)[n]=\operatorname{Pic}^0(C)[n]
\cong(\mathbf Z/n\mathbf Z)^{2g},
$$

and

$$
\operatorname{coker}(n:\operatorname{Pic}(C)\to
\operatorname{Pic}(C))=\mathbf Z/n\mathbf Z
\oplus\operatorname{coker}\bigl(n:\operatorname{Pic}^0(C)\to
\operatorname{Pic}^0(C)\bigr)=\mathbf Z/n\mathbf Z,
$$

the second summand being zero by divisibility.
