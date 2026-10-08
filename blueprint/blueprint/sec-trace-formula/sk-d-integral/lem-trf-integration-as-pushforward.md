+++
id = "lem-trf-integration-as-pushforward"
kind = "lemma"
title = "Integration is pushforward to the point"
order = 2284
uses = ["def-trf-borel-moore-pushforward", "def-trf-dualizing-complex", "def-trf-integration", "thm-trf-dualizing-complex-composition"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, $s=\Spec k$, and let $T$ be
separated finite type
and proper over $s$
with exceptionally admissible
structure morphism $a_T:T\to s$. Identify
$\omega_s=Ra_s^!A_s=A_s$ ($a_s=\operatorname{id}_s$) and
$\End_{D(s,A)}(A_s)=\End_{D(A)}(A)=A$ via $R\Gamma(s,-)$. Then for
every Borel–Moore section $\alpha:A_T\to\omega_T$ of
[def-trf-borel-moore-pushforward],

$$
\int_T\alpha=(a_T)_*\alpha\in A,
$$

where $\int_T$ is the integration of [def-trf-integration] and
$(a_T)_*$ the pushforward of [def-trf-borel-moore-pushforward]
along the proper morphism $h=a_T:T\to T'=s$.

## Proof

Take $h=a_T$, $T'=s$ in [def-trf-borel-moore-pushforward]. Then
$\omega_{T'}=Ra_s^!A_s=A_s$ by [def-trf-dualizing-complex], and the
isomorphism $Ra_T^!\omega_s\xrightarrow{\sim}\omega_T$ of
[thm-trf-dualizing-complex-composition] (with $d=a_T$, $X=s$) is the
identity of $Ra_T^!A_s=\omega_T$, since the composition isomorphism
$Ra_T^!R\operatorname{id}_s^!\cong Ra_T^!$ for the identity is the
identity by the unit coherence of the exchange data. Hence
$(a_T)_*\alpha$ is the composite

$$
A_s\xrightarrow{\eta_{a_T}}Ra_{T*}A_T
\xrightarrow{Ra_{T*}\alpha}Ra_{T*}\omega_T
\cong Ra_{T!}Ra_T^!A_s\xrightarrow{\varepsilon_{a_T}}A_s .
$$

Applying the $A$-linear equivalence
$R\Gamma(s,-):D(s,A)\to D(A)$ ($k$ algebraically closed) term by
term, the first arrow becomes the map $\eta^*$ of
[def-trf-integration] (composed with $Ra_{T*}\cong Ra_{T!}$, which
commutes with $Ra_{T*}\alpha\leftrightarrow Ra_{T!}\alpha$ by
naturality of that identification), the second becomes
$R\Gamma(\tau)$ with $\tau=\alpha$, and the last becomes
$\varepsilon_{a_\beta}$ with $\beta=T$. So the two composites
$A\to A$ agree, i.e. $\int_T\alpha=(a_T)_*\alpha$ under
$\End_{D(A)}(A)=A$.
