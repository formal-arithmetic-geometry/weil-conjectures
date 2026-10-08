+++
id = "def-trf-borel-moore-pushforward"
kind = "definition"
title = "Borel–Moore sections and their proper pushforward"
order = 2282
uses = ["def-compact-support-direct-image-detailed", "def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-dualizing-complex", "def-weil-derived-direct-image", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties", "thm-trf-dualizing-complex-composition"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, $s=\Spec k$. Let $T$ be a
separated finite-type
$k$-scheme whose structure morphism $a_T:T\to s$ is
exceptionally admissible, with
dualizing complex $\omega_T=\omega_{T,A}=Ra_T^!A_s$ of
[def-trf-dualizing-complex]. A *Borel–Moore section* on $T$ is a
morphism

$$
\alpha:A_T\longrightarrow\omega_T
$$

in $D(T,A)$; they form the $A$-module
$\Hom_{D(T,A)}(A_T,\omega_T)$.

Let $h:T\to T'$ be a proper
morphism of such $k$-schemes, with $h$, $a_T$ and $a_{T'}$
exceptionally admissible (so $a_T=a_{T'}\circ h$). For a
Borel–Moore section $\alpha$ on $T$, its *pushforward*
$h_*\alpha:A_{T'}\to\omega_{T'}$ is the composite

$$
A_{T'}\xrightarrow{\ \eta_h\ }Rh_*A_T
\xrightarrow{\ Rh_*\alpha\ }Rh_*\omega_T
\xrightarrow{\ \sim\ }Rh_!Rh^!\omega_{T'}
\xrightarrow{\ \varepsilon_h\ }\omega_{T'},
$$

where:

- $\eta_h$ is the unit of the adjunction $Lh^*\dashv Rh_*$ of the
  derived direct image at
  $A_{T'}$, using $Lh^*A_{T'}=A_T$;
- the isomorphism is the identification $Rh_*\cong Rh_!$ for the
  proper $h$ of [def-compact-support-direct-image-detailed],
  followed by $Rh_!$ applied to the inverse of the canonical
  isomorphism $Rh^!\omega_{T'}\xrightarrow{\sim}\omega_T$ of
  [thm-trf-dualizing-complex-composition] (applied with $d=h$,
  $X=T'$, $F=T$);
- $\varepsilon_h$ is the counit of the adjunction
  $Rh_!\dashv Rh^!$ of [def-trf-admissibility] at $\omega_{T'}$.

Since each arrow other than $Rh_*\alpha$ is independent of
$\alpha$ and $Rh_*$ is an additive $A$-linear functor, the map
$\alpha\mapsto h_*\alpha$ is $A$-linear.
