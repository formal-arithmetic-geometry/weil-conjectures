+++
id = "thm-pur-diagonal-dualizing-object"
kind = "theorem"
title = "The smooth dualizing object is the Tate twist"
order = 2010
uses = ["cor-pur-vector-bundle-purity", "def-coefficient-twists-detailed", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-derived-tensor", "def-weil-scheme-morphism-properties", "lem-pur-diagonal-base-change", "lem-pur-diagonal-regular-immersion", "thm-pur-dnc-invariance"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $f:X\to Y$ be smooth,
separated, of pure
relative dimension $d$. Then there is a canonical isomorphism

$$
\omega_f=Rf^!\Lambda_Y\xrightarrow{\ \sim\ }\Lambda_X(d)[2d].
$$

## Proof

The final restriction of the Tate line uses [def-coefficient-twists-detailed], with tensor identifications as in [def-weil-derived-tensor].
Step 1: the section invariant of the diagonal. Apply
[thm-pur-dnc-invariance] to the smooth map
$p_1:W\to X$ of [lem-pur-diagonal-base-change] and its closed
section $\Delta$. By [lem-pur-diagonal-regular-immersion] its
normal bundle is canonically $N_\Delta\cong T_{X/Y}$, a vector
bundle of rank $d$, so

$$
C(p_1,\Delta)\;\cong\;C(\pi_T:T_{X/Y}\to X,\,0_T).
$$

Step 2: the two sides. The left side is $\omega_f$ by
[lem-pur-diagonal-base-change]. For the right side,
[cor-pur-vector-bundle-purity] applied to $\pi_T$ gives

$$
\omega_{\pi_T}=R\pi_T^!\Lambda_X\;\cong\;\Lambda_{T_{X/Y}}(d)[2d],
$$

and pulling back by the zero section $0_T$ gives

$$
C(\pi_T,0_T)=0_T^*\omega_{\pi_T}
\;\cong\;0_T^*\Lambda_{T_{X/Y}}(d)[2d]
\;\cong\;\Lambda_X(d)[2d].
$$

Combining the two steps proves the assertion. The identification is
canonical (every displayed step is canonical, by the uniqueness clause
of [thm-pur-dnc-invariance]); compatibility with base change
follows from the base-change compatibility of the diagonal, of
[thm-pur-dnc-invariance], and of
[cor-pur-vector-bundle-purity] (the normal bundle of the diagonal
of the base change is the base change of the normal bundle).
