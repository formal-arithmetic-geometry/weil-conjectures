+++
id = "thm-galois-fundamental"
kind = "theorem"
title = "The fibre functor is an equivalence"
order = 976
uses = ["def-galois-fibre-functor", "lem-fet-galois-category", "lem-galois-aut-profinite", "lem-galois-transitive", "thm-galois-abstract-equivalence", "thm-galois-lc-etale"]
+++
Let $Y$ be connected with a geometric point $\bar y\to Y$. Then the
fibre functor induces an equivalence

$$
F_{\bar y}:\mathrm{F\acute Et}(Y)\xrightarrow{\ \sim\ }
\pi_1(Y,\bar y)\text{-}\mathbf{Set},
$$

and likewise on $\mathrm{FLC}(Y)$ under the identification of
[thm-galois-lc-etale], where
$\pi_1(Y,\bar y)=\operatorname{Aut}(F_{\bar y})$ carries the profinite
topology of [def-galois-fibre-functor]. The equivalence is compatible
with finite limits and colimits, and with base change along $Y'\to Y$ for
$Y'$ connected, where it corresponds to the passage to the open subgroup
of the fundamental group.

## Proof

By [lem-fet-galois-category] the pair
$(\mathrm{F\acute Et}(Y),F_{\bar y})$ is a Galois category, so
[thm-galois-abstract-equivalence] applies with
$G=\operatorname{Aut}(F_{\bar y})=\pi_1(Y,\bar y)$ as in
[def-galois-fibre-functor], which is profinite by
[lem-galois-aut-profinite]; this is the equivalence. The
identification with $\mathrm{FLC}(Y)$ is [thm-galois-lc-etale], and
the compatibility with finite limits and colimits is the exactness of
$F_{\bar y}$. For base change: by [lem-galois-transitive] the
Galois covers pro-represent the fibre functor, so the pullback of the system of Galois
covers of $Y$ along $Y'\to Y$ is a cofinal system for $Y'$, and the
limit of the corresponding automorphism groups is the stabilizer of the
fibre of a cover trivializing a connected cover of $Y'$, an open subgroup
because stabilizers in a finite continuous $\pi_1$-set are open.
