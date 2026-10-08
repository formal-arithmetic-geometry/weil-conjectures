+++
id = "lemma-weil-pbc-h1-torsor-comparison"
kind = "lemma"
title = "Finite-etale torsor comparison"
order = 1139
uses = ["def-weil-pbc-finite-torsors", "def-weil-pbc-strict-henselian-setup", "lemma-weil-pbc-etale-degree-zero", "lemma-weil-pbc-finite-etale-henselian-lifting", "lemma-weil-pbc-finite-locally-constant-etale-equivalence", "thm-galois-lc-etale", "thm-weil-pbc-finite-etale-lifting"]
+++
For a finite abelian group $M$ and proper $Y\to\operatorname{Spec}A$,
restriction induces a bijection

$$
H^1(Y,\underline M)\xrightarrow{\sim}H^1(Y_0,\underline M).
$$

## Proof

An $\underline M$-torsor is a finite etale $Y$-scheme $P$ with a simply
transitive $M$-action by the finite-locally-constant equivalence. Apply the
henselian lifting lemma to lift $P$, every automorphism $m:P\to P$, and the
multiplication diagrams. Uniqueness of lifted morphisms preserves the group
law and simple transitivity. Restriction and lifting are inverse on
isomorphism classes, which is the displayed $H^1$ bijection. This is the
torsor subtree of Tag `0A5G`.

## Detailed form

Under the hypotheses of [thm-weil-pbc-finite-etale-lifting], restriction is a
bijection

$$
 H^1(Y,\underline M)\xrightarrow{\sim}H^1(Y_0,\underline M)
$$

for every finite abelian group $M$.

## Proof

By [def-weil-pbc-finite-torsors] the two sides classify $M$-torsors, which by
[thm-galois-lc-etale] are the simply transitive $M$-actions on finite etale schemes. The equivalence of
[thm-weil-pbc-finite-etale-lifting] preserves such actions and their
isomorphism classes, giving the bijection.
