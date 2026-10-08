+++
id = "lemma-weil-pbc-finite-pullback-descent"
kind = "lemma"
title = "Finite descent compatibility"
order = 1083
uses = ["def-weil-pbc-finite-section-pullback", "lemma-weil-pbc-finite-pullback-closed-fibre", "lemma-weil-pbc-finite-pullback-composition"]
+++
Let $u:T'\to T$ be finite surjective. Suppose $s'\in(u^{-1}F)(T')$ is
equipped with a descended section $s\in F(T)$, meaning
$u_T^\sharp(s)=s'$. Then the same equality holds after restriction to a
closed fibre.

## Proof

The first equality is the descent witness. Its closed-fibre restriction is
the equality supplied by Lemma
[lemma-weil-pbc-finite-pullback-closed-fibre].
