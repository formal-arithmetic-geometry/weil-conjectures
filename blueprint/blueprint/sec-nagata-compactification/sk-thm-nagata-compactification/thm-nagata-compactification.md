+++
id = "thm-nagata-compactification"
kind = "theorem"
title = "Nagata compactification, [stacks-project]"
order = 407
lean = ["AlgebraicGeometry.NagataCompactification"]
uses = ["def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-final-compactification", "lemma-nagata-final-ambient-proper", "lemma-nagata-final-basechanged-compactification", "lemma-nagata-final-factorization", "lemma-nagata-final-open-immersion", "prop-nagata-closed-subscheme-compactifiable", "prop-nagata-finite-type-closed-in-fp"]
+++
The explicitly constructed factorization
$\mathsf C_{\mathrm{Nag}}(f)$ is a compactification of $f$. In particular,
every separated finite type morphism to a quasi-compact and
quasi-separated scheme is compactifiable.

## Proof

$\mathsf C_{\mathrm{Nag}}(f)$ is the composition of two maps $j_f$ and $p_f$. The first map is a quasi-compact open immersion by
[lemma-nagata-final-open-immersion]; the second is proper by
[lemma-nagata-final-ambient-proper]; and their composite is $f$ by
[lemma-nagata-final-factorization]. These are exactly the fields of
[def-nagata-compactification]. Hence the named construction is a
compactification, and its existence witnesses compactifiability.
