+++
id = "lemma-nagata-power-torsion-quotient-torsionfree"
kind = "lemma"
title = "The power-torsion quotient has no exceptional torsion"
order = 142
lean = ["Submodule.powTorsion_quotient_eq_bot"]
uses = ["def-nagata-power-torsion", "lemma-nagata-power-torsion-submodule"]
+++
Multiplication by $a$ on $M/\Gamma_{(a)}(M)$ is injective. More generally,
no nonzero class in the quotient is killed by a power of $a$.

## Proof

If $a^n[m]=0$, then $a^nm$ belongs to the power-torsion submodule, so some
further power of $a$ kills $m$. Thus $m$ already represents zero in the
quotient.
