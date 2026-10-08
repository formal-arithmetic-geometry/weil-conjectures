+++
id = "lemma-nagata-power-torsion-kernel-localization"
kind = "lemma"
title = "Power torsion as a localization kernel"
order = 140
lean = ["Submodule.powTorsion_eq_ker_localization"]
uses = ["def-nagata-power-torsion", "lemma-nagata-power-torsion-submodule"]
+++
The power-torsion submodule is the kernel of the localization map

$$
M\longrightarrow M_a.
$$

## Proof

An element maps to zero in localization away from the powers of $a$ exactly
when it is killed by one element of that multiplicative system, namely by a
power of $a$.
