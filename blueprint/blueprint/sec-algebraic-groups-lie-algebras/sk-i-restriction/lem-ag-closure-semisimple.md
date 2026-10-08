+++
id = "lem-ag-closure-semisimple"
kind = "lemma"
title = "A semisimple datum is semisimple for its closure and identity component"
order = 2517
uses = ["d-monodromy", "def-wf-semisimple-module", "def-wf-simple-module", "lem-wf-algebraic-component-cosets", "lem-wf-finite-index-restriction-semisimple", "lem-wf-stabilizer-density"]
+++
For a semisimple represented degree datum as in [d-monodromy], $V$ is a
semisimple $G$-module and a semisimple $G^\circ$-module, in the sense of
[def-wf-simple-module] and [def-wf-semisimple-module].

## Proof

Write $V=\bigoplus_iV_i$ with each $V_i$ a simple $W$-representation.
The stabilizer of a subspace is Zariski closed, by the argument of
[lem-wf-stabilizer-density]; a $\rho(W)$-stable subspace is therefore
stable under the closure $G$, and conversely a $G$-stable subspace is
$\rho(W)$-stable. Hence each $V_i$ is $G$-stable, and a proper nonzero
$G$-stable subspace of $V_i$ would be $W$-stable, contradicting
simplicity. So the same decomposition exhibits $V$ as a semisimple
$G$-module. By [lem-wf-algebraic-component-cosets], $G^\circ$ is a
normal subgroup of finite index in $G$, so
[lem-wf-finite-index-restriction-semisimple] makes $V$ a semisimple
$G^\circ$-module.
