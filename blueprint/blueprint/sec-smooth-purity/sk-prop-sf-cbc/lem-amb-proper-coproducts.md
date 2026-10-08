+++
id = "lem-amb-proper-coproducts"
kind = "lemma"
title = "Proper direct image preserves arbitrary coproducts"
order = 1562
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-scheme-morphism-properties", "lem-exc-direct-image-coproducts", "lem-weil-pbc-cohomology-filtered-colimit", "lemma-weil-pbc-geometric-stalk-conservative", "thm-sc-finite-type-torsion-cd"]
+++
Let $r:V\to T$ be a proper
morphism of finite type between Noetherian schemes. On the
ordinary derived categories
of etale $A$-module sheaves, $Rr_*$ preserves arbitrary coproducts.
The notation refers to derived direct images.

## Proof

Choose a common finite bound $e$ for the dimensions of the
geometric fibres of the finite-type morphism $r$.
The stalk formula of [cor-weil-pbc-geometric-fiber-finite]
and the bound [thm-sc-finite-type-torsion-cd] give
$R^a r_*F=0$ for $a>2e$, for every sheaf $F$.
The functors $R^a r_*$ commute with filtered colimits: on each
geometric fibre this is
[lem-weil-pbc-cohomology-filtered-colimit], and
[lemma-weil-pbc-geometric-stalk-conservative] detects the comparison.
They therefore commute with direct sums, a direct sum being the
filtered colimit of its finite subsums. The finite acyclic-resolution argument of
[lem-exc-direct-image-coproducts] applies on the unbounded
ordinary category. Its hypercohomology spectral
sequence has only the columns $0,\ldots,2e$. For each total
degree it thus uses a finite interval of cohomology sheaves of the
input. Applying this spectral sequence to the coproduct comparison
proves the assertion, including for unbounded complexes. It
also extends the geometric-fibre formula to unbounded complexes by
the same finite-interval argument.
