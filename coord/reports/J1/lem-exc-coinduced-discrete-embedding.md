# Delivery report

Files written:

- `dag/nodes/sec-curve-estimates/lem-exc-coinduced-functions-open-stabilizer.json` — statement node, unsplit, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-exc-coinduced-discrete-embedding.json` — split statement; no Mathlib match.

Attachments: none. I searched the slopmaster2 source for the item id and coinduced/open-stabilizer declarations; no sorry-free declaration states either node.

WANTED: none.

The returned version had three defects. The auxiliary node repeated the item's action and open-stabilizer conclusion, so I replaced it with the strictly smaller topological statement for a continuous map from a profinite group to a discrete space. I restored the item's statement and `stmt_deps` exactly to the baseline, leaving the auxiliary citation only in the proof. I also corrected the orbit-map description from right cosets to left cosets and read the local Stacks TeX instead of reporting it absent.

## Review by J1

I read `/home/ubuntu/c1-stacks-review/etale-cohomology.tex`. Tag 04JP (`definition-G-module-continuous`, lines around 8786) defines an $R$-$G$-module by a continuous action on a discrete module and immediately states that this is equivalent to every element having open stabilizer. Tag 0DVG (`section-continuous-group-cohomology`, lines around 9008) defines continuous cochains and states the comparison for profinite groups, but it does not contain the coinduced embedding; that embedding remains an agent-written proof ingredient. The item's statement now agrees with the imported baseline and uses only `lem-exc-discrete-modules-abelian` as a statement dependency.

The new node is self-contained: it introduces the profinite group, discrete space, and continuous map, and states only the open normal subgroup invariance needed later. Its proof is intentionally unsplit, with the compactness argument (local constancy, an open-normal neighbourhood basis, and a finite subcover) described here rather than hidden in the statement. I searched the DAG and blueprint with the item terms and `tools/blueprint_refs.py`; no existing node states this fact. LeanSearch was unavailable, LeanFinder returned only compact-open/continuous-representation results, and Mathlib grep found no exact theorem for arbitrary discrete codomain.

For item step 1, `lem-exc-discrete-modules-abelian` supplies the module and continuous discrete-action setting. The pointwise module operations, associativity and identity equations, and preservation of continuity under precomposition by $x\\mapsto xh$ are elementary. Step 2 uses the new node exactly as stated: for each $f$ it supplies $U$ with $f(xu)=f(x)$, which gives $U\\subseteq\\operatorname{Stab}(f)$ under the defined action; a subgroup containing an open subgroup is open, so 04JP's criterion applies. Step 3 uses the open-stabilizer clause of `lem-exc-discrete-modules-abelian`: the orbit map is constant on each left coset $xH$ because $xh m=xm$. Pointwise $A$-linearity, equivariance, evaluation-at-identity injectivity, and naturality are direct calculations. I checked the hypotheses at each step: $G$ is profinite where the new node is used, $M$ is discrete with open stabilizers, and no finiteness of $M$ is assumed.

I tested the revised topological statement on the trivial profinite group, a finite discrete group, and constant maps into a one-point space; all satisfy the asserted open-normal invariance. I also checked the item formulas for $G=1$, $M=0$, and a finite group action. The repair specifically removes the relabelling identified by D1, restores the exact metadata required by E7/B3, and records the actual 04JP/0DVG source content required by F1.

What could not be finished: no Lean compilation is permitted at stage 1; the required checks are performed by the delivery scripts.
