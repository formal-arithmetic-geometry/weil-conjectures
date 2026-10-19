# Worker report: lem-trf-residual-curve-value-group

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-residual-curve-value-group.json`: item, split into four proof steps; Mathlib searches retained and proof dependencies updated.
- `dag/nodes/sec-trace-formula/lem-trf-separably-closed-value-group-divisible.json`: new statement-only node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-rational-rank-zero-torsion.json`: new statement-only node; no direct Mathlib match (the search found only the more general module-rank/torsion API).
- `citations.json`: verbatim statement quotes for every node cited in every item step.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, value-group terminology, and nearby trace-formula names; no sorry-free declaration states this item exactly.

## WANTED

- The local archival copy of `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, especially Proposition 4.3.1 and §2.1, for the Abhyankar, torsion, and divisibility input. I read the primary PDF online at the cited pages and wrote `proof_origin.by = agent` because the PDF is not present locally.

## What was wrong or missing

The imported item was unsplit with an empty proof. Its statement agrees with the first-stage valued-field argument in Temkin’s Proposition 4.3.1 and I retained its hypotheses and conclusion. The split now cites the existing relative Abhyankar inequality, then adds two strictly smaller statement-only inputs: zero rational rank implies torsion, and the value group of a separably closed valued field is divisible. The final equality and the two $R/\mathfrak m_R$ refinements are written directly as elementary group and unit calculations rather than moved into nodes. No definition was changed, no SGA source was used, and no unit record is touched because this is not the unit key node.

## Not duplicates

- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-valuation-value-group-torsion`: the new node proves divisibility of a ground-field value group from separable closedness; the existing node gives a power-times-unit torsion statement for an algebraic field extension.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-valuation-value-group-torsion`: the new node is the abstract rationalization criterion for an abelian group; the existing node is an elementwise valuation-ring statement for algebraic extensions.
- `lem-trf-residual-curve-value-group` vs `lem-trf-abhyankar-inequality`: the item combines the inequality with separably closed divisibility to identify value classes and obtain unit representatives; the existing node only states the inequality.


- `lem-trf-rational-rank-zero-torsion` vs `def-trf-multipointed-curve-modification`: the new node is an abstract abelian-group tensor criterion; the existing node defines curve modifications.
- `lem-trf-rational-rank-zero-torsion` vs `def-trf-multipointed-curve`: the new node is an abstract torsion criterion; the existing node defines multipointed curves.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-abhyankar-finite-type-field-height`: the new node converts rational rank zero to torsion; the existing node bounds valuation height over a prime field.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-birational-quasi-modification-common-cover`: the new node is a group fact; the existing node constructs a common curve modification.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-birational-riemann-zariski-neighbourhoods`: the new node is a group fact; the existing node concerns Riemann–Zariski neighbourhoods.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-elementary-semistable-chart-globalization`: the new node is a group fact; the existing node globalizes semistable charts.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-finite-fibre-valuation-domination`: the new node is a group fact; the existing node proves finite-fibre valuation domination.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-geometrically-reduced-eta-normal`: the new node is a group fact; the existing node proves geometric reducedness and eta-normality.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-marked-curve-finite-type-model`: the new node is a group fact; the existing node constructs finite-type marked curve models.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-marked-nodal-dualizing-degrees`: the new node is a group fact; the existing node computes dualizing degrees on nodal curves.
- `lem-trf-separably-closed-value-group-divisible` vs `def-trf-multipointed-curve-modification`: the new node proves value-group divisibility; the existing node defines curve modifications.
- `lem-trf-separably-closed-value-group-divisible` vs `def-trf-multipointed-curve`: the new node proves value-group divisibility; the existing node defines multipointed curves.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-abhyankar-finite-type-field-height`: the new node proves divisibility from separable closedness; the existing node gives an absolute valuation-height bound.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-birational-quasi-modification-common-cover`: the new node proves divisibility of a value group; the existing node constructs a common curve modification.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-birational-riemann-zariski-neighbourhoods`: the new node proves divisibility; the existing node concerns Riemann–Zariski neighbourhoods.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-elementary-semistable-chart-globalization`: the new node proves divisibility; the existing node globalizes semistable charts.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-finite-fibre-valuation-domination`: the new node proves divisibility; the existing node proves finite-fibre domination.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-geometrically-reduced-eta-normal`: the new node proves divisibility; the existing node proves geometric reducedness and eta-normality.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-marked-curve-finite-type-model`: the new node proves divisibility; the existing node constructs marked finite-type models.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-marked-nodal-dualizing-degrees`: the new node proves divisibility; the existing node computes nodal dualizing degrees.


- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-residual-curve-value-group`: the new node is only the abstract implication from zero rational rank to torsion; the item applies it to a valued curve extension and concludes unit representatives.
- `lem-trf-rational-rank-zero-torsion` vs `lem-trf-abhyankar-inequality`: the new node is the group-theoretic consequence after rational rank is known; the existing node supplies the valuation inequality and residue term.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-residual-curve-value-group`: the new node only proves divisibility of the ground value group; the item combines it with torsion and ordered-group cancellation to identify the two value groups.
- `lem-trf-separably-closed-value-group-divisible` vs `lem-trf-abhyankar-inequality`: the new node uses separable closedness to prove divisibility; the existing node is independent of separable closedness and gives the Abhyankar bound.


- `def-trf-rational-rank` vs `lem-trf-residual-curve-value-group`: the new node only defines rational rank; the item proves a value-group equality and unit-representative conclusion.
- `def-trf-rational-rank` vs `def-trf-multipointed-curve-modification`: the new node defines an abelian-group invariant; the existing node defines curve modifications.
- `def-trf-rational-rank` vs `def-trf-multipointed-curve`: the new node defines an abelian-group invariant; the existing node defines multipointed curves.
- `def-trf-rational-rank` vs `lem-trf-abhyankar-finite-type-field-height`: the new node defines rational rank; the existing node proves a valuation-height bound.
- `def-trf-rational-rank` vs `lem-trf-abhyankar-inequality`: the new node defines rational rank; the existing node states the relative valuation inequality using it.
- `def-trf-rational-rank` vs `lem-trf-birational-quasi-modification-common-cover`: the new node defines rational rank; the existing node constructs a common curve modification.
- `def-trf-rational-rank` vs `lem-trf-birational-riemann-zariski-neighbourhoods`: the new node defines rational rank; the existing node concerns Riemann–Zariski neighbourhoods.
- `def-trf-rational-rank` vs `lem-trf-elementary-semistable-chart-globalization`: the new node defines rational rank; the existing node globalizes semistable charts.
- `def-trf-rational-rank` vs `lem-trf-finite-fibre-valuation-domination`: the new node defines rational rank; the existing node proves finite-fibre valuation domination.
- `def-trf-rational-rank` vs `lem-trf-geometrically-reduced-eta-normal`: the new node defines rational rank; the existing node proves geometric reducedness and eta-normality.
- `def-trf-rational-rank` vs `lem-trf-marked-curve-finite-type-model`: the new node defines rational rank; the existing node constructs marked curve models.
- `def-trf-rational-rank` vs `lem-trf-marked-nodal-dualizing-degrees`: the new node defines rational rank; the existing node computes nodal dualizing degrees.


## Review by N4

I read the item node, its `sec-trace-formula` chapter and `sk-i-curve-zero` unit metadata, the ancestor blueprint proof for `lem-trf-local-term-locality`, and Temkin’s Proposition 4.3.1 proof online (pp. 27–28) together with §2.1 Lemma 2.1.2. I also read the complete statements of every existing node cited by the item. Step 1 uses exactly the relative Abhyankar statement: with $F=K$, valued extension $L/K$, valuation ring $O$, induced ring $R=O\cap K$, and the given residue transcendence degree one, its inequality gives rational rank zero for $\Gamma_L/\Gamma_K$. Step 2 uses exactly the new rational-rank node’s assertion that zero rational rank makes every quotient class torsion. Step 3 uses exactly the new separably-closed value-group node’s divisibility conclusion, and I checked its edge cases: in characteristic different from $p$, separable $n$th-root polynomials give divisibility; for the characteristic prime, an Artin–Schreier equation $Y^p-Y=a$ applied to an element of negative value gives the required $p$-division, including the trivial value class. Step 4 explicitly checks the cancellation in the torsion-free ordered value group, chooses a representative $c\in K^\times$, and proves $z/c\in O^\times$. Step 5 (the fourth proof step) verifies $c\in R$ when $z\in O$ and rules out $c\in R^\times$ when $z\in\mathfrak m_O$, so it gives the stated maximal-ideal refinement. I tested the statement on the trivial valuation ($O=L$, $R=K$), a rank-one valuation with transcendental residue, and the mixed-characteristic and characteristic-$p$ separably closed cases.

For the new nodes I searched the whole DAG and both blueprint snapshots for their statements and key phrases; no duplicate blueprint node exists. I ran and read LeanFinder, Loogle, LeanSearch, and Mathlib-source grep searches for each node. The value-group search returned only definitions and unrelated rank-one/finite-field APIs; the rational-rank search returned `rank_eq_zero_iff_isTorsion` for module rank and torsion APIs, which do not directly state the tensor-to-abelian-group criterion. I read `Mathlib/LinearAlgebra/Dimension/Torsion/Finite.lean` around that declaration, `Mathlib/FieldTheory/IsSepClosed.lean` around the separably closed root lemmas, and the valuation value-group definitions. The exact statement quotes in `citations.json` are verbatim. No proof step exceeds 2000 characters or hides another independent lemma.

## What could not be finished

Nothing in this one-level split. The two new non-Mathlib dependencies are intentionally statement-only and unsplit, as required by stage 1.