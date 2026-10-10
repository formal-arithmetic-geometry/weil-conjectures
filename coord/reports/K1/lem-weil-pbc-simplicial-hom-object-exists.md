1. Files written

- dag/nodes/sec-curve-estimates/lem-weil-pbc-simplicial-hom-object-exists.json: the item, split into three proof steps; no Mathlib match.
- dag/nodes/sec-curve-estimates/lem-weil-pbc-simplicial-index-finite-initial.json: one new unsplit statement, the combinatorial core of Stacks 017K; no Mathlib match.

2. Attachments

None. No sorry-free slopmaster2 declaration states the item or the new node; the search covered the item id, simplicial Hom objects, and compatible families in WeilConjectures/.

3. WANTED

None.

4. What was wrong or incomplete

The imported item had no proof. My first delivery gave the new node the wrong direction of initiality. For $S=\Delta[0]$ and $m_0=0$, the two arrows $[0]\to[1]$ in the simplex category demonstrate that the inclusion of degree zero into $\mathcal I_S$ is not initial. The correct assertion concerns $\mathcal I_{S,\leq 2m_0}^{\mathrm{op}}\to\mathcal I_S^{\mathrm{op}}$, with arrows from each simplex of $\mathcal I_S$ into a bounded-degree simplex. The first report also incorrectly said that the Stacks source was unavailable and filed a WANTED for it. Both errors are corrected.

5. What could not be finished

Nothing in the stage-1 split. This stage writes no Lean.

## Review by K1

I read Stacks simplicial.tex Lemma 017J (lemma-exists-hom-0-from-simplicial-set) and Lemma 017K (lemma-exists-hom-0-from-simplicial-set-finite), categories.tex Definition definition-initial and Lemma 002R (lemma-initial), and hypercovering.tex Lemma 01G2 (lemma-coprod-prod-SR). Their statements supply, respectively, the compatible-family diagram, its finite truncation, the limit comparison for an initial functor, and finite limits in $\mathrm{SR}(X)$. I checked the item's statement against 017J/017K: its finite nonempty $S_n$ and finite nondegenerate set imply the source's eventual degeneracy condition, and its universal family is the cone form of the source's representing object.

Step 1 cites def-weil-pbc-semi-representable-object for $\mathrm{SR}(X)$ and its simplicial object $K$, and def-weil-pbc-simplicial-set for the simplex category and $S$ operators. It constructs precisely the category and diagram in the proof of 017J; the cone equations are exactly $K(\varphi)\circ f_s=f_{S(\varphi)(s)}$. No coproduct claim is used in this cone construction.

The new node states only the combinatorial reduction of 017K. Its objects and morphisms match the 017J indexing category. It explicitly states the two conditions for initiality of the opposite inclusion: every $z$ has an arrow $z\to y$ with $y$ bounded, and any two such arrows are connected by a commuting zigzag $y_0\to y_1\leftarrow y_2\to\cdots\leftarrow y_{2r}$ of bounded objects under $z$. The first comes from the Eilenberg-Zilber expression $s=S(\sigma)(u)$ with $u$ nondegenerate of degree at most $m_0$, giving the arrow $(n,s)\to(k,u)$. For the second, 017K first reduces the targets of two arrows out of $z$ to degrees at most $m_0$; when the degree of $z$ exceeds $2m_0$, the two order maps then have a common repeated position among the first $2m_0+1$ values. Injectivity of degeneracy maps lets the common source simplex descend by one degree, and iteration gives the bounded zigzag. Categories 002R gives the limit comparison, which is part of the node's statement.

I tested the repaired direction on $S=\Delta[0]$, $m_0=0$: $\mathcal I_S$ is the simplex category, each $[n]$ has the unique map $[n]\to[0]$, so the comma category for the opposite inclusion has a single object up to its unique map. By contrast, the old direction fails at $[1]$ because its two vertex arrows from $[0]$ have no common bounded refinement. The other edge case is an admissible $S$ with several vertices: degenerate simplices still map to their unique nondegenerate ancestors, while the finite subcategory retains all degree-zero vertices, so it does not collapse distinct components.

Step 2 cites the new node, including its Categories 002R comparison clause; it no longer invokes 002R as an uncited independent fact. Step 3 cites lem-weil-pbc-semi-representable-finite-limits, whose statement says $\mathrm{SR}(X)$ has all finite limits, and the new node again for extension of the bounded limit cone to all simplices. The limit universal property then gives the unique map $W\to H$ for any compatible family, as the item states. All hypotheses used at each step appear in the item or in these cited statements.

Before creating the new node, I searched the DAG and blueprint for the 017K finite truncation, and the Lean source for this declaration; none duplicates it. LeanSearch, LeanFinder, and Mathlib-source searches produced general simplicial-set finiteness and initial-functor results but no theorem for this indexing category. The new node is an unsplit statement only, introduces every object it uses, and its source is 017K plus Categories 002R. I corrected the item proof origin from agent to document after re-reading the Stacks sources and removed the false WANTED.
