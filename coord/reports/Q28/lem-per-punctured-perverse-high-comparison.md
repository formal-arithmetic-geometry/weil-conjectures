# Worker report: lem-per-punctured-perverse-high-comparison

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-punctured-perverse-high-comparison.json` — split statement, no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-punctured-support-cohomological-bound.json` — new statement-only support bound, no Mathlib match.
- `citations.json` — verbatim certificates for every cited node in every proof step.

## Attachments

None. I searched the exact item id, the source keywords and the slopmaster2 source; no sorry-free declaration states this item.

## WANTED

None. The cited source PDF is present in `literature/`.

## What was wrong or incomplete in the imported node

The imported item had an empty proof and did not expose the finite coefficient devissage or the finite hypercohomology filtration used in ILO XVII, Lemma 5.3.2. I supplied those arguments in six steps. The source's Proposition 3.2.1 is a genuine external support-sensitive vanishing statement, so I made it one new statement-only node rather than hiding it in a proof step. No definition was duplicated and no item clause was moved into that node.

The source uses the perverse notation $D^{\leq\varphi}$; the item spells it out as the geometric-stalk inequality. I checked that the proof uses precisely this inequality. The source's Proposition 3.2.1 is stated for a sheaf of $\mathbf Z/\ell\mathbf Z$-modules and does not require constructibility; the new node keeps that generality. The item has $Λ=\mathbf Z/\ell^n\mathbf Z$, so Step 4 explicitly filters by powers of $\ell$.

## Not duplicates

- `lem-per-punctured-support-cohomological-bound` vs every existing node found by `rg` for `punctured`, `3.2.1`, `support`, and `cohomological dimension`: none states Proposition XVII 3.2.1 for sheaves on a punctured excellent strictly henselian local scheme.
- `lem-per-punctured-perverse-high-comparison` vs existing `lem-per-perversity-localization-calculus`, `lem-per-normal-pinned-extension`, and `lem-per-artin-gabber-affine-curve`: those state perverse truncation/extension or affine pushforward bounds; none compares $H^{q-1}(U,\Lambda)$ with $H^{q-1}(U,M)$ under the item hypotheses.

## Review by Q28

I read the item node and its source in Illusie–Laszlo–Orgogozo, *Travaux de Gabber*, arXiv:1207.3648, Exposé XVII, Lemma 5.3.2 (printed pp. 288–289). I also read the immediately used source result, Proposition 3.2.1 (printed p. 268), whose statement is the new support-bound node. The item hypotheses agree clause by clause: prime power $Λ$, $d\ge2$, excellent normal strictly henselian local $X$, punctured open $U$, geometric-stalk bound by $\varphi(y)$, and a specified isomorphism $Λ_U\simeq\tau^{\mathrm{ord}}_{\le0}M$. The comparison map is the composite with the ordinary truncation map exactly as in the source.

Step 1 uses the existing ordinary standard-truncation and derived-category nodes. Their statements say that the truncation retains the cohomology in the stated range and gives the canonical triangle; this produces $C=\tau^{\mathrm{ord}}_{\ge1}M$ with positive cohomology and identifies the map $u$. Step 2 uses the existing scheme-stalk dimension node, the Krull-dimension definition, exactness of geometric stalks, stalk conservativity, and the derived-category definition. I checked the two chain inequalities directly: a chain of generalizations of $y$ followed by $y\rightsquigarrow x$ gives $\dim\mathcal O_{X,y}\le d-1$, and concatenating a chain to $y$ with a chain in $\overline{\{y\}}$ gives $\dim\mathcal O_{X,y}+\dim\overline{\{y\}}\le d$. Thus nonzero stalks of $\mathcal H^r(C)$ vanish for $r>2d-4$, with the $d=2$ case giving $C=0$.

Step 3 is the elementary arithmetic consequence of Step 2: for $r=2i-1$ or $2i$, the inequality $r\le2\dim\mathcal O_{X,y}-2$ implies $\dim\mathcal O_{X,y}\ge i+1$, hence support closure dimension at most $d-i-1$. Step 4 cites the new Proposition 3.2.1 node, exact stalks, the short-exact-to-triangle node, enough injectives, the triangulated derived global-sections node, the global-sections definition, and the long-exact triangle node. I checked that each cited statement supplies exactly what the step takes: the new node supplies vanishing for $ℓ$-killed quotients; exact stalks preserve the support bound; the short exact sequence of powers of $ℓ$ supplies triangles; enough injectives and the derived direct-image statement justify derived global sections; and the triangle node supplies the long exact sequence. The induction starts at $\ell^nF_r=0$, so it proves the same bound for the $Λ$-module sheaf $F_r$.

Step 5 uses the existing successive-truncation triangle and the same derived-global-sections and long-exact nodes. The degree calculation is explicit: for $t\ge2d-2$ and $r=2i-1,2i$, $t-r\ge2(d-i-1)$. The finite Postnikov induction therefore kills $H^t(U,C)$; the $d=2$ edge case was checked separately. Step 6 applies the long exact sequence to the first triangle. For $q\ge2d$, both adjacent terms are $H^{q-2}(U,C)$ and $H^{q-1}(U,C)$, which vanish by Step 5, so the required map is an isomorphism.

I reran the DAG and blueprint searches for the child statement, checked all cited node files, and generated `citations.json`; every quote is a verbatim substring of the cited statement. I ran the required LeanFinder, LeanSearch, Loogle and Mathlib grep searches through `msearch.py`; the returned hits were unrelated derived truncation, algebraic etale-locus, structural stalk, or module-support declarations, so the new node is not a Mathlib leaf. No Lean source was written or compiled, and no SGA 4 or SGA 4½ source was cited.
