Files written:

- `dag/nodes/sec-abelian-varieties/lem-pqf-leray-five-term.json` (statement, split; no new nodes and no Mathlib leaves).
- `citations.json` (verbatim citations for every proof-step dependency).

Attachments: none.  No project declaration in `WeilConjectures/` carries the blueprint tag or states this generic five-term sequence without `sorry`.

WANTED: none.

The imported node had an empty proof despite depending on the standard low-degree extraction. I retained its statement and dependencies, and supplied three steps. The Stacks source (Homology, Lemma 0132, label `lemma-first-quadrant-ss`) explicitly supplies finite filtrations and convergence; the exact five-term display is the standard total-degree 1--2 extraction from the exact-couple definitions immediately preceding that lemma. No duplicate child node was created because the DAG already contains the exact-couple, convergence, and filtration statements.

## Review by G1

I read the item, its ancestor proof paragraph in `pqf-lem-leray-lowdegree`, and the source around `lemma-first-quadrant-ss` in `homology.tex`. I also opened each cited DAG node. Step 1 uses exactly the exact-couple statement that the pages are successive homology objects and that `d_r` has bidegree `(r,1-r)`; with first-quadrant indices this leaves only `d_2 : E_2^{0,1} -> E_2^{2,0}` in the relevant degrees. Step 2 uses the convergence statement's canonical `E_infty` to associated-graded isomorphisms and the filtration statement's graded-piece definition; these supply the finite filtration edge maps in degrees 1 and 2. Step 3 uses the exact-couple kernel/image page formula together with the same convergence and filtration statements to identify the kernels and images at each term, including the transgression label and the two edge maps. Every quote in `citations.json` is copied verbatim from the cited node. I checked the edge cases of a zero spectral-sequence page and of a sequence with only the `(0,1)` and `(2,0)` entries: the displayed sequence reduces respectively to the zero exact sequence and to the kernel/cokernel sequence of `d_2`. The Mathlib searches were rerun for the item (LeanFinder, Loogle, grep, and unavailable LeanSearch); they found no spectral-sequence five-term theorem.
## Second reading by G1

- Item statement: checked against the ancestor blueprint proof and Homology Lemma 0132 (`lemma-first-quadrant-ss`); verdict: hypotheses and displayed five-term sequence agree, with edge directions read from the decreasing filtration.
- Step 1: checked against `def-sp-exact-couple`; verdict: the bidegree and page homology formula leave only `d_2:E_2^{0,1}\\to E_2^{2,0}` in these degrees.
- Step 2: checked against `def-sp-convergence` and `def-sp-filtration`; verdict: corrected the degree-2 edge to the inclusion `E_2^{2,0}\\to H^2` of `F^2H^2`, using `F^3H^2=0`.
- Step 3: checked against the exact-couple, convergence, and filtration statements; verdict: corrected exactness at `E_2^{2,0}` to use the stable bottom-piece inclusion and retained the transgression identification.
- New node `lem-pqf-leray-five-term`: no new node was created; the existing dependency statements were opened and every citation remains a verbatim quote in `citations.json`.
- Small cases checked: zero pages give the zero exact sequence; with only `(0,1)` and `(2,0)` nonzero the sequence is the kernel/cokernel sequence of `d_2`; edge maps have the stated inclusion/quotient orientations.

Changes made: repaired the reversed final edge map and its exactness explanation; recorded source comparison, dependency checks, and edge-case tests. Lemma 0132 supplies finite filtration and convergence, while the five-term display is the standard total-degree `1--2` extraction from the exact-couple construction.
