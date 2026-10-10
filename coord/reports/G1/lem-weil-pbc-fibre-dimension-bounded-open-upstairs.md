# Worker report: fibre dimension bounded open upstairs

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-fibre-dimension-bounded-open-upstairs.json`: split Stacks 00QH into four steps; statement unchanged.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-quasi-finite-over-polynomial-algebra.json`: new unsplit statement of Stacks 00QE, no Mathlib match after LeanSearch, LeanFinder and source grep.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra.json`: new unsplit statement of Stacks 00QG, no Mathlib match after the same three searches.

The source is `algebra.tex`: 00QH (`lemma-dimension-fibres-bounded-open-upstairs`, lines 31308-31323) cites 00QE (`lemma-quasi-finite-over-polynomial-algebra`, lines 31170-31215) and 00QG (`lemma-dimension-quasi-finite-over-polynomial-algebra`, lines 31291-31305). Tag names were checked in `tags/tags`. The latter follows from 00QF (`lemma-dimension-inequality-quasi-finite`) and 00OP (`lemma-dim-affine-space`); its unsplit statement does not assume that the polynomial map is injective, since 00QF gives the bound for every quasi-finite map and this is the form produced by 00QE. No false source assertion is reproduced.

For the fibre argument, the existing `lem-weil-pbc-quasi-finite-four-rings` supplies 00PP-style base-change stability through its 00PN statement. `lem-weil-pbc-tensor-cancel-base-change` and `lem-weil-pbc-localization-base-change` identify the fibre of `S_g` with the principal localization of the fibre of `S`; `lem-weil-pbc-polynomial-scalar-extension` identifies the polynomial source. `lem-weil-pbc-dimension-supremum-local-dimensions` gives local dimension at most global dimension, and `lem-weil-pbc-dimension-at-point-open-subspace` preserves the local dimension under localization. The fibre-prime and basic-open nodes identify the correct points and neighbourhood. All proof citations belong to the item's unit; no cross-unit statement tool is requested.

Checked the cases `n=0` (quasi-finite fibres have dimension at most zero), an empty fibre away from the chosen prime (dimension `-infty`), and `R=S=k` (choose `g=1`, dimension zero). The 00QE witness `g` is outside the chosen prime, so its fibre is nonempty there. No Lean declarations attach to this item. No wanted literature. No file or statement errors were found in the item; the imported node was simply unsplit. `review_split.py` passes and `check_dag.py --cycles` finds zero cycles; its seven reach warnings concern other nodes already on the base branch.
## Review by G1

I read Algebra 00QH, 00QE, 00QG, and the cited 00PP/00PN base-change argument. The item statement agrees with 00QH, including the fibre point and integer d. The new nodes are the exact 00QE and 00QG dependencies; 00QG correctly uses the noninjective polynomial-map form justified by 00QF.

Step 1 applies 00QE and identifies D(g) with localized primes. Step 2 uses tensor cancellation, localization base change, polynomial scalar extension, and the four-rings quasi-finite base-change statement to obtain a quasi-finite finite-type map on each residue-field fibre. Step 3 applies 00QG and the supremum-of-local-dimensions and fibre-prime statements. Step 4 identifies the principal open in the fibre and uses invariance of local dimension on open subspaces. Each cited statement says the fact used.

Both new nodes are self-contained, statement-only, use exact tags and definition citations, and record the required searches. I searched the DAG for duplicate 00QE/00QG or fibre-dimension statements; none exists. All dependencies remain in `sk-thm-p1`, with no tool use. I checked n=0, empty fibres, and the field identity case g=1. B-E checks pass and the DAG has zero new cycles; no repair was needed.
