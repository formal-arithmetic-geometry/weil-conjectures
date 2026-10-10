# Worker report: lem-weil-pbc-smooth-at-prime-free-conormal-basis

Split the item in four steps following Stacks Smoothing Ring Maps, Lemma Tag 07C6
(`lemma-find-strictly-standard`). The proof first chooses a principal smooth neighbourhood
of the prime and obtains the split conormal sequence. It then selects a subset of the given
relation classes forming a basis over the residue field, spreads that prescribed basis to a
principal neighbourhood, and spreads the complementary module of differentials as a free
module of rank `n - c`. Further localization combines the two neighbourhoods and preserves
smoothness.

Added one strictly smaller unsplit node,
`lem-weil-pbc-prescribed-residue-basis-spreads`, for the prescribed-basis form of the
shrinking argument in Algebra Lemma Tag 0GWM. Its statement is self-contained, it has no
proof fields, and its LeanSearch, LeanFinder, and Mathlib source searches are recorded. No
exact existing DAG node or single Mathlib declaration states that the specified global
elements, rather than some basis, become a basis.

The item statement is unchanged. No Lean files were changed and no Lean build was run, as
required for Stage 1. No existing imports or nodes became unnecessary.

Checks run: JSON parsing, `git diff --check`, `tools/review_split.py`,
`tools/check_dag.py --cycles`, and `tools/preflight_delivery.py`.

## Review by E1

I read Smoothing Ring Maps Lemma 07C6 and its proof, and Algebra Lemma 0GWM with its cited 05GF and 00HN shrinking argument. The item states only the conormal and differential freeness constructed inside 07C6, with the same finite presentation and smooth-at-prime hypotheses. Step 1 applies the already reviewed split-conormal statement to a principal smooth neighbourhood. Step 2 is finite-dimensional linear algebra on its split residue-field sequence: selected relation classes have size $c\le m,n$ and the differential fibre has dimension $n-c$. Step 3 uses finite-projective presentation and local freeness, then the new helper to preserve those *particular* relation classes as a basis. Step 4 uses the existing 0GWM free-at-prime statement for the differential module and localization of Kahler differentials. Writing each element of $A_b$ as a numerator over a power of $b$ makes the common principal shrink $buv$ valid and outside the prime; further localization preserves both bases and smoothness.

The child is self-contained, statement-only, and cites its module-localization notions. Its prescribed-basis assertion follows from 0GWM's proof applied to the map $A^c\to M$ defined by the chosen elements; the existing node states only existence of an unspecified basis, so this is not a duplicate. I searched the current DAG by 0GWM, prescribed basis, and local free module before accepting it. Its LeanSearch, LeanFinder, and source grep results do not claim a false Mathlib leaf. The cases $c=0$ and a polynomial algebra with $I=0$ satisfy the argument; no normality or Noetherian hypothesis is used. The branch has one item-only commit, a split report, no cycle, and no route departure. No correction was sent back.
