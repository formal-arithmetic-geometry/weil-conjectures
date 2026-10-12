## What changed

Proved `ModuleCat.projective_resolution_ext_all_degrees`. The forward implication reuses a bounded projective resolution at the bound `i - 1` and applies `projective_resolution_ext_degree`; the reverse implication specializes the all-degrees hypothesis at `n + 1`. Added the proof-only import `Sheaf.RingTheory.ProjectiveResolutionExtDegree`.

## Proved and sorry left

The declaration `ModuleCat.projective_resolution_ext_all_degrees` is proved. No new `sorry` declarations were added.

## No longer needed

The original planned dependencies `def-weil-pbc-finite-global-dimension`, `def-pc-ext`,
`lem-weil-pbc-projective-ext-criterion`, and `lem-weil-pbc-ext-long-exact-first-variable`
are not needed by this proof and were removed from the node's `proof_deps`; the proof uses
the degree characterization node instead. No import was removed; the new import of
`Sheaf.RingTheory.ProjectiveResolutionExtDegree` is proof-only and required.

## Where the brief, the DAG or earlier work was wrong

The planned direct induction and long exact sequence argument is unnecessary after the degree characterization is available: monotonicity of the resolution bound follows immediately by reusing the same resolution, and arithmetic reduces every degree `i ≥ n + 1` to the degree theorem at `i - 1`.

## Second reading by S2

1. The delivered module was diffed against the repository version. The theorem signature and
   all existing declarations are unchanged byte for byte; only the proof and a proof-only import
   were added.
2. Both sandbox modules compile with `lcompile.py --all`. The target theorem has no `sorry`; the
   imported degree characterization remains the separately named open theorem. No forbidden
   declarations or hollow definitions were introduced.
3. The all-degrees statement is unchanged and no new statement was split off. The proof uses the
   existing degree characterization, and its two implications are valid at the edge case
   `i = n + 1` (including `n = 0`).
4. The shorter route is the direct reduction to the degree characterization. The four old proof
   dependencies are no longer used, while the unit route through the degree characterization is
   retained.
5. The node's proof, proof dependencies, and proof origin match the Lean proof. The unit and
   chapter metadata are unchanged.

Changed during second reading: completed this report with the required review section and listed
all four pruned proof dependencies explicitly.
