## What changed

Completed AlgebraicGeometry.IsCurve.dense_open_high_cohomology_high in
lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenHighCohomologyHigh.lean without changing
its signature or any public import. Added proof-only imports for the dense irreducible
opens, zero-dimensional cohomology, Ext/derived comparison, finite edge map, closed
complement, open-closed exactness, forgetting coefficients, and cohomology bijectivity.
Updated the existing node's proof, proof_deps and proof_origin to match the Lean proof.

The canonical closed complement embeds into the zero-dimensional complement of a smaller
dense union supplied by exists_dense_irreducible_opens. Zero-dimensional vanishing and
the finite edge map kill the third term of the open-closed short exact sequence in every
positive degree. Sheaf.H.bijective_map_f then proves the prescribed map bijective above
one. The proof follows Stacks Tag 0GJA, proof paragraphs 1–3, read at
https://stacks.math.columbia.edu/tag/0GJA. It retains the dense-open reduction in the
sk-thm-p1 unit; no unit step is bypassed.

## Proved and sorry left

Proved AlgebraicGeometry.IsCurve.dense_open_high_cohomology_high
(node lem-pbc-s2-dense-open-high-cohomology-high): 1 of 1 original sorries removed.
No sorry remains in the delivered module; no new statement or sorry is introduced.
The proof uses the existing zero_dimensional_etale_cohomology declaration. The second
reader's scratch #print axioms check now reports only propext, Classical.choice and
Quot.sound for the completed theorem, with no sorryAx.

Local compilation is clean. Edge cases require no additional hypotheses: X empty,
U=X, zero coefficients, zero sheaf, reducible or nonreduced X, and q=2 are covered.
The dimension bound is obtained by an inducing map, so no mistaken assumption that X
itself is irreducible occurs. The coefficient-forgetting/lowerStar identification and
the specified counit are definitionally checked by Lean.

## No longer needed

The three public imports are unchanged and supply the existing statement. Removed the
original proof-only imports Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit,
Sheaf.AlgebraicGeometry.CurveCoefficientPair, and WeilConjectures.SixFunctors.Finite.Exact.
The finite edge-map module imports finite exactness internally; the target proof needs
no separate import. CurveCoefficientPair supplies no declaration used here.
The temporary proof import WeilConjectures.SixFunctors.OpenClosed.AxiomCensus was replaced
by WeilConjectures.SixFunctors.OpenClosed.Exact; no census module is needed.

The direct proof dependency lem-weil-pbc-cohomology-pullback-derived-unit and its module
Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit are not needed by this proof: the
already proved finite edge-map theorem suffices. The direct dependency
lem-weil-pbc-closed-point-residue-field-base is also unnecessary: the existing
zero-dimensional cohomology theorem handles the geometry and arbitrary abelian sheaves.
The direct dependencies lem-weil-pbc-finite-type-over-noetherian and
lem-weil-pbc-noetherian-finitely-many-components are absorbed by the already proved
lem-pbc-q1-dense-irreducible-opens; their facts remain used internally there.
The direct dependency lemma-weil-pbc-finite-direct-image-exact is replaced by the existing
lem-weil-pbc-finite-pushforward-cohomology; finite exactness remains used internally by
its proved edge-map theorem in WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen.
The old direct proof dependency def-weil-pbc-curve-setting remains a statement dependency
and supplies IsCurve through the unchanged public Curve import; it is no longer listed
as a separate proof dependency. This accounts for all six removed old proof dependencies.
No claim is made that these shared nodes are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The DAG's plan lacked the explicit Ext/derived
cohomology comparison needed because zero_dimensional_etale_cohomology states derived
cohomology vanishing while the target uses Sheaf.H. The existing comparison theorem
supplies this without a new node. The existing finite edge-map result also avoids
formalizing the much larger derived-unit comparison merely to compute the boundary.


## Second reading by J2

1. PASS: diffed the sole delivered module against the repository. Its existing theorem
   signature and docstring are byte-for-byte unchanged, as are all public imports; no
   definition or other visible declaration changes. No change record is needed.
2. PASS: compiled the module locally without errors or warnings. No sorry or forbidden
   declaration occurs. Compiled a scratch copy with #print axioms: the theorem depends
   only on propext, Classical.choice and Quot.sound, with no sorryAx.
3. PASS: there are no split-off statements, new declarations, new nodes, or remaining
   sorries to validate. Checked the existing inputs and the empty-scheme, full-open,
   reducible/nonreduced, zero-sheaf and q=2 cases: the inducing-map dimension argument
   and positive-degree vanishing introduce no extra assumptions.
4. PASS: read the proof from the target downward, the finite edge-map theorem, the
   Ext/derived comparison, the zero-dimensional theorem, and the exact-sequence input.
   Searched the library for alternative dense-open/cohomology comparisons with rg and
   msearch grep; no independent shorter theorem was found. All proof imports supply
   declarations used directly. The proof uses the prescribed counit, and keeps the
   dense-open reduction of sk-thm-p1; its realized statement/step nodes are not bypassed.
   Checked every removed old proof dependency against the node diff. Corrected the
   report's omitted removed imports and curve-setting proof-dependency explanation.
5. PASS: the delivered node's proof steps, six proof_deps and proof_origin match the
   Lean argument. Its recorded Lean signature matches the unchanged theorem. Checked
   the cited Stacks Tag 0GJA proof online: positive-degree boundary vanishing is valid
   without constructibility; constructibility is used only for degree-zero finiteness.

Changes by the second reader: corrected the report's import/pruning inventory and its
outdated transitive-axiom status. The Lean proof and DAG metadata needed no repair.
