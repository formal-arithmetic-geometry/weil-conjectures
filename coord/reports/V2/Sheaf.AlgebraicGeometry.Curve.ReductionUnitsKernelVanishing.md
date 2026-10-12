## What changed

The signature of `AlgebraicGeometry.IsCurve.subsingleton_H_two_reduction_units_kernel`
is unchanged. Its proof now derives degree-two vanishing for every lifted associated
quasi-coherent sheaf from the existing Zariski dimension bound, the module/abelian
comparison, the etale/Zariski comparison, and the coefficient-universe comparison.
It uses topological invariance for the quotient terms and decreasing induction on a
finite filtration, with actual exactness of the long cohomology sequence at each step.
The finite geometric filtration is isolated in the new module
`Sheaf.AlgebraicGeometry.Curve.ReductionUnitsFiltration`.

## Proved and sorry left

Closed: `AlgebraicGeometry.IsCurve.subsingleton_H_two_reduction_units_kernel`
(node `lem-sc-reduction-units-kernel-h2`), from existing statements and the new
geometric filtration statement. This is a decomposition, not an unconditional proof:
one upper hole closed and one lower hole added, net zero holes.

Added and left: `AlgebraicGeometry.Scheme.exists_reduction_units_finite_filtration`
(node `lem-sc-reduction-units-finite-filtration`), with its whole proof `by sorry`.
It asserts only the geometric finite filtration, with no cohomological vanishing.
No other holes are added; no definitions or existing signatures are changed.

## No longer needed

Removed direct imports:
- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`
- `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`

The item's direct proof dependencies no longer include
`lem-sc-etale-affine-qcoherent`, `lem-sc-cech-spectral`,
`pqf-lem-affine-vanishing`, or `lem-sc-noetherian-cohomology-above-dimension`.
The comparison theorems encapsulate the affine/Cech argument and the direct Zariski
bound supplies vanishing. `etale-proposition-etale-reduced` and
`def-sc-etale-qcoherent-module` move to the geometric filtration node.
Some removed modules remain transitive dependencies of the comparison or filtration;
no claim is made that all of them leave the targets' import closure.
The unit `sk-prop-h2` has no realized nodes for this item's internal argument, and its
Kummer statement and step are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan gives the nilpotent-units argument in words but its listed
proof dependencies do not state that filtration. The new geometric theorem makes
that missing step an independent item. It is strictly part of the argument: it
works for any Noetherian scheme, asserts no H^2 vanishing, and still requires the
curve dimension bound plus the exact-sequence induction to obtain the conclusion.

Edge cases: reduced schemes permit n=0 and E=0; empty schemes have zero sheaves;
zero-dimensional and disconnected curves satisfy the same dimension bound. No
smoothness, properness, algebraic closure, connectedness or nonemptiness is used.
The available cohomology comparison for structure modules on smooth connected
curves is too specialized, so the general existing quasi-coherent comparison is used.
The source path in the node is absent locally; the detailed source argument retained
in the parent node and original docstring was read. No new source claim is introduced.

Validation: both sandbox modules now compile with `lcompile.py --all`, without
warnings. The published coefficient-lift dependency is available. The prior proof
inferred different Ext universes on the two sides of the coefficient comparison;
the repaired proof installs the small Ext instance before the standard derived
category, compares small and large Ext explicitly, and transfers subsingletonness
by injectivity with the small-universe witness supplied explicitly. The original
statement remains unchanged.

## New nodes

`lem-sc-reduction-units-finite-filtration`, in
`dag/nodes/sec-curve-estimates/lem-sc-reduction-units-finite-filtration.json`, states
a finite sheaf filtration with pulled-back quasi-coherent additive quotients and a
zero final term. Its proof records nilradical nilpotence, the quotient formula,
flat etale pullback and exact reduction-topos transport. Searches found no existing
filtration: LeanFinder returned unrelated cotangent results, Loogle zero results,
grep ring-level results; LeanSearch was unavailable. Blueprint search returned no
matching node. The existing kernel-vanishing node is updated to the implemented route.


## Second reading by V2

1. PASS. Read the full diff against the repository: the existing theorem signature
   and docstring are byte for byte unchanged. Only its proof and plain imports change.
   No existing definition or target changes; the new theorem is in its own module.
2. PASS. Both delivered modules compile without warnings through lcompile.py.
   Scratch #print axioms for both declarations reports only propext, Classical.choice,
   Quot.sound and sorryAx. The only direct sorry is the whole proof of
   AlgebraicGeometry.Scheme.exists_reduction_units_finite_filtration, as reported.
   There are no definitions in the delivery, forbidden declarations, or data definitions
   chosen from an unproved existence theorem. Filtration witnesses are eliminated only
   inside a theorem proof. The long-exact-sequence step uses actual exactness.
3. PASS. The new filtration statement is strictly geometric and has no H^2 conclusion;
   it is not a renamed restatement. Checked the powers N^(j+1)/N^(j+2), with
   2j+2 >= j+2, and uniform nilpotence on a finite affine cover. Reduced and empty
   schemes admit n=0; for dual numbers the single quotient is the additive nilradical.
   No separatedness is needed for the geometric filtration. The complete docstring
   and matching node describe its construction and exact transport under reduction.
   Independent LeanFinder, Loogle and grep queries (recorded in the node) found only
   ring/cotangent facts, not this sheaf theorem. Repository and upstream rg agree.
   Closing this geometric theorem requires substantial constructions, not a short repair.
4. PASS. The proof uses the existing general comparison and dimension-bound theorems,
   then finite decreasing induction; the specialized smooth-curve comparison does not
   apply. All removed old proof dependencies are listed above, including the two moved
   to the geometric node. Checked sk-prop-h2.realized: its internal realization lists
   are empty, and its Kummer statement and step are preserved. No whole module is
   claimed pruned from the target closure. Removed two redundant plain imports from
   the item (Basic is public through Gm; TopologicalInvariance through the coefficient
   comparison), and the redundant Properties import from the new module. Scratch
   compilation confirmed these removals preserve elaboration. Remaining public imports
   in the new module supply signature vocabulary, not proof-only declarations.
5. PASS. The existing node changes only proof, proof_deps and proof_origin, matching
   the comparison/filtration/exactness proof. Its statement and Lean signature record
   stay fixed. The new node has source, proof steps, their dependency union, searches,
   split status, creation metadata, blueprint ancestry, chapter/unit and verbatim
   whitespace-normalized Lean statement. The reported accounting is one original hole
   closed, one geometric hole added: a decomposition with net zero holes.

Second-reading changes: removed three redundant imports, recorded independent searches
in the new node, completed the removed-import list, and added this audit. No mathematical
statement or proof body required repair.
