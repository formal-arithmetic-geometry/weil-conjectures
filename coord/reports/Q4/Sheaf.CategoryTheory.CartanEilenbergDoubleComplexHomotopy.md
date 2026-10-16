## What changed

Replaced the proof of `cartanEilenberg_doubleComplex_homotopy` with a decomposition: obtain the total-object witnesses and component homotopy from the component theorem, then prove the filtration clause using the separate factorization theorem. Added two helper modules. The filtration theorem is proved; the component theorem remains open.

## Proved and sorry left

Closed the original hole in `CategoryTheory.cartanEilenberg_doubleComplex_homotopy`
(node `lem-sp-cartan-eilenberg-double-complex-homotopy`) by decomposition. Added one
hole, `CategoryTheory.cartanEilenberg_doubleComplex_homotopy_components`
(node `lem-sp-cartan-eilenberg-double-complex-homotopy-components`): it still needs
the horizontal lift, residual vertical null-homotopy, and total-homotopy assembly
formalized in its four proof steps. This is a decomposition with net zero holes
closed, rather than a complete proof of the comparison theorem.

`CategoryTheory.cartanEilenberg_secondFiltration_factor`
(node `lem-sp-cartan-eilenberg-double-complex-homotopy-filtration`) is proved.
Actual holes remaining: zero in the parent, one in the component helper, zero in
the filtration helper. The second reading adds no holes and closes no further holes.

## No longer needed

Removed the parent module's unused direct proof imports
`Sheaf.CategoryTheory.CartanEilenbergVerticalNullhomotopy` and
`Sheaf.CategoryTheory.HorizontalComparisonLift`. These remain imported by the
open component module, so neither module is pruned from the import closure.

The parent's old direct `proof_deps`, `lem-sp-ce-horizontal-lift` and
`lem-sp-ce-vertical-nullhomotopy`, are now indirect dependencies through
`lem-sp-cartan-eilenberg-double-complex-homotopy-components`. They are still
needed by that component proof plan. No module is claimed pruned.

Removed four duplicate private helpers from the filtration module and reused
`HomologicalComplex₂.factors_finset_sup`, `HomologicalComplex₂.factors_zsmul`, and
`HomologicalComplex₂.secondFiltration_inclusion_factors` (which itself uses
`factors_image`) from `DoubleComplexTotal` via a proof-only `import all`.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-c477a, head c477aa071:

- D1: removed the filtration conclusion from the component node statement and its
  unused `def-sp-filtration` statement dependency. The fourth component proof step
  now explains finite totalization, extension by zero, and boundary vanishing;
  the separate filtration helper supplies the filtration conclusion.
- H8: replaced the component theorem's placeholder docstring with the four numbered
  proof steps in its node. Replaced the filtration theorem's incorrect row-comparison
  description with its finite-supremum, pullback, and factorThru proof.
- H3: rewrote the filtration node statement with the abelian category, total objects,
  morphism delta, first-quadrant hJ, homotopy H, typed component maps, exact hcomp
  identity, and the factorization equation. Removed the nonexistent component
  boundary-vanishing hypotheses. Its proof now records the same finite-supremum
  argument as the Lean proof, including empty intervals and negative target indices.

The horizontal child also requires column quasi-isomorphisms and injectivity.
These follow from the stated boundary/cycle hypotheses: apply the homology long
exact sequence to the natural cycle-column-boundary short exact sequences, and
split the evaluated target sequences using their injective first terms. The
component docstring and node now explain these steps. Their formalization and
the total homotopy assembly remain part of the one open component theorem.

The sandbox also contained stale copies of the already updated horizontal and
vertical dependency nodes. The second reading removed these from the delivery,
preventing an accidental overwrite of newer proof metadata.

The inherited unit field is `sk-prop-av-pqf-finite`; its actual unit text is the
proper/quasi-finite geometric theorem and its `realized` arrays are empty. It
does not document the Cartan--Eilenberg route. This delivery preserves that
inherited assignment and all unit records; it makes no claim to repair that
pre-existing classification problem.

## New nodes

`lem-sp-cartan-eilenberg-double-complex-homotopy-components` records the component construction through the total homotopy identity, without the filtration conclusion.

`lem-sp-cartan-eilenberg-double-complex-homotopy-filtration` records the independent finite-supremum factorization through the second filtration. The interface change is recorded in `coord/changes/cartan-eilenberg-double-complex-homotopy-helpers.md`.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes.** I compared all three delivered modules with the
   repository versions. The target declaration is byte-for-byte unchanged; the two additional
   modules contain new helper declarations only. No existing definition or target statement was
   altered. Verdict: pass.

2. **Proof and axioms.** I compiled the three modules with `lcompile.py --all`. The target and
   filtration theorem contain no `sorry`; the component theorem is the one named split-off hole.
   The filtration proof uses only subobject factorization and finite-supremum arguments, and the
   target reduces to the two helpers. No forbidden declaration or hollow definition was added;
   the axiom probe is left to delivery preflight. Verdict: pass, with the documented component
   theorem remaining open.

3. **Split-off statements and duplicates.** I checked both helper statements against the target:
   the component theorem omits only the final filtration conclusion, while the filtration theorem
   assumes the component identity and proves only the factorization. They are therefore strict
   reductions, not restatements. The three required Mathlib/library searches found no matching
   Cartan--Eilenberg declaration, and `rg` found no duplicate in `lean/`. Verdict: pass.

4. **Pruning and imports.** The target imports the two helpers as proof-only imports. Public imports
   in each helper are needed by its signature; private imports are used by proofs. No old proof
   dependency can be removed without losing the component construction, and the unit route through
   the horizontal/vertical comparison and filtration steps is retained. Verdict: pass.

5. **DAG agreement and documentation.** The target and both helper nodes record the declarations,
   proof dependencies, proof origins, source locations, and unit consistently with the Lean code.
   The helper change record names the only user. Verdict: pass.

I changed only this report section; no Lean proof or node metadata required repair.


## Second reading by Q4

1. **Signatures and accidental changes — pass after repair.** Compared the parent
   module with the repository and checked its complete declaration signature by
   an exact string comparison: it is byte-for-byte unchanged. The two helper
   modules are new. No existing definition or statement changed. Removed the
   two stale dependency-node copies that would have overwritten newer repository
   proof metadata.

2. **Proofs and axioms — pass with one declared open theorem.** Compiled all three
   modules locally with `lcompile.py`; no errors or warnings. Scratch copies with
   `#print axioms` show only `propext`, `Classical.choice`, and `Quot.sound` for
   `cartanEilenberg_secondFiltration_factor`; the parent and component theorem
   additionally use `sorryAx`, precisely because the component theorem is open.
   There is exactly one `sorry`, the named public component theorem with its
   docstring proof and node. No forbidden declarations or hollow definitions
   occur. Reused the component theorem's total-object witnesses, removing the
   parent's redundant total constructions and its file-wide linter suppression.

3. **Split statements and searches — pass as a decomposition.** The component
   theorem is the construction/homotopy part of the original conclusion, without
   its filtration clause. The filtration helper proves that missing clause from
   the component formula for general integer-indexed double complexes. The latter
   has a complete formal proof, so the delivery proves a real proper part of the
   argument; it does not claim a net hole reduction. Checked the empty interval
   q>n, negative total degrees, and target inclusions with vertical degree above
   n-1: the empty supremum or zero source handles each case. Checked component
   vanishing at p=0 and q=0 and the signs in the total differential expansion.
   Fresh searches used all three required kinds (four tools). LeanFinder returned only generic
   null-homotopic-map constructions; Loogle returned a bifunctor homotopy helper;
   grep returned generic subobject supremum factorization lemmas. LeanSearch
   returned short-complex and bifunctor homotopy components. None states the
   component theorem or the filtered homotopy theorem. Library searches did find
   the four duplicated private helpers in `DoubleComplexTotal`; these are now
   reused. The new nodes record the actual searches.

4. **Route, pruning, and imports — pass with the inherited unit issue reported.**
   Removed the parent's unused horizontal/vertical imports; the component module
   retains both dependencies. The filtration module imports `DoubleComplexTotal`
   publicly for its statement and uses a separate proof-only `import all` for
   its existing private helpers. The remaining public imports supply notions in
   the signatures. No unit statement or realized step is bypassed or changed;
   the assigned unit's empty `realized` record and unrelated text are reported
   above rather than represented as a checked Cartan--Eilenberg blueprint route.
   No modules leave the target closure.

5. **DAG agreement — pass after repair.** The parent node now records obtaining
   total-object witnesses and applying the two helper declarations, matching its
   Lean proof. The component node keeps the horizontal and vertical proof-plan
   dependencies, and now explicitly derives the horizontal child's column
   hypotheses. The filtration node records the finite-supremum/pullback proof and
   reuse of the existing helpers. The new nodes have their source, proof origin,
   searches, Lean records, creation data, chapter, and inherited unit fields.
   The component node has no filtration conclusion; the filtration node states
   the actual typed component hypothesis without unused boundary assumptions.

Changed the parent proof and imports, removed duplicate filtration helper proofs,
expanded the component proof plan, synchronized the three delivered nodes and
search records, removed stale dependency-node copies, and corrected this report.
No additional theorem hole was closed or added during the second reading.
