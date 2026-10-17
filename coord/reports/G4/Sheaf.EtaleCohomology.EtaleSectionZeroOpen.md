## What changed

Proved `AlgebraicGeometry.Scheme.etale_section_zero_open` completely. The proof applies the existing
`AlgebraicGeometry.exists_etaleSections_equal_open_etale_criterion` to the underlying sheaf of sets,
then identifies equality with the zero section, uses the open-immersion range formula, and proves the
geometric-stalk equivalence with the filtered-colimit point APIs `toPresheafFiber_eq_iff'` and
`toPresheafFiber_w`. Added the proof-only import
`Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion`; retained the public étale-point import.
Updated the copied DAG node to record this proof route and its actual dependencies. The required change record is `coord/changes/G4-etale-section-zero-open.md`.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.etale_section_zero_open`.
No holes remain and no holes were added. No theorem was split off.

## No longer needed

Removed the original proof-only imports `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`,
`Mathlib.CategoryTheory.Filtered.Final`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures`, and
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits`.

The original multi-step DAG route through étale cancellation, open-map descent, affine pointed
neighbourhood indexing, full-subcategory cofinality, and filtered module colimits is not needed by
this Lean proof. The retained direct proof dependencies are
`lem-weil-pbc-etale-sections-equal-open-etale-criterion` and
`def-weil-pbc-geometric-stalks`; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned Stacks proof is mathematically valid, but it is unnecessarily long for the current
library: the already proved agreement-open theorem packages the first two clauses, while the
pointed étale stalk API packages the remaining colimit argument. No target statement or definition
was changed.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

The source compiles with `lcompile.py --all`, has no `sorry`, and preserves the target signature.
The proof uses only the agreement-open theorem, the étale point/stalk APIs, and open-immersion
range/lifting facts. The copied node records the changed proof route and dependencies. No target,
definition, or imported public interface was changed.

## Second reading by G4

1. **Signatures:** Compared the delivered module with the repository version. The theorem statement,
   declaration name, visibility, and all existing declarations are byte-for-byte unchanged; only
   proof imports, namespace opens, and the proof body differ. Verdict: pass.
2. **Proof and axioms:** Compiled the sandbox with `lcompile.py --all`; it is error- and warning-free,
   contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and the theorem's
   axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Statements and split-offs:** No theorem was split off and no new node was added. The existing
   agreement-open and pointed-stalk APIs are applied with the original hypotheses and conclusion;
   no Mathlib or upstream duplicate was introduced. Verdict: pass.
4. **Route and pruning:** The proof follows the unit route through the agreement-open criterion and
   geometric-stalk APIs, while pruning the four unused proof-only Mathlib imports. The `realized`
   unit route remains intact and the report lists all removed dependencies. Verdict: pass.
5. **DAG agreement:** The copied node's proof steps, `proof_deps`, and `proof_origin` match the Lean
   proof; its statement and statement dependencies are unchanged. Verdict: pass.

Changed during second reading: appended this review record only; no Lean, DAG, or change-record
   repairs were necessary.
