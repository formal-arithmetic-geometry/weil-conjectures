## What changed

Filled `AlgebraicGeometry.isProjective_of_isProper_of_dim_le_one` in
`lean/Sheaf/AlgebraicGeometry/Curve/ProperProjective.lean`, preserving its signature and
all existing docstrings. The existing imports suffice, including their immersion
composition instances; no import is added.

The proof follows the existing node `lem-sc-proper-dim-one-projective` unchanged.
Properness supplies separatedness, local finite type, and quasi-compactness, so
`exists_closed_open_immersion_projectiveSpace_of_dim_le_one` gives `i`, `j`, and their
structure-morphism equalities. Associativity proves that the composite immersion
`i ≫ j` has structure morphism `f`. The existing projective-space properness instance
supplies separatedness of its structure morphism; `IsProper.of_comp` then makes
`i ≫ j` proper. Its range is closed by `Scheme.Hom.isClosedMap.isClosed_range`, and
`IsClosedImmersion.of_isPreimmersion` gives a closed immersion. Its witness fills
`IsHProjective`, while quasi-compactness of `f` fills the other parent of `IsProjective`.

Read the statement and proof of Stacks Tag 0A26 at
https://stacks.math.columbia.edu/tag/0A26 (the local literature source is not populated).
Read the node and its proof-dependency signatures, and the unit record
`dag/units/sk-thm-curveestimate.json`: this item is not a unit realization, and both
steps of the planned proof are retained. No node or interface change is needed.

Searches: LeanFinder for proper schemes of dimension at most one being projective
returned general properness results, not this converse. Loogle for
`AlgebraicGeometry.IsProper.of_comp` found the exact cancellation lemma. The launcher
source grep for `isProjective_of_isProper|exists_closed_open_immersion_projectiveSpace_of_dim_le_one`
returned no hits; direct repository searches found the existing quasi-projectivity
statement and the similar abelian-variety projectivity proof. The proof uses the
Mathlib declarations directly rather than importing the broader abelian-variety theory.

Validation: local `lcompile.py` compiled the final file without warnings. No extra
hypotheses, nonemptiness restriction, or positive-dimension restriction were added;
the proof also applies to empty schemes and dimension-zero schemes as stated.

## Proved and sorry left

Proved from existing declarations:
`AlgebraicGeometry.isProjective_of_isProper_of_dim_le_one`
(node `lem-sc-proper-dim-one-projective`). One of one original sorries removed.

No sorry remains in the delivered module. No new module, theorem, or sorry is added.
The existing dependency
`AlgebraicGeometry.exists_closed_open_immersion_projectiveSpace_of_dim_le_one`
(node `lem-sc-dim-one-quasi-projective`, module
`Sheaf.AlgebraicGeometry.DimOneQuasiProjective`) remains to be proved by its own worker;
it is not changed by this delivery. This is a reduction to that existing dependency,
not a claim that all transitive proof obligations are closed.

## No longer needed

None. No import was removed, and every planned proof dependency is still used.
All public imports support the unchanged statement; the existing proof-only import
supplies quasi-projectivity. The second reader removed the redundant newly added
`Mathlib.AlgebraicGeometry.Morphisms.Immersion` import; no original import was pruned. No node or module of the
planned argument can be pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The quasi-projectivity signature gives a closed/open
factorization rather than a single immersion; Mathlib composition instances bridge
this directly. The projective space used here is the existing relative base-change
model; its properness instance provides the separatedness needed for cancellation.
This is consistent with the original proof route and requires no statement change.


## Second reading by P1

1. Compared the delivered module with the repository using `diff -u`. The sole existing
   theorem signature, universe, namespace, and all docstrings remain byte for byte
   unchanged. No definition, public import, or target statement changes; no change
   record is required. Verdict: pass.
2. Compiled the delivered file locally without errors or warnings. A scratch copy with
   `#print axioms AlgebraicGeometry.isProjective_of_isProper_of_dim_le_one` reports
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The module has no
   remaining sorry or forbidden declaration. The existing quasi-projectivity theorem
   remains open and accounts for the transitive sorry. Verdict: pass as a reduction.
3. There are no split-off statements or new nodes. Inspected the existing dependency's
   signature: it supplies exactly the closed/open factorization over the field. The
   argument imposes no nonemptiness or positive-dimension assumption, and also applies
   to empty and zero-dimensional schemes and projective space with N = 0. Verdict: pass.
4. Read the proof top down and searched independently for proper immersions into
   projective space with LeanFinder, the closed-preimmersion criterion with Loogle,
   and corresponding declarations in both library roots with rg. The existing
   upstream `IsClosedImmersion.of_comp_of_isSeparated` packages the same final
   argument but requires a broader upstream import; the present short direct proof
   needs no additional imports. Tested removal of the newly added immersion import
   in a scratch copy: compilation succeeds. Removed that redundant addition. All
   old proof dependencies remain used, so no old node or module is pruned. The unit
   `sk-thm-curveestimate` realizes `thm-sc-proper-cohomology`, not this item, and its
   route is retained. Verdict: pass after import cleanup.
5. Read `lem-sc-proper-dim-one-projective` and its dependency records. Properness supplies
   the first step's hypotheses; the second step uses projective-space separatedness,
   cancellation of properness, closed range, the closed-preimmersion criterion, and
   the projectivity definition exactly as planned. Its `proof`, `proof_deps`, and
   literature `proof_origin` agree with this implementation; no node edits are
   needed. Verdict: pass.

Changed only the redundant newly added proof import and this report. The original
worker's proof is correct and was preserved.
