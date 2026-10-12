## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal` with a complete Lean
proof from two separate steps of the Stacks 08DQ calculation. The existing theorem's
signature, universes, visibility, and docstring are unchanged. Added the proof-only
import `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationModel`.

Added `Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation`. It constructs the
unit complex, ordinary Hom dual, total tensor, specified Hom projections, and actual
summand evaluation formula. `IsLocalOrdinaryEvaluation` pins a chain map by these
components. It does not assume that the map is an isomorphism. A named theorem
states degreewise invertibility for a strictly perfect input and arbitrary F.

Added `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationModel`. Its named theorem
states a commuting square with ordinary complex models, without asserting the
invertibility of the evaluation chain map. The original proof obtains that square,
applies the degreewise theorem, promotes it to an isomorphism of complexes using
`HomologicalComplex.Hom.isIso_of_components`, localizes it, and cancels the target
comparison using `IsIso.of_isIso_comp_right`.

Updated the original node's proof, proof_deps, and proof_origin to this argument.
No existing definition, statement, public import, or instance was changed. The
abbreviation for the localized module category unfolds to the existing carrier.
The only selected data are the already specified projections of homComplex_exists;
the new existence theorem is used only by elimination in a proof of a proposition.

## Proved and sorry left

Closed the hole in
`AlgebraicGeometry.strictlyPerfect_rhom_evaluation_isIso_on_open`
(node `lem-pc-strictly-perfect-rhom-evaluation-local`). No sorry remains in the item.

Added two holes, both whole proofs of public named theorems:

- `AlgebraicGeometry.isIso_localOrdinaryEvaluation_degree`
  (`lem-pc-strictly-perfect-ordinary-evaluation`).
- `AlgebraicGeometry.strictlyPerfect_evaluation_local_model`
  (`lem-pc-strictly-perfect-evaluation-model`).

This is a decomposition: one upper hole closed and two lower holes added, not a
sorry-free proof of the mathematical result. The first statement is solely a
calculation on ordinary complexes, with no derived categories, K, N, or hP. The
second states the model square and component formula and contains no invertibility
assertion for f. The final combination is proved in Lean.

Manual edge checks: for P=0 all source and target terms are zero; rank-zero free
retracts cause no exception; on empty U the same maps are maps between zero objects.
For P=O[0], only q=r=0 contributes and the formula is the unit-action identity.
For P concentrated in degree r, the contributing dual degree is -r, and p=r+n;
the displayed transport is in the correct direction. Expanding the differential
gives d_F followed by evaluation and -(-1)^(p+q) times precomposition with d_P,
matching the Hom differential. Bounded P makes the relevant sums and products
finite even for unbounded F. No affine hypothesis was added.

## No longer needed

No original imports were removed and no globally pruned module is claimed.
The original direct proof dependency list is replaced by the two new nodes.
The following old dependencies are still needed by their statements or by the
lower calculations, rather than being bypassed:
`def-pc-canonical-derived-tensor-hom-bijection`, `def-pc-perfect-complex`,
`def-pc-scheme-derived-tensor-structure`, `def-pc-tensor-complex-sheaves`,
`def-pur-derived-internal-hom`, `def-pur-hom-complex`,
`lem-pc-bounded-above-flat-kflat-site`, `lem-pc-rhom-strict-perfect-hom`,
`lem-sc-derived-internal-hom-restrict-open`, and
`lem-sc-finite-free-internal-hom-exact`.

## Where the brief, the DAG or earlier work was wrong

The supplied plan correctly notes that the existing strictly-perfect RHom wrapper
has an affine hypothesis, whereas this item has arbitrary U. That wrapper cannot
be applied directly to U. The model-square node explicitly retains the local
cohomology-sheaf argument needed to pass from affine subopens to arbitrary U.
The existing restriction theorem supplies existence of an object isomorphism,
not the evaluation commuting square; the latter is the substantive compatibility
step that is now isolated, with the actual component formula recorded.

The local checkout contains the literature index but not the Stacks TeX files.
Read the primary-source pages at https://stacks.math.columbia.edu/tag/08DQ,
https://stacks.math.columbia.edu/tag/08DM, and
https://stacks.math.columbia.edu/tag/08DL instead. Checked the exact TeX labels in
the Stacks tags index. The unit record sk-thm-picard-duality was read; no unit or
chapter statement or route was changed.

## New nodes

`lem-pc-strictly-perfect-ordinary-evaluation`, in
`dag/nodes/sec-picard-framework/lem-pc-strictly-perfect-ordinary-evaluation.json`,
is the finite-free/retract calculation of Stacks 08DQ after passing to ordinary
complexes. Its module includes real definitions of the component formula and a
single named missing theorem.

`lem-pc-strictly-perfect-evaluation-model`, in
`dag/nodes/sec-picard-framework/lem-pc-strictly-perfect-evaluation-model.json`,
is the ordinary-model and compatibility calculation of Stacks 08DQ, 08DM, and
08DL. Its statement provides the exact commuting square needed by the item,
with no isomorphism claim about the ordinary chain map.

Searches ran through msearch: LeanSearch was unavailable with HTTP 500; LeanFinder
found Tor and tensor-summand APIs, not the needed sheaf evaluation statements;
Mathlib grep found scalar HomComplex constructions, not internal sheaf Hom.
Repository searches found the affine strictly-perfect computation and the
object-level restriction isomorphism. Blueprint searches for strictly perfect
and 08DQ found no duplicate of either new statement. No change record is needed:
all existing interfaces are preserved.

## Second reading by G1

1. Compared the delivered target module with the repository version. The target declaration signature and all existing declarations are unchanged; the only target change is a proof-only import and proof body.
2. Compiled all three delivered modules with `lcompile.py`; each compiled successfully. The only remaining `sorry`s are the two named split-off theorems, and no forbidden declarations or hollow definitions occur.
3. Checked both split-off statements against their node records, their docstrings, and the Stacks calculation. They are strictly lower-level ordinary-evaluation and model-compatibility assertions, with no added hypotheses to the target and no duplicate declaration found in the library.
4. Checked the proof route and imports. The target uses the model square, degreewise invertibility, componentwise isomorphism, localization, and cancellation exactly as written; the unit `sk-thm-picard-duality` route is retained. No unused original import was identified.
5. Checked the DAG updates: both new nodes have matching Lean declarations, proof steps, dependencies, source, unit, and chapter metadata; the target node records the realized two-step route and the decomposition.

Changes made: added this second-reading record only. No Lean statements, definitions, proofs, imports, or DAG records required repair.
