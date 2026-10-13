## What changed

Replaced the single hole in `Sheaf.RingTheory.ArtinianFlatSubalgebras` with a compiling
reduction following Stacks Tag 07FG. The main module constructs the family as the range
of an explicit finite-coefficient construction, proves its monotonicity and directedness,
proves coverage from generation, and proves the complete algebra-map universal property
using Mathlib `Subalgebra.iSupLift`, including uniqueness and all stated universes.
The existing theorem signature and public imports are unchanged.

Added `Sheaf.RingTheory.ArtinianCoefficientPresentation` with the explicit definition
`Algebra.artinianCoefficientSubalgebra` and the coefficient-field claim (parent steps 1–8).
Added `Sheaf.RingTheory.ArtinianCoefficientDescent` for the algebraic descent argument
(parent steps 8–11). These are distinct mathematical parts of the argument, not restatements
of the directed-colimit conclusion. Updated the parent node's proof and dependencies.

## Proved and sorry left

Closed the original hole in `Algebra.exists_directed_artinian_flat_subalgebras`
(node `lem-weil-pbc-popescu-artinian-flat-subalgebras`) by decomposition. Its proof has no
remaining hole. It still depends on the following two newly named holes:

- `Algebra.exists_artinian_coefficient_presentation`
  (`lem-weil-pbc-artinian-coefficient-presentation`): adjusted residue-field section,
  maximal-ideal generators and finite coefficient containment, together with generation.
- `Algebra.exists_artinian_coefficient_descent`
  (`lem-weil-pbc-artinian-coefficient-descent`): descend the relations and obtain the
  flat Artinian local essentially finite type properties at every finite coefficient stage.

Both proofs are exactly `by sorry`. This closes one upper hole and adds two lower holes:
a decomposition, not an axiom-free proof or a positive net hole reduction.
`Algebra.artinianCoefficientSubalgebra` is a real algebra-adjoin construction with no hole
and no witness selected from an unproved theorem. Witnesses of the intermediate theorems
are eliminated only inside the main theorem proof.

Edge cases checked mathematically: when the maximal ideal is zero, t can be empty, sigma
is the inverse residue isomorphism, c can be empty, and the stages are the finitely generated
intermediate fields. Empty finite coefficient sets still produce a nonempty family indexed
by all finite sets. For dual numbers, taking t={epsilon} makes the construction the expected
truncated polynomial algebra over each coefficient field; its maximal ideal extends correctly.
Non-k-linear coefficient sections are handled by ring closure in the presentation hypothesis:
using algebra closure there instead would make that hypothesis automatic and the descent false.
The descent lemma does not assume characteristic or finite H1; those are used solely in
constructing the adjusted presentation. No target, definition or existing statement changed.

All three delivered Lean files compile locally with the prescribed launcher, without warnings.

## No longer needed

Removed the main module's proof imports:

- `Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`
- `Sheaf.RingTheory.ExistsLiftOfFieldCharP`
- `Sheaf.RingTheory.JacobiZariskiHomologySequence`

These are relocated proof obligations of the two intermediate statements, not globally pruned
mathematics. In particular their nodes remain needed for the coefficient claim/descent proofs.
The original twelve-step dependency set is now reached through those two nodes: no original
mathematical node is claimed globally unnecessary. No blueprint unit statement or realized step
is bypassed. Added proof imports are `Sheaf.RingTheory.ArtinianCoefficientDescent` and
`Mathlib.Algebra.Algebra.Subalgebra.Directed`. Public imports retained for the original interface.

All old direct `proof_deps` are replaced at the parent node (retained within the two
intermediate proof plans):

- `lem-weil-pbc-artinian-local-noetherian-nilpotent`
- `def-weil-pbc-noetherian-ring`
- `def-weil-pbc-mv-polynomial-ring`
- `def-pc-field-extension`
- `lem-weil-pbc-field-char-p-nilpotent-lifting`
- `def-weil-pbc-kahler-differentials`
- `lem-weil-pbc-jacobi-zariski-homology-sequence`
- `def-weil-pbc-smooth-ring-map`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-tensor-quotient-base-change`
- `lem-weil-pbc-field-extension-base-change-faithfully-flat`
- `def-weil-pbc-faithfully-flat-ring-map`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `def-weil-pbc-flat-ring-map`
- `lem-weil-pbc-finite-dim-algebra-artinian`
- `def-weil-pbc-finite-type-algebra`
- `def-weil-pbc-essentially-finite-type-algebra`
- `lem-weil-pbc-artinian-local-essentially-finite-type-residue`

Second reading also removed redundant direct imports `Mathlib.RingTheory.Adjoin.Basic`
and `Mathlib.RingTheory.Ideal.Span` from the new presentation module. Their declarations
are already available through its other statement imports.

## Where the brief, the DAG or earlier work was wrong

The original dependencies state field lifting, Jacobi–Zariski, and the residue finite type
criterion, but not the coefficient adjustment claim or the descent of the polynomial relations.
Those two substantial missing combinations are now explicitly stated, rather than treating the
existing dependencies as if they already supplied the parent theorem.

The specified local `literature/stacks-project/smoothing.tex` is absent in this clone. Read
Stacks Tag 07FG directly at https://stacks.math.columbia.edu/tag/07FG and matched its paragraphs
with the complete source proof recorded in the parent node. No source error or disputed statement
was found. LeanSearch returned Internal Server Error; this is recorded as unavailable, with no
verdict inferred. LeanFinder, Loogle and source grep found no direct proof of either combination.
The similar private section helper in FirstOrderPowerSeriesComparison only supplies an unadjusted
section for complete rings and does not provide the finite-coefficient claim needed here.

## New nodes

`def-weil-pbc-artinian-coefficient-subalgebra` records the explicit k-algebra adjoin construction
from a fixed ring map sigma, finite ideal generators and finite residue coefficients. It lives
in ArtinianCoefficientPresentation with its theorem; it has no proof obligation.

`lem-weil-pbc-artinian-coefficient-presentation` records the coefficient adjustment claim from
Tag 07FG and the generation consequence. Its proof follows the original induction, lifting,
Jacobi–Zariski and finite differential-support argument, with the source proof in its docstring.

`lem-weil-pbc-artinian-coefficient-descent` records relation descent and the local Artinian/flat/
essential finite type conclusions for an explicit finite coefficient stage. Its proof follows
Hilbert basis, tensor quotient base change, faithful flatness, nilpotence and Tag 07DT (3).
No change records or forced adaptations are required.

## Second reading by R2

1. **Interface: PASS.** Compared the main module with the repository by `diff` and the
   declaration parser. The sole existing signature is byte for byte unchanged, as are
   existing public imports; no definition or target statement was modified. The added
   modules contain exactly the reported construction and two intermediate statements.
2. **Proof and axioms: PASS as decomposition.** Compiled all three modules in import order
   using `lcompile.py`, without errors or warnings. Read every proof step, including
   monotonicity, nonempty directed coverage, construction of the universal map, restrictions
   and uniqueness. Scratch-copy `#print axioms` for all four public declarations gives only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the three theorems, exactly
   as expected from the two reported holes. The explicit definition has no `sorryAx`.
   No forbidden trust mechanism or data chosen from a holed existence theorem occurs.
3. **Split statements: PASS.** Independently checked the presentation induction and
   relation descent against https://stacks.math.columbia.edu/tag/07FG and the essential
   finite type step against https://stacks.math.columbia.edu/tag/07DT. Checked fields
   (zero maximal ideal), empty finite sets, dual numbers, and non-k-linear sections.
   Ring closure in the containment hypothesis is essential; algebra closure would be
   vacuous. Descent also works in characteristic zero once a section satisfying the
   hypotheses is given. Neither hole restates the directed union or universal property.
   Each has a complete source-based docstring and node. Independent LeanFinder search for
   descending finite polynomial relations to residue subfields, Loogle search for
   `Subalgebra, Directed, _ →ₐ[_] _`, Mathlib grep for residue sections/coefficient fields,
   and project grep found no replacement for either hole. Loogle confirms the existing
   `Subalgebra.iSupLift` route is the appropriate direct route for the colimit step.
   The characteristic-zero `IsLocalRing.exists_residue_section` supplies no adjusted
   finite-coefficient containment, so it cannot close the presentation hole.
4. **Route and pruning: PASS.** The main proof uses the two strict parts of the original
   argument and Mathlib for directed supremum gluing. The three old Sheaf proof imports
   are absent and their mathematical obligations occur in the lower proof plans. Listed
   every replaced old parent dependency explicitly above. Read `sk-thm-p1.json`'s
   `realized` field: this lemma is below its realized steps; none of those steps or the
   unit route is bypassed. No shorter proof of either substantial hole was found that
   could be completed in a few minutes. Removed two redundant imports in the new module.
5. **DAG: PASS.** The parent changes only `proof`, `proof_deps`, and `proof_origin`, and
   its new route matches the actual Lean proof. New records include source, complete proof
   plans and dependency unions, searches, origin, split status, creation, blueprint, unit,
   chapter, and matching Lean declarations. The construction node has an empty proof plan
   because its definition is explicit. All eighteen old parent dependencies are accounted
   for in the union of the two lower plans.

Second-reading changes: removed two redundant imports from the new presentation module;
expanded the pruning inventory to name every replaced old parent dependency; added this
independent review. No theorem, definition, or proof body required repair. The accounting
remains one original hole closed by decomposition and two lower holes added, net minus one.
