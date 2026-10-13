## What changed

Proved `AlgebraicGeometry.Scheme.perfect_universalH0_bottom_model` with its original
signature and docstring unchanged. The single delivered module adds proved private
helpers for the residue rank, affine chart refinement, and bottom differential.
The proof uses the existing finite-free residue model and derived open-pullback
homology theorem. It constructs the refined complex by exact restriction, rather
than choosing data from a new existence statement. All new imports are proof-only.
The node's proof and proof dependencies now describe the compiled proof.
The conservative preflight command-scope check is documented in
`coord/changes/perfect-universal-h0-bottom-model-proof-scope.md`; no exported
signature, visibility, notation, attribute, or public import changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.perfect_universalH0_bottom_model`
(node `lem-sc-perfect-universal-h0-bottom-model`). No `sorry` remains in the
module, no holes were added, and no statements were split off. Every private
helper is proved, including the square-matrix argument via Mathlib transpose
injectivity. The theorem still depends on existing library declarations in its
import closure; this delivery does not claim those dependencies are axiom-free.

Validation: the module compiles through lcompile.py with no warnings. The rank-zero
source and target are included in the finite-index matrix proof; the zero free
sheaf is proved zero from its universal property. An empty scheme has no point s.
No reducedness, separatedness, or positive rank assumption is introduced.

## No longer needed

No original public import was removed: all express types in the existing statement.
Two redundant proof imports tried during development were removed:
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
The proof no longer needs `lem-pc-derived-pullback-open-restriction-universes`
(`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`): it uses the
more direct `lem-pc-derived-open-pullback-homology` instead. The residue-model
node and square-injective-free-map Mathlib leaf remain needed. The draft helper
modules were consolidated into proved private helpers and are not delivered.
No other planned node or original module is pruned.

## Where the brief, the DAG or earlier work was wrong

The planned route is mathematically sound. The stated open-restriction comparison
is more general than this proof needs, so the proof uses the direct homology
comparison. The residue-rank dimension and chart-restriction glue needed explicit
Lean proofs. In particular, derivedFiberCohomology and moduleSpecΓFunctor have
separately packaged scalar actions; an explicit identity linear equivalence proves
their dimensions agree. No existing definition, statement, visibility, or target
was changed. The added namespace openings and elaboration settings are recorded
in `coord/changes/perfect-universal-h0-bottom-model-proof-scope.md` because
the static checker conservatively treats them as interface commands. The theorem-of-cube unit route is preserved.


## Second reading by M2

1. **Unchanged interface — pass.** Read the complete repository/sandbox diff.
   The existing theorem signature and its existing docstring are byte-identical.
   No existing definition, visibility, attribute, notation, or public import
   changes. Added imports are proof-only. The scope-command change record
   correctly describes local namespace openings and elaboration options; these
   do not change the exported statement. No other module is delivered.
2. **Proof and axioms — pass.** Independently compiled the module with lcompile.py
   (32.2 seconds, no warnings). A scratch copy prints axioms for all seven private
   declarations and the public theorem. All private declarations use only
   propext, Classical.choice and Quot.sound. The public theorem additionally uses
   sorryAx through pre-existing dependencies, not a hole in this delivery.
   No sorry or prohibited declaration/attribute occurs in the delivered module.
   restrictFreeIso is a composition of explicit canonical isomorphisms, not an
   arbitrary existence witness. The refined complex is termwise exact restriction.
3. **Split statements and edge cases — pass.** No statements are split off and no
   new holes or nodes are added. Read the private helper statements and proofs:
   the square source/target ranks are essential and match, zero ranks work through
   Fin.elim0 and the matrix criteria, and the residue scheme is nonempty because
   its field is nontrivial. Empty S admits no s. Nonreduced rings are allowed.
   Independent leanfinder, loogle and grep searches found no shorter scheme-level
   result. Read the upstream field-rank equivalence in FreeComplex: it needs a
   Module.Finite instance, while the current direct trivialization proof derives
   the dimension without this extra prerequisite. The matrix proof uses the
   existing Mathlib leaf rather than introducing a duplicate theorem.
4. **Route and pruning — pass.** Checked the old proof_deps, their statements,
   the new imports, and dag/units/sk-prop-av-cube.json. The residue-model and
   square-injective-map route is retained; only the general open-pullback
   comparison is replaced by the direct homology comparison. No unit statement
   or step is bypassed; this supporting node is not a unit realization entry.
   Every removed old dependency is named under No longer needed. All four added
   proof imports supply declarations used in the proof; original public imports
   remain needed for the statement. Source checks against Stacks Tags
   [0BDL](https://stacks.math.columbia.edu/tag/0BDL),
   [0BCD](https://stacks.math.columbia.edu/tag/0BCD), and
   [0EWY](https://stacks.math.columbia.edu/tag/0EWY) confirm the cited route.
5. **DAG agreement — pass.** The existing node changes only proof, proof_deps and
   proof_origin. The dependency union equals the uses of its four proof steps.
   Each step matches the actual residue vanishing, rank refinement, strict
   perfectness, and square-matrix argument. Statement, lean record, unit and
   blueprint remain unchanged. There are no new-node records to check.

Second reading changed only the new private rank-refinement helper's explanatory
proof docstring: it now describes the actual single restriction after choosing
an H0 trivializing chart, rather than suggesting two successive refinements.
No Lean proof or existing API docstring needed repair. Appended this review.
