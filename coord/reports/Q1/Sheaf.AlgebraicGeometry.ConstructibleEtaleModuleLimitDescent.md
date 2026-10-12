## What changed

Proved `AlgebraicGeometry.Scheme.exists_constructible_etaleModuleSheaf_descent` with its
signature unchanged. The proof establishes qcqs of the given limit cone using Mathlib,
uses the existing affine free finite-presentation theorem, descends its arrow, and takes
its cokernel. The isomorphism to F is the composition of Mathlib's cokernel-preservation
isomorphism, the isomorphism induced by the descended commuting square, and uniqueness
of the colimiting cokernel cofork supplied by the presentation theorem.

Added `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`, with the proved
comparison `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff`. It copies the
identical stratification data and applies the first equivalence of the existing
`finite_locally_constant_module_values_iff` on every stratum. This enables the source
library's proved `IsConstructibleSheaf.cokernel` theorem to supply constructibility.
It uses the existing finite-values theorem, which remains an intended stage-3 dependency.

Added `Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent` for the remaining part:
descent of an arbitrary arrow between finite sums of affine etale free sheaves to an
arrow between constructible sheaves. It groups original steps 3-6 and constructibility
of their two descended objects in step 7. It does not mention F, any presentation of F,
or any cokernel. Thus it is strictly the arrow-descent part of the argument.

All imports added to the original module are proof-only. Its original public import is
unchanged. Updated its DAG proof, proof_deps and proof_origin; added records for the two
new modules. No existing definitions or statements changed, and no change record is needed.

Local compilation in import order passed for all three modules. Lines are at most 100
characters. The prescribed deliver3.py dry run is the final validation.

## Proved and sorry left

Original module: proved 1 of 1 original sorries:
`AlgebraicGeometry.Scheme.exists_constructible_etaleModuleSheaf_descent`, node
`lem-weil-pbc-constructible-module-limit-descent`. No sorry remains in that module.

New module: proved `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff`, node
`lem-weil-pbc-constructible-etale-module-sheaf-comparison`. No sorry in this module.

Exactly one new sorry remains:
`AlgebraicGeometry.Scheme.exists_affine_free_etaleModule_arrow_descent`, node
`lem-weil-pbc-affine-free-etale-module-arrow-descent`, in
`lean/Sheaf/AlgebraicGeometry/AffineFreeEtaleModuleArrowDescent.lean`.
It is a public named theorem with its entire proof `:= by sorry`, a source, and a complete
natural-language proof. The existing finite presentation and finite-values equivalence
also remain dependencies; this delivery does not alter their proofs.

Edge cases checked for the new statement: empty families give zero sums and require
only Nonempty I; zero arrows require no extra condition; a singleton system gives
an arrow at that stage; the zero ring and empty limit pose no additional assumption.
For the proved comparison, the records agree literally on domains and immersions,
and the finite-values equivalence applies without nonempty-stratum assumptions.

## No longer needed

No import was removed from the original module, which previously imported only the
constructibility definition. Removed the redundant proof-only import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` during the second reading;
its cokernel-preservation interface is already imported by KernelCokernel.
All remaining added imports are used.

The old parent `proof_deps` absent from its new direct dependencies are all listed here:

- `lem-weil-pbc-limit-affine-transition`, `lem-weil-pbc-affine-morphism-permanence`,
  `lem-weil-pbc-qcqs-morphism-permanence`: the given cone's projection affineness and
  qcqs are proved directly by Mathlib. No existential replacement cone is used.
- `def-weil-pbc-scheme-conventions`, `def-weil-sheaf-of-modules-category`,
  `def-weil-pbc-etale-constructible-sheaf`: foundational interfaces remain in the
  unchanged statement and its public imports; they are not separate proof steps.
- `def-weil-presheaf-modules-sheafification`, `lem-weil-pbc-free-yoneda-presheaf-module`,
  `lem-weil-pbc-affine-etale-site-colimit`, `lem-weil-pbc-inverse-image-free-etale-module`,
  `lem-weil-pbc-limit-pullback-sections-colimit`, `lem-weil-pbc-inverse-image-composition`,
  `lem-weil-pbc-etale-free-sheaf-constructible`, `prop-constructible-pullback`: retained
  through the new arrow-descent node's plan, not globally pruned.
- `prop-weil-pbc-inverse-image-modules-exact`,
  `lem-weil-pbc-inverse-image-module-adjunction`: not used in the final cokernel argument;
  the ModuleCat-valued upperStar's existing left adjunction supplies preservation.
  The free-sheaf dependency's own route may still use the module adjunction stack.

This describes pruning of this proof only, not removal from every target's closure.

## Where the brief, the DAG or earlier work was wrong

The planned use of `thm-constructible-serre` is not a direct Lean application:
its declaration uses `IsConstructibleSheaf`, whereas this item's signature uses
`IsConstructibleEtaleModuleSheaf`. These mathematically equivalent predicates needed
an explicit comparison. The already stated finite-values equivalence makes that
comparison a complete short proof; no duplicate cokernel-closure sorry was added.

The inverse-image exactness theorem recorded in the DAG is about SheafOfModules over
constant ring sheaves. The actual finite presentation and target use ModuleCat-valued
sheaves. The final step needs only the existing left adjoint on the latter category;
there is no need to invoke or translate the ringed-site exactness theorem there.

LeanSearch returned Internal Server Error for both new-node searches; real failures
are recorded in searches.jsonl and in the nodes as unavailable. LeanFinder and Mathlib
grep were available and found no matching theorem. Repository search found the
finite-values equivalence and the source library's cokernel theorem, both used.

The local checkout has no literature/stacks-project/etale-cohomology.tex. The relevant
source statements and proofs were read at the official Stacks pages
https://stacks.math.columbia.edu/tag/09YU,
https://stacks.math.columbia.edu/tag/095N, and
https://stacks.math.columbia.edu/tag/03RZ. The source paths in the DAG retain their logical
repository locations; no repository file was written. The unit sk-thm-p1 and all its
realized statements/steps are unchanged; this is a split below its unit level.

## New nodes

`lem-weil-pbc-affine-free-etale-module-arrow-descent` states just the descent of a finite
free arrow, with constructible source and target and a commuting square of pullback
isomorphisms. Its five proof steps group the existing object/section descent plan.
Its source is Stacks 09YU (3) via 095N and the parent's steps 3-7. It is the one remaining
new item to prove, not a renamed form of the original theorem.

`lem-weil-pbc-constructible-etale-module-sheaf-comparison` is proved by transporting
stratifications and applying `lem-weil-pbc-finite-locally-constant-module-values` on
strata. It supplies the exact interface needed for the source cokernel theorem.
Both nodes inherit chapter sec-proper-base-change and unit sk-thm-p1; their complete
Lean signatures and actual Mathlib searches are recorded. There are no change records.

## Second reading by Q1

1. Compared the original module against the repository with diff and checked its complete
   declaration signature: byte-for-byte unchanged. No existing definition changed; only
   proof imports, proof text and explanatory comments were added. The two other modules
   are genuinely new declarations, recorded in new nodes. Verdict: pass.
2. Compiled all three files locally in import order, and compiled scratch copies with
   `#print axioms` for every delivered theorem. Each reports only propext,
   Classical.choice, Quot.sound and sorryAx. The latter is expected from the named
   arrow-descent theorem and existing open finite-presentation/finite-values dependencies.
   Scanned for forbidden declarations and hollow definitions: none. The sole delivered
   sorry is the complete proof of the public arrow-descent theorem. Verdict: pass.
3. Read the arrow-descent statement and its five-step docstring against Stacks 09YU,
   095N and 03S8. Finite free sums descend by object descent, sections descend individually,
   directedness brings the finite choices to one stage, and generator comparison proves
   the square. The finite ring is Noetherian; the affine objects and qcqs base meet 03S8.
   Checked empty source/target families, a singleton system, zero coefficients and empty
   schemes; none requires an added hypothesis. This lemma contains neither the original
   F nor a cokernel, so it is strictly an intermediate part, not a restatement.
   Read the comparison proof and both stratification definitions: it transports precisely
   the same data and uses the existing finite-values equivalence on each stratum.
   Independent LeanFinder search for morphism descent returned quasicoherent presentation
   results, which do not apply; Loogle does not index IsConstructibleSheaf. Mathlib grep
   and repository searches found no duplicate comparison or free-arrow descent theorem.
   The arrow proof requires a substantial section/base-change construction and is not a
   few-minute closure. Verdict: pass, one split remains.
4. Read the proof from the target downward: Mathlib establishes qcqs directly, the existing
   presentation theorem supplies the cokernel, and the source library's proved cokernel
   theorem plus preservation/uniqueness completes the reduction. Removed the redundant
   proof import of Preserves.Shapes.Kernels and recompiled successfully. The arrow module's
   colimit import is needed for its statement's coproduct instances. Expanded No longer
   needed to list every old direct dependency absent from the new parent proof, including
   those retained through arrow descent. Checked sk-thm-p1.realized: neither this node nor
   either new node replaces a realized unit step. Verdict: pass after repairs.
5. Checked all three node records against their Lean signatures and proof steps. New nodes
   have source, natural-language proof, search records, creation, blueprint, chapter/unit
   and full Lean records. Corrected the parent's proof/proof_deps to omit projection and
   composition nodes whose declarations its Lean proof does not use: the projection facts
   come from Mathlib, and the last step uses cokernel preservation rather than composition
   of scheme inverse images. proof_deps is the union of the remaining step uses.
   Verdict: pass after repairs.

Second-reading changes: one redundant proof import removed; parent DAG dependencies
corrected; exhaustive local-pruning list and this independent reading appended. No theorem
statement, definition, or remaining split statement changed.
