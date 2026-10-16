## What changed

Proved the body of `AlgebraicGeometry.ProEtale.condensedField_presentation_corank_eq` from the
presentation-independent geometric evaluation statement
`exists_condensedField_compatible_evaluations` in the new module
`Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation`. The parent constructs a common
geometric point using Mathlib fibre-product point surjectivity and the algebraic closure of its
residue field. It then maps both given presentations by the compatible evaluation functors,
identifies their cokernels using the natural comparison, and computes each cokernel dimension
explicitly. It also constructs all finite-free coordinate equivalences by biproduct
preservation, proves their projection and single-coordinate formulas, and derives the full
matrix equation from the regular endomorphism scalar equation. The proved private helper
`finrank_cokernel_of_matrix` identifies the categorical cokernel with its range quotient,
transports the range along the supplied coordinate equivalences, and applies rank-nullity. All
original signatures and public imports are unchanged. Added proof-only imports of the evaluation
module, Mathlib PullbackCarrier, and Mathlib's algebraic closure, ModuleCat biproducts, and
ModuleCat cokernels. Updated the parent DAG route to match the actual proof. The private helper
section and new evaluation interface are documented in
`coord/changes/B3-condensed-field-presentation-corank.md`.
The second reading added proof-only imports of SitePullbackAbelianExact and
GeometricFieldProEtaleEvaluation to the new evaluation module, to expose the declarations
used in its pending proof plan. The latter publicly imports ProfinitePointPullback.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.condensedField_presentation_corank_eq`,
node `lem-weil-pbc-condensed-field-presentation-corank`. Added one hole in
`AlgebraicGeometry.ProEtale.exists_condensedField_compatible_evaluations`, node
`lem-weil-pbc-condensed-field-presentation-evaluation`. This is a decomposition, with one hole
closed and one added; it is not a net proof. The new statement has no chosen module P, no finite
presentation, and no rank or corank conclusion. It remains to construct the internal-module
evaluation functors at the supplied common geometric point, prove their finite-colimit
preservation, compare their composites with module pullback, and verify the scalar formula for
endomorphisms of the regular module. The common-point construction, finite-free coordinates,
matrix compatibility, cokernel transport, and dimension/rank calculation have been proved in the
parent and are not left in the new hole.

## No longer needed

Removed four proof-only imports from the parent:
`Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`,
`Sheaf.CategoryTheory.SitePullbackAbelianExact`,
`Sheaf.Paper.GeometricFieldProEtaleEvaluation`, and `Sheaf.Paper.ProfinitePointPullback`.
The continuous realization is already publicly imported by PresentationMatrix. The site
exactness and geometric evaluation imports now accompany the pending proof in
PresentationEvaluation; geometric evaluation publicly imports ProfinitePointPullback.
No module or node
was pruned from the target closure. The parent's old direct proof dependencies
`lem-weil-pbc-profinite-point-pullback`, `lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-geometric-field-proetale-evaluation`,
`lem-weil-pbc-condensed-field-continuous-realization`, and
`def-weil-pbc-condensed-field-presentation-matrix` are retained as proof dependencies of the
new evaluation node. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG treated the residue-field construction and the final rank-nullity step as
elementary but provided no internal-module evaluation/matrix interface. Mathlib directly
supplies fibre-product points; this makes the common-point construction short. The finite-free
matrix argument, final rank-nullity, and categorical cokernel transport have been written
explicitly. The missing geometric interface is independent of all chosen presentations and is
now isolated. No existing statement was changed. LeanSearch was attempted but returned an
Internal Server Error; semantic/type searches and Mathlib source searches were completed, and
the unavailable service is recorded without an absence verdict.

## New nodes

`lem-weil-pbc-condensed-field-presentation-evaluation` is the fixed-geometric-point construction
of compatible additive evaluation functors, their finite-colimit preservation, natural pullback
comparison, and the regular-module scalar formula. It is in
`lean/Sheaf/AlgebraicGeometry/CondensedFieldPresentationEvaluation.lean`, with the original
source and a complete proof plan. Edge cases: arbitrary (possibly zero) finite matrix sizes are
allowed; maps from Spec(Omega) ensure the geometric schemes are nonempty. No noetherian
hypothesis or coefficient completeness is introduced.

The finite-free coordinate construction is irreducible with proved projection and
single-coordinate APIs. A separate proved scalar-to-matrix helper keeps the coefficient
realization abstract during elaboration. This avoids repeatedly unfolding the concrete monoidal
coefficient realization; no compilation limit was raised and no existing module needed
adaptation.

## Second reading by B3

1. **Existing interfaces: PASS.** Compared both delivered modules with the shared
   repository. PresentationEvaluation is new. The entire existing
   `condensedField_presentation_corank_eq` signature, from its declaration name to
   `:= by`, is byte-identical; its public import is unchanged. The original module
   gains only private helpers and a proof. No existing definition, target statement,
   hypothesis, conclusion, or public declaration was altered. The change record
   explains the private variable section and new interface.
2. **Proof and axioms: PASS as a decomposition.** Recompiled both files in import
   order after moving the old sandbox build artifacts aside, so stale upstream
   probe artifacts could not satisfy imports. Both compile without warnings. The
   only explicit `sorry` is the named new evaluation theorem; there is no forbidden
   declaration or hollow definition. Scratch `#print axioms` checks of both public
   theorems show exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is expected from the reported open evaluation statement. Read the
   projection and single-coordinate formulas, reduction to matrix entries, range
   transport, quotient rank-nullity, common-point construction, and cokernel
   comparison in the parent. The cokernel isomorphism has the required directions.
   No data definition chooses an arbitrary witness from an unproved existence
   theorem; the evaluation witnesses are eliminated inside a theorem proof.
3. **Split statement: PASS.** Matched each hypothesis and conclusion of the new
   node with Lean: arbitrary maps p,g, the fixed common algebraically closed
   geometric point, additive functors, finite-colimit preservation, a natural
   comparison on all modules over X, regular-module linear coordinates, and both
   scalar formulas. Its docstring constructs the evaluation and explains the
   module laws, colimits, comparison, and scalar calculation. For identity maps
   the two functors may be the same geometric evaluation. For zero endomorphisms
   the scalar is zero; for identity endomorphisms it is one. The maps from the
   field exclude empty V or W. Zero rows and columns remain covered by the proved
   finite-biproduct and rank-nullity arguments. There is no finite-presentation or
   corank conclusion in the split theorem: the parent proves those parts.
   Independent LeanFinder, Loogle, and source searches used ordinary evaluation,
   weak contractibility, and colimit keywords. PresheafOfModules evaluation and
   its colimit instances, ConstantInternalModuleSheafEquivalence,
   InternalModuleAbEquivalence, the ordinary weakly-contractible evaluation
   results, and upstream mapMod APIs are useful ingredients but do not supply
   this internal-module geometric scalar comparison. No quick closure or exact
   duplicate was found. The new searches are recorded in the node and search log.
4. **Route and pruning: PASS after report/import repair.** The parent first uses
   Mathlib pullback-point surjectivity and algebraic closure, then the evaluation
   interface, then Mathlib biproducts, cokernel/range quotients, and rank-nullity.
   Its only geometric hole is a genuine part of the old argument. Checked
   `dag/units/sk-thm-properbasechange.json`: neither this node nor its old
   dependencies is a realized unit statement or step, and the realized P1,
   reduction, and torsion-assembly route is unchanged. Corrected No longer needed
   to list all four removed parent imports and all five old direct proof
   dependencies. They remain available in the new node's import/proof closure;
   no module is claimed pruned. Added the missing proof-plan imports to the new
   module, using plain imports. ProfinitePointPullback is already public through
   GeometricFieldProEtaleEvaluation, so no duplicate direct import is needed.
5. **DAG agreement: PASS.** The existing node differs only in `proof`,
   `proof_deps`, and `proof_origin`. Its four steps match the actual common-point,
   evaluation/matrix, cokernel, and dimension arguments. Its sole new direct
   proof dependency is the evaluation node. The new node has the matching Lean
   signature, source, proof in words and named dependencies, searches, split
   status, creation record, blueprint origin, chapter and unit. The new theorem
   remains explicitly open; closing one upper hole and adding this lower hole
   is recorded as one decomposition and zero net holes closed.

Second-reading changes: supplied the new module's proof-plan imports, corrected
import/dependency accounting, added independent search evidence to the new node,
updated the change record, and added this review. No proof body or statement
required repair.
