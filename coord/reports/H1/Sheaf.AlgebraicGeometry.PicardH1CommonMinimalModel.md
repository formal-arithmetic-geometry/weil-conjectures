## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.picard_h1_common_minimal_model`
with a complete Lean reduction. The existing signature and public imports are unchanged.
The theorem now obtains one target neighbourhood for each i, takes their finite
intersection, proves perfectness of the source direct image from
`perfect_derivedDirectImage_baseChange`, and applies the existing
`exists_finiteFreeResidueModel`. The private proved helper `refine_residue_model`
restricts that actual complex to an affine open inside the common neighbourhood.
It transports every term isomorphism, the derived comparison and both bounds.
The proof constructs both section frames from the free-module isomorphisms and
applies a generic residue-differential statement to the actual section e0.symm(1).

Three strictly smaller statements are in three new modules: one-bundle local descent,
marked-source-fibre Betti numbers, and a residue calculation for a given bounded
free complex. None asserts existence of the common minimal model or rephrases
its hypotheses and conclusion. Perfectness, finite intersection, affine refinement,
section bases and assembly are proved here rather than moved into these holes.
All new statements have source references, complete proofs in words, and DAG nodes.

Added proof imports for these three modules, the invertibility bridge in
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`, the free-section
linear equivalences, and the affine-open basis. The adjoint-comparison proof supplies
the additive tensor-pullback family required by the current perfectness interface.
The original commutative-diagram hypothesis hui is retained verbatim but not needed
by these separate one-bundle arguments; its unused-variable linter is disabled
locally on the existing theorem. No definition, statement, universe or visibility
was changed, and no other existing module was adapted.

The source read was Stacks Tags 0BF2 and 0BCD on the official Stacks site, with
the existing 0B91 and field-rank declarations read in full. Searches covered both
library roots, the DAG, and the imported blueprint with finite free, residue,
line bundle and trivial rank queries. Logged LeanFinder searches found general
rank/local-freeness and homological-complex APIs, not these geometric statements.
Loogle found finite-rank invariance tools. All three LeanSearch queries returned
Internal Server Error; they are recorded as unavailable, not negative results.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picard_h1_common_minimal_model`
(node `lem-sc-picard-h1-common-minimal-model`). Its proof now compiles from named
statements. This is a decomposition, not an unconditional sorry-free proof.

The two private lemmas `invertible_directImage_isPerfect` and
`refine_residue_model` have complete proofs with no sorry. The main module has
zero sorries. Exactly three holes are added, each as the entire proof of a named
public theorem in its own new module:

- `AlgebraicGeometry.Scheme.exists_descendedInvertible_neighbourhood`
  (`lem-sc-descended-invertible-neighbourhood`).
- `AlgebraicGeometry.Scheme.picard_directImage_fibre_betti`
  (`lem-sc-picard-direct-image-fibre-betti`).
- `AlgebraicGeometry.Scheme.residueRankModel_differential_eval_eq_zero`
  (`lem-sc-residue-rank-model-differential`).

Thus holes closed: 1; holes added: 3; the net is -2 before any downstream pruning.
Existing imported theorems may still depend on their own recorded holes. Their
proofs were not changed and are not counted as newly proved here.

Edge cases checked in the argument: n=0 makes the finite intersection top; no
target witnesses are needed. A marked point excludes an empty W. The universal
structure-unit hypothesis rules out empty marked source or target fibres; rank
zero descent cannot have invertible pullback on such a nonempty fibre. The source
fibre over a field has H0 dimension one even without a chosen trivialization.
For m=0 the section-frame equivalence still exists and the final coordinate
condition is vacuous. The generic residue lemma also allows beta0=0 and makes no
rank-one or negative-vanishing assumption: for a two-term field complex with a
nonzero differential, the cohomology dimensions are strictly below term ranks,
so its hypotheses fail rather than asserting a false vanishing. The affine
refinement retains all degrees and boundedness, not merely degrees zero and one.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial` from the assigned module.
Its node `lem-sc-field-pullback-rank-one-trivial` is still required by the new
marked-fibre subargument and is imported there; it is not pruned from the closure.
The parent node now cites the smaller fibre statement instead of this lower node.

No module or mathematical node is asserted to be globally pruned. The two
original substantive proof imports `PerfectDirectImageBaseChange` and
`PerfectFiniteFreeResidueModel` are actually invoked and retained. All original
public imports are retained to preserve the public interface. The unit record
`sk-prop-av-cube` has no realized entry for this subordinate statement; this
reduction follows the same 0BF2 source argument and bypasses no unit step.

## Where the brief, the DAG or earlier work was wrong

The original plan did not have named statements for one-bundle neighbourhood
descent, the marked-fibre cohomology calculation, or residue differential vanishing.
These are substantive gaps between its existing declarations, now explicit as
three independent items. The current perfect direct-image theorem also requires
an additive tensor-pullback family and sheaf-level finite presentation; both are
supplied here by proved adjoint uniqueness and the invertibility bridge.

No mathematical error or false statement was found. No arbitrary data are defined
by choosing a witness of an unproved existence theorem. Existential choices of
complexes, neighbourhoods and frames occur only inside the proof of the theorem.

## New nodes

`lem-sc-descended-invertible-neighbourhood` is the single-target rank-one descent
step. It permits any base map and requires no derived-category or source-model
data. Its universally quantified restriction conclusion supports the finite
intersection in the parent proof. Module: `DescendedInvertibleNeighbourhood`.

`lem-sc-picard-direct-image-fibre-betti` is just the marked-source-fibre calculation,
with no target family or model construction. Its two assertions are negative
Betti vanishing and degree-zero Betti number one. Module: `PicardDirectImageFibreBetti`.

`lem-sc-residue-rank-model-differential` concerns a given generic bounded free
representative, not a geometric direct image. It tests any section in degree zero
and any finite section frame in degree one. Module: `ResidueRankModelDifferential`.

All three nodes lie in `dag/nodes/sec-abelian-varieties/`, use the parent's chapter,
unit and blueprint ancestor, and record actual logged searches. The parent node's
proof, proof_deps and proof_origin describe the implemented reduction.
There are no change records or forced adaptations.

## Second reading by H1

1. **Repository comparison.** I diffed the delivered parent module and node against
   the repository versions. The theorem signature and all existing declarations are
   unchanged; only the author line, imports, proof, and DAG proof metadata changed.
   Verdict: pass.
2. **Compilation and proof hygiene.** I compiled all four delivered modules with
   `lcompile.py --all`. They compile without errors. The only remaining `sorry`s are
   the three named split theorems above; there are no axioms, unsafe declarations,
   hollow definitions, or forbidden implementation attributes. Verdict: pass.
3. **Split statements.** I checked each new theorem against its docstring, node,
   edge cases, and imported declarations. The three statements are strictly smaller
   reductions and are not restatements of the parent target; each has a matching node
   and source/proof metadata. Verdict: pass, with the stated decomposition of one
   parent hole into three lower holes.
4. **Pruning and route.** The parent proof uses the new lemmas, perfect direct-image
   and finite-free model results, and the required tensor-pullback bridge. The removed
   direct import of `FieldPullbackRankOneTrivial` is still retained where the fibre
   lemma uses it. No unused node or module was claimed pruned, and the unit record's
   realized route is unchanged. Verdict: pass.
5. **DAG agreement.** The parent node's `proof`, `proof_deps`, and `proof_origin`
   follow the Lean proof; each new node has the required `lean` record, blueprint,
   source, searches, and split status. Verdict: pass.

I changed nothing during this second reading beyond recording this review. The dry
run and final delivery checks are run after this report update.
