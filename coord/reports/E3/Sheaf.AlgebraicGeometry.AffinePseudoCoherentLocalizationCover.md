## What changed

Replaced the sorry in
`AlgebraicGeometry.affine_pseudoCoherent_localization_cover` with a complete Lean
finite-cover assembly. The proof unfolds scheme pseudo-coherence at each prime,
refines the supplied neighbourhood using the principal-open basis, applies a
single-open model comparison, proves that the good elements generate the unit
ideal, extracts a finite subset using `Ideal.span_eq_top_iff_finite`, and
enumerates that subset by `Fin r`. The range equality and every local assertion
are proved in Lean. The existing signature and public imports are unchanged.

Added the proof-only import
`Sheaf.AlgebraicGeometry.AffinePseudoCoherentPrincipalModel` and its module.
The new theorem isolates steps 2–4 of the original plan: transport of one
specified bounded-above finite-free sheaf model to one specified localization.
It has neither the global pseudo-coherence hypothesis nor the finite-cover
conclusion of the assigned theorem. Updated both DAG records to describe this
route. No definitions, instances, file options, or other existing modules change.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.affine_pseudoCoherent_localization_cover`
(node `lem-pc-affine-pseudo-coherent-localization-cover`). There are no sorries
left in the assigned module.

Added one hole in the new module:
`AlgebraicGeometry.affine_pseudoCoherent_principal_model`
(node `lem-pc-affine-pseudo-coherent-principal-model`). Its proof is exactly
`:= by sorry`, with its source and full natural-language proof in the docstring.
This is a decomposition: one upper hole closed, one strictly local hole added,
net zero holes closed. The principal-open refinement, unit-ideal extraction,
finite enumeration, and combination are proved, rather than split off.

The new statement was checked on an empty principal open (the localization is
the zero ring and the zero complex is a representative), f = 1 (the hypothesis
then supplies a model on the entire spectrum), rank zero, unboundedness below,
and the zero ring. It does not require nonempty opens, positive ranks, boundedness
below, or a shared module/sheaf morphism universe. The supplied sheaf-derived
localizations on all opens support the restrictions used by the proof plan.

Both modules compile locally through lcompile.py. No lake command was run.

## No longer needed

No existing import was removed and no module is claimed pruned. The following
old proof dependencies are no longer direct dependencies of the cover theorem:
`lem-pc-affine-qcoh-derived-equivalence`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-weil-pbc-spec-module-tilde-sections`.
All three move to the proof plan of
`lem-pc-affine-pseudo-coherent-principal-model`; they remain needed there,
so this is a relocation of dependencies, not pruning.
The cover extraction uses Mathlib's finite-subset-of-span theorem; no new
quasi-compactness or enumeration node is needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed interface was found. The declarations named by
original steps 2–4 provide ingredients, but their signatures do not directly
supply the comparison between a model on a localized open site and a localized
module complex. This comparison is the new local item; its definition-level
restriction, finite-free complex lifting, and derived reflection remain open.

The original proof described compactness extraction; the Lean proof instead
uses the equivalent unit-ideal criterion and finite support of membership in
an ideal span. The unit record has no realized nodes for this auxiliary step,
and its fixed statement and route are preserved.

The cited Stacks source was read at https://stacks.math.columbia.edu/tag/08E7
and https://stacks.math.columbia.edu/tag/08E5. The local-model argument expands
the affine comparison step, rather than using the whole affine criterion
(which would introduce an import cycle through the assigned module).

## New nodes

`lem-pc-affine-pseudo-coherent-principal-model`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-pseudo-coherent-principal-model.json`,
is the single-open comparison for a supplied finite-free model. Its module is
`Sheaf.AlgebraicGeometry.AffinePseudoCoherentPrincipalModel`; it retains the
localization, tilde adjunction, and affine derived equivalence of the original
plan. Three successful kinds of Mathlib search (LeanFinder, Loogle, grep) and
an unavailable LeanSearch attempt are recorded from searches.jsonl. Searches
of the current library and blueprint found no theorem with this interface.
No change record or forced adaptation is needed.


## Second reading by E3

1. **Existing interfaces: pass.** Read the complete diff against the repository.
   The sole existing declaration's signature, including all universes and
   hypotheses, is byte-for-byte identical. Public imports are unchanged; the
   added comparison import is plain `import`. There are no changed definitions,
   instances, other existing modules, or unreported interface changes.
2. **Proof and axioms: pass as a decomposition.** Independently compiled both
   modules in import order with `lcompile.py --all`: no errors or warnings.
   Scratch copies with `#print axioms` for both declarations report only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The cover module
   has no sorry; the new named local comparison is the only delivered sorry.
   Inspected both files for forbidden declarations/options and hollow data:
   none. No data definition chooses an arbitrary witness of an open theorem.
3. **Split-off statement: pass.** It assumes one specified finite-free model on
   one specified neighbourhood and concludes the module property on one
   contained principal open. It neither assumes global pseudo-coherence nor
   extracts a cover, so it is strictly one part of the original argument.
   Checked nilpotent f/empty D(f), the zero ring, f = 1, zero ranks, and bounds
   of either sign; none requires a missing hypothesis. Exact restriction,
   the localized tilde comparison, lifting differentials by full faithfulness,
   and derived affine reflection justify the docstring's argument. The
   localized-site/sheaves-on-the-open equivalence must be used in implementing
   that argument. Reviewed the matching node and source citations, including
   [Stacks 08E7](https://stacks.math.columbia.edu/tag/08E7) and
   [Stacks 06Z0](https://stacks.math.columbia.edu/tag/06Z0).
   Independent searches used LeanFinder with “exact faithful associated sheaf
   functor reflects quasi isomorphisms complex localization finite free”,
   Loogle with `AlgebraicGeometry.tilde.functor`, and grep with
   `IsPseudoCoherent|mapDerivedCategory|overFunctor`, plus searches of both
   library roots. They found the ordinary full/faithful tilde functor and
   restriction comparisons, but no theorem with the new interface. The affine
   criterion imports the cover theorem, so using it here would be circular.
   Closing the local comparison requires these transport constructions and
   is not a few-minute application of an existing theorem.
4. **Top-down route and pruning: pass.** Read the finite-cover proof line by
   line: the basis refinement feeds the local comparison, the spectrum covering
   criterion gives the unit ideal, finite span support extracts the finite
   family, and the equivalence with Fin proves its range and local assertions.
   This is a real reduction, not a renamed application of the original hole.
   The unit's realized statement and step arrays are empty and unchanged;
   neither its route nor its fixed text is bypassed. All public imports supply
   types or definitions in the signatures; the sole proof-only import supplies
   the comparison. Clarified the three moved old dependencies under
   `## No longer needed`; no modules are pruned.
5. **DAG agreement: pass.** Existing-node changes are confined to proof,
   proof_deps, and proof_origin. Their steps match the Lean assembly, and the
   covering-criterion node is a Mathlib leaf matching the lemma actually used.
   The new node has its complete statement, verbatim Lean signature, source,
   proof plan/dependencies, search records, creation record, blueprint origin,
   chapter, unit, and Lean record. Its plan retains the old local comparison
   ingredients and additionally names exact open restriction.

Second reading changed only the report: made the moved direct dependencies
explicit and recorded this independent review. No Lean or node repair was
needed. One upper hole is closed and one local hole added: net zero, a
finite-cover decomposition, not a complete proof of pseudo-coherence.
