## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.generic_torsion_cohomology_colimit`
with a complete Lean proof from existing continuity declarations. The private,
fully proved `lowerStar_isColimit` handles qcqs morphisms: restrict to the affine
etale basis, evaluate on qcqs base changes, apply module-section continuity via
Ab ≃ Mod(ℤ), and reflect colimits back through the coefficient and site equivalences.
The main proof applies the existing large-index `sheafH_isColimit_large_filtered`
to this direct-image cocone. All original theorem binders and its conclusion are unchanged.

Added proof imports for affine etale density, the integer-module equivalence,
sheaf adjunctions, `EtaleSectionsFilteredColimit`, and
`Curve.EtaleSheafHLargeFilteredColimit`. Updated the existing node's proof,
proof_deps and proof_origin to match this route. No new statement modules or nodes.
Change record: `coord/changes/generic-torsion-cohomology-imports.md` documents the
redundant public import removal and its unchanged effect on all downstream users.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.generic_torsion_cohomology_colimit`
(node `lem-sc-generic-torsion-finite-stalk-colimit-cohomology`): 1 of 1 original
sorries removed. The private helper `lowerStar_isColimit` is also fully proved.
No sorry remains in the delivered Lean file; none is added elsewhere.
This is a stage-3 proof from existing dependencies, including the already-stated
large-index cohomology continuity theorem; it does not claim those dependencies
are now axiom-free.

Local compilation is clean. The import-pruning compatibility check passes.
The delivery dry run provides the local probe, server compilation and preflight.

## No longer needed

Removed direct import `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
No original proof-dependency nodes were recorded, so none are removed.
For this cohomology passage, no Galois-module equivalence, finite stable-subgroup
construction, torsion hypothesis or finite-stalk hypothesis is used. Those remain
needed for the separate finite-stalk presentation in the parent module, and are
not claimed to be globally pruned. Neither the general higher-direct-image
continuity module nor the directed-poset continuity module is imported: the
existing section theorem and arbitrary-filtered large-index Ext theorem suffice.

## Where the brief, the DAG or earlier work was wrong

The node's old proof was a single unnamed non-elementary step with no dependency
records. Its complete statement concerns every filtered cocone, without finite-stalk
or torsion assumptions. The proof above works for precisely that statement.
The module's original informal description mentions finite products of invariants;
that description alone does not give the needed arbitrary-diagram Lean comparison.
The affine-basis section argument supplies it without new Galois theory.

The source library's general higher-direct-image filtered-colimit theorem is
indexed by `Type` (universe zero), so it does not directly handle this `Type (u+1)`
index. `EtaleSectionsFilteredColimit` and the large-index Ext theorem do.

The existing abelian sections helper in `EtaleDirectedCohomologyColimit` is private,
so it cannot be imported as a public lemma. Its coefficient-transport argument is
used inside the proved direct-image helper rather than declaring another copy.

Removing `EtaleTorsion` also removed instances needed to elaborate the original
`Sheaf.functorH` signature within the compiler's instance-search limit; that import
is retained. The unit's route is preserved: this proves the parent's generic
cohomology-colimit passage, without bypassing its finite-stalk or vanishing steps.

## Second reading by N1

1. Compared the complete module against the repository with `diff -u`: the existing
   theorem signature and docstring are byte-for-byte unchanged, and there are no
   changed definitions or target statements. The only public import removal has the
   supplied change record and a retained transitive public path. Verdict: pass.
2. Compiled the delivered module locally without errors or warnings. Inspected every
   proof: no sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition
   is introduced. Compiled a scratch copy with `#print axioms` for both the public
   theorem and the private helper; each uses only propext, Classical.choice, Quot.sound,
   and sorryAx from existing open dependencies. Verdict: pass as a conditional stage-3
   reduction, not an axiom-free closure of its dependencies.
3. There are no new split-off statements or nodes. The private helper is fully proved
   and makes the strictly intermediate direct-image assertion, not a restatement of
   the cohomology result. Checked the qcqs base-change hypotheses and coefficient
   universes; empty objects, zero sheaves, and degree zero require no additional
   assumptions. Verdict: pass; no open statement to close.
4. Read the proof top down and checked the existing section and large-index cohomology
   declarations. A fresh LeanFinder search for qcqs etale pushforward filtered-colimit
   continuity found no applicable shortcut; source searches found only finite-colimit
   direct-image results under different hypotheses. The basis/equivalence argument
   handles the required arbitrary filtered index in Type (u+1). Added imports are
   proof-only; retained public imports support the unchanged signature and its instances.
   The old proof_deps is empty, so the pruning list is complete. The unit's realized
   arrays are empty in the repository; no realized step or finite-stalk reduction is
   bypassed or removed by this delivery. Verdict: pass.
5. Checked the node's four proof steps and dependency union against the actual Lean:
   qcqs permanence is a verified Mathlib leaf; the other two dependencies name exactly
   the section-continuity and large-index cohomology theorems applied. proof_origin
   describes this route; lean.statement agrees with the unchanged signature. No new
   nodes require additional fields. Verdict: pass.

Second reading changed only this review report and added an independent search record;
no Lean proof repair or DAG repair was needed. The cited blueprint text is not present
in this machine's read-only literature checkout; the unit record, parent context, Lean
statements and actual proof were checked directly.
