## What changed

Withdrew the unused forwarding module
lean/Sheaf/AlgebraicGeometry/FieldFibreHomology.lean using deleted.txt. This removes
its three public import lines; deliver3.py writes the required empty module stub.
The existing upstream theorem
AlgebraicGeometry.Scheme.Modules.single_field_fibre_homology remains intact with
its complete proof and unchanged signature, attributes, public imports and helpers.
No upstream file is edited. Change record:
coord/changes/D4-field-fibre-homology-retire-forwarder.md.

Q5's already reviewed restoration made the actual replacement: the child node
new-field-fibre-homology is attached to the upstream implementation, and its sole
DAG parent lem-pc-finite-free-single-field-fibre is attached to
WeilConjectures.AlgebraicGeometry.FiniteFreeSingleFieldFibre. That module directly
imports the upstream implementation and applies single_field_fibre_homology.
This delivery finishes retirement of the now-unused compatibility path.

## Proved and sorry left

Closed 0 of 0 sorries; added 0 holes; split off 0 statements. There were no local
declarations or holes in the assigned module at the start of this session, and
none are introduced. The already complete upstream proof is reused, not counted
as newly proved. Its downstream homotopy-equivalence theorem also remains proved.
There are no remaining sorry declarations in the delivery.

The original forwarding module compiled through lcompile.py in 1.1 seconds.
A scratch import probe compiled in 1.3 seconds and checked both upstream
declarations: each depends only on propext, Classical.choice and Quot.sound.
The mandatory delivery dry run checks the final withdrawal packet.

## No longer needed

Pruned module Sheaf.AlgebraicGeometry.FieldFibreHomology, the forwarding path only.
Removed its explicit public imports of
Mathlib.Algebra.Homology.Embedding.CochainComplex,
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf, and
WeilConjectures.AlgebraicGeometry.FieldFibreHomology.
All three remain needed by the retained upstream proof or its consumer; none is
claimed globally pruned. No theorem, DAG node, or mathematical dependency is
removed. All six proof dependencies of new-field-fibre-homology stay unchanged.

A full scan of Lean imports under lean/Sheaf, lean/WeilConjectures and quarantine
finds no live or quarantined importer of the withdrawn module.
tools/downstream.py independently reports zero downstream modules and zero uses
through the Sheaf path. A full DAG scan
finds no Lean attachment to it and exactly one parent using the mathematical
node: lem-pc-finite-free-single-field-fibre. That parent's implemented proof
already uses the retained upstream theorem, so withdrawal does not rely merely
on the absence of current Lean importers. No parent edge update is required.
The unit route and sk-thm-picard-perfect.realized are preserved.

## Where the brief, the DAG or earlier work was wrong

The assignment describes a proof or quarantine repair, but Q5 already restored
this file as a re-export at landing 20261020T155435-L-3242650, with independent
review recorded in new-field-fibre-homology.reviewed_proof. The earlier quarantine
archive is absent and its rework row disappeared from the shared tree during
this session. The live module is present, and the retirement inventory still
lists it. This packet withdraws that present, unused forwarding path, preserving
the actual implementation and node attachment instead of manufacturing another
proof, reporting a no-op, or deleting any adopted source declaration.

Read the complete upstream proof and its consuming proof: bounded free terms and
locally free single cohomology are flat; truncation reduces to the single object;
bounded flat comparison computes both derived pullbacks termwise; single-complex
homology gives the vanishing and rank. No flatness hypothesis on the field map
is added. Rank zero, an index outside support, and empty schemes remain covered
by the same unchanged statements and proof.

Ran msearch.py Lean Finder, Loogle and grep searches. Loogle and grep locate
DerivedCategory.singleFunctorCompHomologyFunctorIso and grep also locates
exists_iso_singleFunctor_obj_of_isGE_of_isLE. The exact theorem is already in the
adopted source library; no new lemma or node is needed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
