## What changed
The unchanged theorem `Algebra.artinian_transcendental_polynomial_localization`
is reduced to structural properties and a flat local evaluation map. Each
intermediate theorem now has its own module, full proof in words, and node.
The parent node records the conjunction proof actually written in Lean.

## Proved and sorry left
Closed the one hole in `Algebra.artinian_transcendental_polynomial_localization`
by decomposition, not by an independent proof. Added two holes:
- `Algebra.localization_artinian_transcendental_properties`
  (`lem-weil-pbc-artinian-transcendental-localization-core-structural`).
- `Algebra.localization_transcendental_evaluation`
  (`lem-weil-pbc-artinian-transcendental-localization-core-evaluation`).
There are no holes in the item module. Net holes closed minus added: -1.

## No longer needed
Removed the direct proof import
`Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian` from the item module.
Its node remains needed in the evaluation component's planned proof; it is
not globally pruned. No original proof-dependency node is globally pruned:
the original steps are distributed between the two new nodes.
Discarded the earlier sandbox-only module
`Sheaf.RingTheory.ArtinianTranscendentalLocalizationCore` in favor of one
statement per new module.

## Where the brief, the DAG or earlier work was wrong
The earlier sandbox put two statements in one new module, left incomplete
node statements and dependency lists, and wrote a second-reading section
without an independent second reader. These have been corrected.
The earlier package-source discovery failure is now repaired in the launcher tools.
The repair dry run reached preflight and identified missing LeanSearch records in
both new nodes. A real LeanSearch request returned Internal Server Error; both
nodes now record that search as unavailable, alongside the previously executed
LeanFinder, Loogle and grep searches. No tool was edited or bypassed.
All three sandbox modules compile through lcompile.py. The item retains exactly
its original signature. The two components are strictly separate parts of its
conclusion, with the parent combining their proofs by conjunction introduction.
For the structural component, the field case gives F(t), and for evaluation,
S may contain nilpotents: only residue evaluation must be injective, not evaluation
into S. Both arguments retain the unit route and use the concrete localization.

## New nodes
`lem-weil-pbc-artinian-transcendental-localization-core-structural` records
prime identification and structural properties in
`Sheaf.RingTheory.ArtinianTranscendentalLocalizationProperties`.
`lem-weil-pbc-artinian-transcendental-localization-core-evaluation` records
localization evaluation and fibre flatness in
`Sheaf.RingTheory.ArtinianTranscendentalLocalizationEvaluation`.
No existing signature, definition, or visibility changes; no change record.
The evaluation component no longer imports EssentiallySmooth and imports the
fibre criterion privately, retaining that original planned dependency.

## Second reading by N3
1. Compared the delivered item with its repository version by diff. Its existing
   theorem signature and docstring are byte for byte unchanged; only the proof
   and private proof imports change. No definitions, targets, or existing
   visibility were changed. The other two modules are new. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py, then compiled
   scratch copies with #print axioms for each of the three declarations. All
   compile cleanly and use only propext, Classical.choice, Quot.sound, and
   sorryAx. The latter remains because both named component theorems are open.
   No forbidden declarations or hollow definitions occur. Verdict: decomposition,
   not an axiom-free proof; one upper hole closed and two lower holes added.
3. Read both component statements and their complete proof docstrings. They are
   distinct strict parts of the conclusion. Checked D a field (T is D(t)),
   arbitrary residue-field extensions, nilpotents in D and S, and the local
   nontriviality assumptions that exclude zero rings. Transcendence applies to
   residue evaluation, not evaluation into S. For the evaluation component,
   all three rings are Noetherian, both maps local, and M=S is finite nonzero
   over S; its closed fibre is a vector space over F(t), so Tag 00MP applies.
   Confirmed the source arguments against Stacks Tags
   [07FI](https://stacks.math.columbia.edu/tag/07FI) and
   [00MP](https://stacks.math.columbia.edu/tag/00MP).
   Independent LeanFinder search used "flat local homomorphism artinian ring
   polynomial residue transcendental fraction field"; Loogle searched
   "Transcendental, Polynomial.eval₂RingHom" (no hits); grep searched nilpotent
   Artinian and transcendental localization variants, and rg searched the
   project and upstream library. No duplicate component theorem found.
   Mathlib supplies the individual Noetherian/nilpotent and localization facts,
   but not the complete prime identification or flat evaluation component.
   Neither remaining hole is a few-minute application of an existing result.
   Verdict: true, sourced, strictly smaller components with matching nodes.
4. Read the original proof-dependency nodes and their Mathlib matches and the
   unchanged unit sk-thm-p1 realized record. The conjunction reduction preserves
   its route. The parent now directly needs only the two component nodes;
   all original proof dependencies occur in those components' plans. Thus none
   is globally pruned. Removed the unused public EssentiallySmooth import from
   the evaluation module and added its private fibre-criterion import so the
   original flatness dependency stays reachable. Verdict: pass after repair.
5. Checked parent proof/proof_deps/proof_origin against conjunction introduction;
   checked both new nodes' source, statements, declaration signatures, proof
   steps and their dependency unions. The Lean contains no data chosen from an
   unproved existence statement: T is the concrete lifted localization, and the
   existential evaluation map is only a theorem conclusion. Removed the unused
   essentially-smooth stmt_dep from the evaluation node. Verdict: pass.
Changes by this second reader: evaluation-module imports and its unused
statement dependency; independent compilation, axiom checks, searches, and this
report. The mathematical decomposition was retained unchanged.
