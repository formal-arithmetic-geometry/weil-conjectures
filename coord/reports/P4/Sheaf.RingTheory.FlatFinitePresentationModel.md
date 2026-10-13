## What changed

Completed and checked the earlier sandbox proof of
`RingHom.exists_flat_finitePresentation_model` in
`Sheaf.RingTheory.FlatFinitePresentationModel`. Its public signature and original
public theorem docstring are unchanged. The three proved private helpers descend
flatness of a tensor model, construct the finite integer model in one universe,
and transport that model across ring equivalences. The final proof uses ULift
at the maximum universe, as the statement requires.

Added the proof-only import
`WeilConjectures.Mathlib.RingTheory.Finiteness.Descent`; it exports the existing
proved compact flat-locus descent, unit-ideal descent, finite-presentation
approximation, tensor pushout tools and global flatness criterion used here.
The original three public Mathlib imports are preserved. Updated the existing
node's proof, proof_deps and proof_origin to describe the actual argument.
No statements, definitions, visibility or other modules were changed.

The argument follows [Stacks Tag 02JO (1)](https://stacks.math.columbia.edu/tag/02JO)
with the top ring as its own module: compactness gives a flat model over the
image of the limit spectrum; descending the unit-ideal cover makes that model
flat everywhere. The unit statement and its steps are not bypassed.

## Proved and sorry left

Closed the one original hole:
`RingHom.exists_flat_finitePresentation_model`
(node `lem-weil-pbc-flat-finite-presentation-model`).

The private helpers `RingHom.exists_flat_tensor_model`,
`RingHom.exists_flat_model_same_universe`, and
`RingHom.exists_flat_model_of_equiv` are all proved. There are no sorries left
in the item, no holes added anywhere, and no split-off statements.
This is a proof, not a decomposition. A local `#print axioms` check of the public
theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The entire file compiles without warnings through lcompile.py.

Edge cases: no nontriviality or faithful-flatness hypothesis is introduced.
The compact-spectrum lemma accepts the empty spectrum. If the unit-ideal
argument assumes a proper ideal, maximal-ideal existence supplies the point
used in its contradiction; thus the zero-ring case is included. Both independent
input universes are handled by explicit lift equivalences and the left-inclusion
compatibility is proved pointwise after transporting back.

## No longer needed

No existing import was removed: the original file had only its three public
Mathlib imports. No planned Sheaf proof dependency is imported. The following
five planned modules are unnecessary for this proof:

- `Sheaf.RingTheory.ColimitEventuallyFlat`
- `Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule`
- `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
- `Sheaf.Algebra.LimitFinitePresentation`
- `Sheaf.RingTheory.OpenFlatLocus`

The following 15 nodes are removed from this node's direct proof dependencies:

- `lem-weil-pbc-colimit-eventually-flat`
- `lem-weil-pbc-filtered-colimit-algebras-elementwise`
- `lem-weil-pbc-filtered-colimit-algebras-underlying-module`
- `lem-weil-pbc-filtered-colimit-localization-at-prime`
- `lem-weil-pbc-filtered-colimit-rings-zero`
- `lem-weil-pbc-flat-local-ring-maps`
- `lem-weil-pbc-flat-map-local-criterion`
- `lem-weil-pbc-flat-module-base-change`
- `lem-weil-pbc-flat-over-localization`
- `lem-weil-pbc-limit-finite-presentation`
- `lem-weil-pbc-localization-flat`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-localization-tensor-over-base`
- `lem-weil-pbc-localization-tensor-product`
- `lem-weil-pbc-openness-of-flatness`

These are pruned from this item's route, not asserted to be globally unreachable.
The source-library tools have their own proved implementations, which may use
some of the Mathlib results represented by those nodes internally. The updated
proof text names the exact source-library declarations used instead of requiring
the stronger categorical colimit or arbitrary-module statements.

## Where the brief, the DAG or earlier work was wrong

The earlier worker left a complete compiling Lean proof, but no DAG update or
report. This attempt reviewed the code and dependency signatures, restored the
original public theorem docstring, and supplied those missing delivery records.
The old search verdict that source-library flat approximation only concerned
a specified fibre missed
`PrimeSpectrum.exists_fg_forall_flat_localization_tensor_of_isCompact`, which
applies to the whole spectrum. Combined with the existing unit-ideal descent
and global flatness criterion, this proves the model without new holes.

The local checkout does not contain the untracked Stacks algebra.tex cited by
the node. The source proof of Tag 02JO was read from the official Stacks page
linked above; the existing source-library implementations were read locally.
There is no mathematical error, statement dispute or forced adaptation.

## Second reading by P4

Independent second reader, 2026-10-13. Read the delivered module, its repository
version, both node records, the source-library declarations used below,
`dag/units/sk-thm-p1.json`, and the official Stacks proof of
[Tag 02JO (1)](https://stacks.math.columbia.edu/tag/02JO).

1. **Interface: pass.** The only delivered Lean module is
   `Sheaf.RingTheory.FlatFinitePresentationModel`. Its existing theorem signature
   and declaration docstring compare byte for byte equal to the repository.
   In particular both input universes, both finite-presentation conclusions,
   flatness of P → Q, and the equation identifying the left inclusion with f
   remain intact. There are no changed definitions, change records, or forced
   adaptations. The extra import is plain `import`, used only by the proof;
   the three public imports provide notions in the unchanged signature.

2. **Proof and axioms: pass.** Independently compiled the delivered file with
   lcompile.py: exit 0, no warnings (13.7 seconds). A scratch copy with
   `#print axioms` for all three private helpers and the public theorem compiled
   in 11.4 seconds. Every declaration reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered file
   contains no sorry or prohibited axiom/implementation escape. All model
   choices occur inside theorem proofs; no data definition chooses an arbitrary
   witness of an unproved existence assertion.

3. **Split statements and hypotheses: pass.** There are no split-off statements,
   new nodes, or new holes. The proved private helpers are genuine parts of the
   argument (globalizing flatness, constructing a same-universe model, and
   transporting it). Checked the precise hypotheses of
   `exists_fg_forall_flat_localization_tensor_of_isCompact`: finite presentation
   supplies finite type, the integer approximation supplies a Noetherian base,
   and the pushout equivalence supplies flatness of the full tensor algebra.
   The open-flat-locus theorem requires only finite type over the Noetherian T.
   The unit-ideal descent and `flat_tensorProduct_of_map_eq_top` require exactly
   the finite generation, inclusion, local flatness, and ideal equation provided.
   No faithful flatness is used. Empty spectra are accepted by compactness; in
   the zero-ring case the purported proper mapped ideal would give a maximal
   ideal and the same contradiction. ULift places both rings in max u v, and
   tensor congruence transports the left-inclusion equation pointwise.

4. **Shortest route, imports, and unit: pass.** Searched independently with
   LeanFinder for “descend a finitely presented flat algebra to a Noetherian
   subring generated over the integers”, and with rg through upstream ring
   theory and lean/Sheaf using approximation, pushout, compact-flatness, and
   model terminology. No exact existing theorem was found: smoothness and
   faithful-flatness model theorems have stronger hypotheses. The delivered
   proof uses the already proved compact flat-locus and finite unit-ideal
   descent implementations rather than restating them. Its one new proof-only
   import defines the final global-flatness lemma and exposes the other tools;
   all existing public imports are needed by the signature. The report names
   all 15 removed old proof dependencies, and honestly distinguishes planned
   modules from imports actually removed (none). Neither this node nor any
   removed dependency realizes a statement or step of sk-thm-p1; no unit-level
   route is bypassed and the unit record is unchanged.

5. **DAG: pass.** The sole node differs only in `proof`, `proof_deps`, and
   `proof_origin`. Its seven steps match the three helpers and the final lift:
   conjugation, integer presentation approximation, compact flat-locus descent,
   the maximal-ideal/basic-open contradiction, descent of the unit ideal,
   tensor pushout and finite presentation, and transport of compatibility.
   The named upstream tools were read at their definitions. The retained
   Noetherian, finite-presentation, composition, and spectrum nodes match the
   Mathlib facts used. `proof_deps` equals the union of the steps' `uses`.
   Statement, statement dependencies, unit, chapter, and Lean declaration
   record remain unchanged.

**Changes by the second reader:** appended this independent review; no Lean
proof or DAG repair was needed. The delivery closes one original hole and adds
zero holes. No split statement remains to close.
