## What changed

Replaced the proof of
`AlgebraicGeometry.canonicalModuleBaseChange_isIso_on_affine_open_of_affine_cases`
without changing its signature or visibility. The proof constructs the actual affine
model: U = f⁻¹(V), fA = (f restricted to V) followed by V.isoSpec.hom,
gA = W.isoSpec.inv followed by g.resLE and V.isoSpec.hom, and
H = schemeOpenRestriction(X,U)(G). Quasi-compactness and separatedness are supplied
by Mathlib. Quasi-coherence is transferred from ordinary restriction using
overFunctorEquiv. Tensor-pullback additivity follows from the existing adjunction.

Added two modules, with one public theorem each:
`Sheaf.AlgebraicGeometry.FlatOverAffineOpenRestriction` proves relative flatness
of this explicitly restricted module over fA;
`Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeAffineChartComparison` states
the remaining compatibility square for the canonical arrow. The latter has no
affine-invertibility hypothesis, no relative-flatness hypothesis, no
quasi-coherence hypothesis, and no quasi-compactness/separatedness hypotheses.
Its conclusion identifies arrows and their endpoints; it does not assert IsIso.

The main proof obtains the comparison c0 and its source/target isomorphisms,
applies the supplied haffine to fA, gA, H and c0, maps the resulting isomorphism
along derived direct image of W.isoSpec.inv, and cancels the target comparison.
The rewritten original arrow is a composite of three isomorphisms. This is a
real reduction to map compatibility, not an application of an invertibility
statement under another name. No definition or statement of an existing module
was changed, and no data-valued definition was added or selected from a hole.
Existential elimination occurs only inside the theorem proof.

Updated the original DAG node to match this argument. The two new nodes inherit
its chapter, unit and blueprint ancestor. The unit route and haffine computation
remain intact. Compiled all three modules in import order with lcompile.py.

## Proved and sorry left

Closed the original module's one direct hole, in
`AlgebraicGeometry.canonicalModuleBaseChange_isIso_on_affine_open_of_affine_cases`
(node `lem-pc-canonical-module-base-change-affine-locality`). This is a decomposition:
its proof still depends on the new compatibility theorem, and it is not claimed
as an unconditional sorry-free mathematical proof.

Added and proved
`AlgebraicGeometry.isFlatOver_affineOpenRestriction`
(node `lem-pc-flat-over-affine-open-restriction`). Its three private helpers are
also proved. They prove flatness under ordinary restriction, postcomposition
by an isomorphism of the base, and a module isomorphism, respectively. No direct
sorry remains in that module.

The only sorry added, and the only direct sorry in this delivery, is
`AlgebraicGeometry.exists_canonicalModuleBaseChange_affineChart_comparison`
(node `lem-pc-canonical-module-base-change-affine-chart-comparison`). Its whole
proof is `by sorry`; its docstring gives the construction and the arrow argument.
The hole is the compatibility step, independent of the supplied affine
calculation. Direct holes closed: 1. Direct holes added: 1. Net direct change: 0.
Existing holes in imported modules are unchanged.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`
- `Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`
- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap` (redundant with the public
  import through `DerivedModuleBaseChangeMap`)

Their associated nodes are no longer direct proof dependencies of the original
node: `lem-pc-derived-pullback-open-restriction-universes`,
`lem-pc-restrict-derived-direct-image-open`,
`lem-pc-derived-direct-image-composition`,
`lem-weil-pbc-module-base-change-map-open-restriction`, and
`lem-pc-ringed-spaces-derived-pullback-composition`.
The old nodes `def-pc-derived-base-change-map` and
`def-pc-derived-module-base-change-map` also leave the original node's direct
`proof_deps`; they remain statement dependencies and are publicly imported.
The five lemma nodes remain in the plan for the new arrow-comparison node; they are not claimed
as globally unnecessary. The second reader added private imports of the four restriction/composition
modules not already reached by a public import to the new comparison module,
so that its remaining hole retains its stated proof dependencies.
DerivedPullbackComposition is also still reached via
the public definitions of the canonical base-change map. No unit or affine
calculation node is pruned. No Cech calculation, local-to-global isomorphism
detection, or flatness over O_X is introduced into this locality proof.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly describes the mathematical reduction, but the
recorded restriction lemmas give functor isomorphisms rather than a theorem
identifying the whole canonical derived module arrow after spectrum-chart
transport. Its second step also requires a separate flatness transport for the
explicit chart model; no existing theorem states that precise conclusion.
The delivery makes the missing arrow step explicit and proves the flatness step.

Checked edge cases: the chart comparison has no nonemptiness hypothesis;
empty affine opens are spectra of their zero section rings, and the maps into
the empty open only have empty inverse images. Relative-flatness restriction
uses every affine pair and therefore applies to empty opens and the zero module.
The proof does not confuse relative flatness over S with intrinsic flatness
of G over X. It does not deduce invertibility from isomorphic objects alone:
the commuting arrow square is an explicit hypothesis obtained from the new lemma.

Read the blueprint's local-affine paragraph and Stacks Tag 01U4's final
assertion, Tag 08IB's local reduction, and Tag 08HY's canonical mate construction.
The new arrow lemma transports the counit witnessing hc rather than choosing
an independent counit; this is needed because the comparison predicate allows
any witnessing left-derived structure. LeanSearch was unavailable; LeanFinder,
Loogle and source searches were completed and recorded in the new nodes.

## New nodes

`lem-pc-flat-over-affine-open-restriction`, implemented by
`Sheaf.AlgebraicGeometry.FlatOverAffineOpenRestriction`, is the proved
relative-flatness transport. It restricts to actual open subschemes, changes
base by the spectrum isomorphism using flatness of bijective ring maps and
Module.Flat.trans, and transports the module via overFunctorEquiv.

`lem-pc-canonical-module-base-change-affine-chart-comparison`, implemented by
`Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeAffineChartComparison`, states
the remaining canonical-arrow comparison. Its source/target isomorphisms live
in D(W), using derived direct image of W.isoSpec.inv to transport the affine
arrow into the same category. Neither haffine nor any invertibility claim is
repeated in this lemma. The model scheme, two affine morphisms and restricted
module are explicit expressions, not data extracted into definitions from
an unproved existence theorem.

There are no interface changes to existing modules, no forced adaptations,
and no change records.

## Second reading by D3

Independent second reader; 2026-10-13.

1. Compared every delivered source with the repository using diff. Only the original
   locality module already exists; its theorem signature is byte-for-byte identical,
   its public imports and visibility are unchanged, and its only declaration change
   replaces its proof. The existing node changes only proof, proof_deps and
   proof_origin. The other two modules and nodes are new. No definition changes,
   change records, forced adaptations, or data chosen into a new definition occur.
   Verdict: pass.
2. All three modules compiled in import order with lcompile.py, without errors or
   warnings. The only direct sorry is the whole proof of the reported named chart
   comparison. Flatness transport and all its private helpers have real proofs;
   the original theorem really applies haffine and conjugates along the commuting
   arrow square. Inspected every file for prohibited declarations and hollow
   definitions. Explicit axiom probes are recorded below. Verdict: pass, as a
   decomposition depending on the named remaining hole and upstream holes.
3. Read both new statements, their docstrings, nodes, and the comparison predicate.
   The remaining theorem states an arrow compatibility square and never assumes
   haffine or concludes invertibility. It is strictly the geometric compatibility
   part of the argument; flatness transport is proved separately. The counit in hc
   must be transported rather than replaced by an independently chosen counit.
   Empty W, empty V, zero G, identity charts, and the case W mapping into a proper
   subopen all satisfy the construction: cartesianness identifies the relevant
   full inverse image; exact restriction and chart equivalences identify both
   endpoints. Flatness uses arbitrary affine pairs, not intrinsic O_X-flatness.
   Read the cited primary sources at https://stacks.math.columbia.edu/tag/08IB,
   https://stacks.math.columbia.edu/tag/08HY,
   https://stacks.math.columbia.edu/tag/08FE and
   https://stacks.math.columbia.edu/tag/01U4 (literature bodies are not copied to
   this machine). Independent LeanFinder search for adjunction-mate compatibility,
   Loogle search for IsLeftDerivedFunctor, and grep for flatness restriction and
   derived open base change found component lemmas, no duplicate of either new
   theorem. Also searched lean/Sheaf and lean/WeilConjectures and read the existing
   restriction/composition modules. The compatibility proof requires the full
   derived mate calculation; it cannot be closed by a short application of one
   of those functor isomorphism statements. Verdict: pass; one hole remains.
4. The proof first uses Mathlib for morphism properties, restriction of
   quasi-coherence, and flatness transport, then the named geometric compatibility
   step, and finally haffine. No shorter existing arrow-level result was found.
   Public imports supply signature vocabulary; added imports are private.
   Compared the old proof_deps against the new union and completed No longer
   needed for both old definition nodes and the redundant direct base-change
   import. All five old lemma dependencies remain on the compatibility node's
   route; none is claimed globally pruned. Read the unit record
   dag/units/sk-thm-picard-f-representable.json: its realized lists are empty and
   neither this item nor the old dependencies realize a unit step. The enclosing
   affine-calculation/locality route is retained. Verdict: pass.
5. Checked proof steps and their uses against the Lean and verified each
   proof_deps is exactly their union. Both new nodes contain the required source,
   search history, creation, blueprint, chapter, unit and Lean fields; their
   statements match their declarations. The old node keeps its statement and
   all other non-proof fields unchanged. Verdict: pass.

Changes made by the second reader: added private imports of
DerivedPullbackOpenRestrictionUniverses, DerivedDirectImageOpenRestriction,
DerivedDirectImageCompositionUnbounded and ModuleBaseChangeMapOpenRestriction
to the remaining comparison module, retaining its stated proof-dependency route;
DerivedPullbackComposition is already public through DerivedModuleBaseChangeMap.
Completed the omitted SchemeDerivedBaseChangeMap import and the two definition
nodes in No longer needed. No proof, theorem statement, or definition was rewritten.
No additional holes were closed or added: this remains one original hole closed,
one compatibility hole added, net zero direct holes; no globally pruned modules.

Explicit scratch-copy #print axioms results: isFlatOver_affineOpenRestriction
and flatOver_morphismRestrict, flatOver_postcomp_iso, flatOver_of_iso use only
propext, Classical.choice and Quot.sound. The original locality theorem and the
remaining chart-comparison theorem use these three axioms plus sorryAx, as
expected from the named hole and upstream open statements. No other axiom appears.
Scratch Lean copies were removed before preflight/delivery.
