## What changed

Proved `AlgebraicGeometry.leray_edge_cocycle_data` with its signature and both public
definitions unchanged. Its proof constructs the natural edge by conjugating a comparison
on section complexes with `InjectiveResolution.isoRightDerivedObj`. Naturality is proved
using Mathlib's resolution descent and the hom/inv naturality equations. A second descent,
extending the identity, proves the comparison equation for every injective resolution;
evaluation on a cycle then gives the exact two equations of `LerayEdgeCocycle`, including
the arbitrary complex `K` and its equality transport.

Added the proof-only import `Sheaf.AlgebraicGeometry.LerayComplexCocycleComparison`.
That new module states the cycle/kernel and homology/cokernel comparison on arbitrary
nonnegative complexes, before choosing an injective resolution or deriving a functor.
It is the complex-level construction in step 1 of the previous plan. The remaining
resolution transport and coefficient naturality are actual Lean proofs in the item,
not assumptions of the new theorem. Updated the item's node proof, proof dependencies,
and proof origin accordingly. No statement, definition, public import of the item,
or target signature changed. No change record is required.

## Proved and sorry left

Proved (by reduction): `AlgebraicGeometry.leray_edge_cocycle_data`, node
`lem-pc-leray-edge-cocycle-data`. The item's one original sorry is removed; no sorry
remains in that module.

One new named theorem remains sorry:
`AlgebraicGeometry.leray_complex_cocycle_comparison`, node
`lem-pc-leray-complex-cocycle-comparison`, module
`Sheaf.AlgebraicGeometry.LerayComplexCocycleComparison`. Its whole proof is `:= by sorry`.
Its docstring gives the kernel lift, the factorization that kills boundaries, and the
quotient-epimorphism argument for naturality. The new statement was checked mathematically
in degree zero, on the zero complex, for the identity morphism, and on the empty scheme:
the incoming differential is zero in degree zero, the zero complex and the empty
scheme give zero objects, and for the identity morphism the comparison is the usual
kernel-inclusion and homology-quotient construction. No finiteness, properness, injectivity,
or acyclicity assumption is required for this complex-level comparison.

Thus this is a reduction, not a claim that the entire dependency closure is sorry-free.
Mathlib resolution-comparison and descent lemmas are used without new assumptions.

## No longer needed

Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic`.
- `Sheaf.CategoryTheory.GrothendieckEdgeCocycle`.
- `Sheaf.AlgebraicGeometry.TensorPullback`.
- `Sheaf.CategoryTheory.GrothendieckComposablePair`.
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.
- `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`.

Removed from this node's proof dependencies:

- `thm-sp-grothendieck` (`Sheaf.CategoryTheory.GrothendieckSpectralSequence`).
- `lem-weil-pbc-module-pushforward-injective-acyclic`
  (`Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic`).
- `lem-sp-grothendieck-edge-maps`
  (`WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`).
- `lem-pc-grothendieck-edge-cocycle` (`Sheaf.CategoryTheory.GrothendieckEdgeCocycle`).
- `prop-pur-kinjective-resolutions-exist`
  (`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`) as a separate proof step.
- `lem-weil-pbc-ring-modules-grothendieck-abelian` as a spectral-sequence hypothesis.
- `def-sp-composite-acyclicity` (`Sheaf.CategoryTheory.GrothendieckComposablePair`).
- `def-pc-module-pullback` (`Sheaf.AlgebraicGeometry.TensorPullback`) as a proof dependency.
- `pqf-def-cohomology` as an application of its theorem.
- `def-weil-sheaf-of-modules-category` as a separate proof step.

The last three definition/theorem nodes are still statement dependencies or supply notions
through the unchanged public imports. In particular the public import of
`Sheaf.Paper.PQFCohomology` stays: it supplies the module-cohomology and direct-image
signatures. The Grothendieck instance and enough-injective infrastructure reached by that
public import also stay. This report lists what this proof no longer calls; it does not
claim that these modules have no other target consumers. The maintainer computes actual
reachability pruning. No node or module is deleted.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The spectral-sequence construction and
pushforward-injective acyclicity in the old proof plan are unnecessary for existence of
the edge and its cocycle description. They concern the stronger spectral-sequence or
collapse assertions; the elementary comparison on complexes exists without them.
The existing declaration docstring records the old spectral-sequence route; the revised
DAG and the actual Lean proof record the route delivered here.

The original source reference overstates what Tag 01F4 writes explicitly: its proof
states degeneration and proposes a direct proof as an exercise, rather than spelling out
the claimed cycle construction. Read the Stacks source `lemma-apply-Leray` and the sections
construction preceding the Leray section. The new proof in words is marked as K1's
universal-property expansion of that direct-proof exercise. It does not pretend the
details are quoted from 01F4 or that 01F2 states sectionwise kernels.

Searches ran through `msearch.py`: LeanFinder on derived-composite morphisms, Loogle on
`homologyComparison`, and grep on `homologyComparison|cyclesComparison`; the matches are
related derived transformations or comparisons of left and right homology, without the
specialized section-complex equations. LeanSearch for the natural section-complex
comparison returned HTTP 500 and is recorded as unavailable, not as a negative result.
Repository/blueprint searches for homology/global-sections comparisons found no existing
node stating this complex-level comparison without extra injectivity hypotheses.
`cartanEilenberg_leftExact_cohomology` assumes injective cycles and boundaries and concludes
an isomorphism, so cannot be applied to an arbitrary direct-image complex.

The unit `sk-thm-picard-rr` has empty realized statement/step bindings, and this construction
changes only the route below the existing degenerate-Leray node. Its statement and unit
route, including the eventual vanishing/isomorphism step, are untouched. The ancestor
script returns no blueprint ancestor for the item's module-valued `created.item`; the
new node follows the recorded ancestor of `lem-pc-leray-degenerate-sections` instead.

## New nodes

`lem-pc-leray-complex-cocycle-comparison`, in
`dag/nodes/sec-picard-framework/lem-pc-leray-complex-cocycle-comparison.json`, is stated in
`lean/Sheaf/AlgebraicGeometry/LerayComplexCocycleComparison.lean`. It covers only the
comparison before deriving: cycles lift by the kernel universal property, their projected
homology map kills boundaries and descends through a cokernel, and the descended map is
natural in cochain maps. It contains no injective resolution or derived-functor comparison.
The item proves how to turn this comparison into a natural transformation on coefficients
and verifies its formula for every chosen resolution. The node includes all three search
kinds, a self-contained statement, source, proof steps, and the exact Lean signature.

## Second reading by K1

1. Compared both delivered modules with the repository. The new comparison module is
   absent upstream. In LerayEdgeCocycleData, the signatures of LerayEdge,
   LerayEdgeCocycle, and leray_edge_cocycle_data are byte-for-byte unchanged; both
   definition bodies are unchanged. The existing public import and docstring are
   unchanged. Only proof-only imports, theorem-local elaboration options, and the proof
   changed. No statement change or change record is needed. Verdict: pass.

2. Compiled both modules in import order through lcompile.py: comparison 4.0 seconds,
   item 41.9 seconds, no errors or warnings. Scanned for forbidden declarations and
   compiler escapes: none. The only delivered sorry is the named public theorem
   leray_complex_cocycle_comparison, whose whole proof is `by sorry`; no hollow
   definition was introduced. A scratch import with explicit #print axioms for both
   definitions and both theorems returned only propext, Classical.choice, Quot.sound,
   and sorryAx. The definitions already depend on open upstream infrastructure;
   the item's reduction also depends on the new open comparison theorem. Verdict:
   valid reduction, not a sorry-free dependency closure.

3. Read the complete comparison signature, docstring, and new node, and the saved
   cohomology.tex at lemma-apply-Leray (Tag 01F4), including its direct-proof exercise.
   The source states degeneration, not the detailed comparison; the docstring and node
   explicitly identify these details as K1's expansion. The new assertion is true:
   sections of f_*C over Y identify with sections of C over X after map_top,
   sectionwise kernels lift each cycle uniquely, and the quotient map kills incoming
   boundaries. Cokernel descent gives tau, and epimorphic homology projection proves
   naturality. In q=0 there is no incoming differential; zero complexes and empty
   schemes give zero groups; with f the identity this is the usual section-to-sheaf
   homology comparison, which need not be an isomorphism. No properness, affine-base,
   injectivity, or acyclicity hypothesis is used. It is a proper intermediate statement:
   it neither mentions injective resolutions nor provides their derived comparisons.
   Repeated searches with different wording through msearch LeanFinder (left exact
   functor and mapped homology), grep (homology/comparison in either order), and local
   searches of Sheaf, upstream cohomology, and Mathlib ShortComplex APIs found no exact
   existing result. The attempted two-string Loogle query was invalid and gives no
   negative evidence. Read mapHomologyIso and its naturality API: it requires preservation
   of homology, stronger than left exactness of sections. GrothendieckEdgeCocycle adds
   acyclicity and spectral-sequence structure and is not this arbitrary-complex result.
   Closing this specialized construction is not a few-minute API application. Verdict:
   retain the one sourced, documented split-off theorem.

4. Read the item proof top down. Its first block conjugates tau with the canonical
   resolution isomorphisms; naturality uses desc a and the actual Mathlib
   isoRightDerivedObj_hom_naturality/inv_naturality statements (RightDerived.lean,
   lines 126 and 141), whose augmentation equation is proved by simp. The second block
   uses desc of the identity from an arbitrary resolution, cancels inv followed by hom,
   applies tau's naturality, and evaluates the resulting equality on homologyπ(s).
   Substitution by hK accounts for both displayed equality transports. Thus the
   resolution-independence part was not moved into the new sorry. No shorter existing
   applicable declaration was found. The one private comparison import supplies the
   proof; PQFCohomology supplies the public signatures. Compared old and new proof_deps:
   all ten removed nodes are listed above. Corrected the removed-import list to include
   all seven modules in the actual diff. Read sk-thm-picard-rr.json: its realized bindings
   are empty, and the retained downstream LerayEdgeVanishingIso statement still requires
   the separate vanishing/isomorphism argument. No unit statement or realized step was
   bypassed. Verdict: pass after the report correction.

5. Compared the delivered node fields with the original node: only proof, proof_deps,
   and proof_origin changed, following exactly the three Lean proof blocks. Its
   definition/resolution and derived-well-defined dependencies are Mathlib leaves;
   the latter supplies the resolution comparison isomorphisms. The new node has the
   exact Lean signature, source with expansion attribution, complete kernel/cokernel
   argument, search records, created/blueprint/chapter/unit/lean fields, and its
   proof_deps is the union of its steps' uses. Its statement requires only schemes,
   a scheme morphism, a natural degree, an arbitrary nonnegative complex, and a cycle,
   exactly as the Lean does. Verdict: pass.

Changed in this reading: completed the five missing removed-import entries in
"No longer needed" and added this review. No Lean proof, signature, definition, or node
was changed. Scratch axiom-check files were removed before delivery.
