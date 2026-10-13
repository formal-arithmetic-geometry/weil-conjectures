## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_generic_free_neighbourhood` with its
signature and visibility unchanged. The proof follows the generic-basis and
coherent-map-extension route of the node. It constructs the empty-relation finite
presentation of the free source, extends the basis isomorphism, and cancels the
bijective additive restriction-stalk comparisons.

Added two proved public helper modules:
`Sheaf.AlgebraicGeometry.FiniteTypeModuleStalkFinite` proves finite generation of
all stalks of finite type structure-module sheaves using the existing proved
`generating_sections_iff_stalk_span`. Its semilinear restriction-stalk transport
uses the actual ring and module stalk comparisons, with the scalar compatibility
proved on intersected germ representatives.
`Sheaf.AlgebraicGeometry.FiniteFreeModuleStalkEquiv` exposes the already proved
private `localStalkEquiv` coordinate construction of
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank` through `import all`.
This is reuse of its proved construction, not an inference from finrank alone;
no source module is changed. The returned existence is used only to choose an
isomorphism inside a theorem proof, never to define arbitrary data.

Added proof-only imports of those two helpers,
`Mathlib.LinearAlgebra.Dimension.Free`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
Updated the item node's proof, proof dependencies and proof origin.
No definitions or existing interfaces changed; no forced adaptations.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.exists_generic_free_neighbourhood`
(node `lem-weil-pbc-coherent-integral-generic-free-neighbourhood`).

Also proved, with no added holes:
`AlgebraicGeometry.Scheme.Modules.finite_moduleStalk_of_isFiniteType`
(node `lem-weil-pbc-finite-type-module-stalk-finite`) and
`AlgebraicGeometry.Scheme.Modules.exists_finite_free_moduleStalk_linearEquiv`
(node `lem-weil-pbc-finite-free-module-stalk-equiv`).

No `sorry` remains in any delivered module. This is a proof, not a decomposition.
Imported dependency proofs retain their own project status; this delivery does
not claim the entire target closure is free of `sorry`.

Edge cases: no nonzero-stalk assumption is used. For a zero generic stalk the
finite basis has rank zero. The free-stalk equivalence allows empty index sets,
and the finite-generation proof allows an empty generating family. The finite
stalk lemma is vacuous on an empty scheme. All three modules compile locally
without warnings using the prescribed compiler.

## No longer needed

No original imports were removed: both original proof imports are used.
No original mathematical step or unit route is bypassed. The old direct proof
edge `def-weil-pbc-module-stalk` is replaced by the two explicit proved helper
edges; the actual ringed-space stalk definition remains imported publicly as
before. This does not claim its module leaves the full target closure.

Removed experimental redundant imports from the new helper modules:
`Mathlib.AlgebraicGeometry.Restrict`, `Mathlib.Topology.Sheaves.Module`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`.
Their required APIs are already available from the remaining imports.
No additional node or module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The plan did not name separate declarations for
finite generation of the generic stalk or the finite-free coordinate
identification. Both steps are now explicit proved helpers, with their own
nodes. The free coordinate construction already existed as a private helper,
so rewriting it or leaving a new hole was unnecessary.

The coordinate helper's source node is in `sk-thm-picard-duality` (the Picard
framework); it is used as a proved generic algebraic tool. The item's unit
`sk-thm-p1` statement and realized steps are unchanged.

## New nodes

`lem-weil-pbc-finite-type-module-stalk-finite`: finite generation of the actual
stalk of a finite type structure-module sheaf over its actual stalk ring.
Source: Stacks 01B4/01B5. Proved via finite local generators, the existing
stalk-span theorem, and semilinear comparison of restriction stalks.

`lem-weil-pbc-finite-free-module-stalk-equiv`: the coordinate linear equivalence
for the stalk of a finite free structure-module sheaf. Source: Stacks 01C6.
Proved by preserving the free sheaf on the top open and reusing the complete
proved local coordinate construction. Both new statements are strictly parts
of the original argument and have no `sorry`.

## Second reading by Q1

1. Interface comparison: PASS. Diffed the item against the repository version.
   The existing theorem signature, visibility, docstring and public imports are
   byte-for-byte unchanged; only its proof and proof-only imports differ. The
   other two modules and their declarations are new. No definitions, target
   statements, or unrelated modules are changed; no change record is required.
2. Proof and trust check: PASS. Compiled all three modules in import order with
   lcompile.py, without errors or warnings. Scanned the delivered sources for
   sorry and forbidden declarations or attributes: none. Scratch-copy
   #print axioms checks show only propext, Classical.choice and Quot.sound for
   both helpers. The item additionally uses sorryAx from an existing open
   dependency (the stalk-Hom route includes FinitePresentationStalkKernel);
   its imported proof closure is therefore not yet a completed target proof.
   The reused localStalkEquiv is a genuine coordinate construction with proved
   inverse identities. No arbitrary data is defined from unproved existence.
3. New statements: PASS. There are no split-off holes. Both proved helper
   statements are true, needed, and strictly smaller than the item. Reviewed
   finite generators and the semilinear restriction-stalk comparison on common
   germ representatives, including its actual scalar-ring isomorphism. Reviewed
   localStalkEquiv and its coordinate/sum identities in the source module.
   Empty index types and zero stalks work, and an empty scheme has no point.
   Repeated leanfinder, loogle and grep searches with different terminology,
   and searched the project for stalk finiteness and linear equivalences.
   The affine finiteness helper in FiniteTypeModuleSupportPullback needs
   quasi-coherence and a longer localization route; StalkFiniteFree remains
   sorry and requires local freeness. Neither replaces these general helpers.
   Existing private coordinate constructions are reused rather than copied.
4. Route and pruning: PASS. The argument starts at the item, uses Mathlib's
   finite basis, the proved generator-span/coordinate constructions, and then
   the planned coherence criterion and coherent stalk-map extension. No
   shorter applicable public theorem was found. New public imports supply
   the helper signatures; implementation imports are proof-only. The original
   proof imports are both used. The old direct edge
   def-weil-pbc-module-stalk is explicitly accounted for under No longer needed;
   its public module remains required by the unchanged statement. No module
   is claimed pruned. Read sk-thm-p1.json: its statement and realized steps
   are preserved, with the coordinate helper used only as a generic tool.
5. DAG agreement: PASS. Compared the item node's proof, proof_deps and
   proof_origin with the basis, empty-relation presentation, extension, and
   cancellation in Lean. Both helper nodes have matching verbatim statements,
   source, complete proof steps, dependency union, search records, creation,
   blueprint, chapter/unit and Lean attachment fields. No unsupported new
   reduction or restatement of the item is introduced.

Second-reading changes: added this review and explicit axiom/closure limitation
to the report; no Lean or DAG repair was needed. Holes closed: one original
item theorem; holes added: zero; two additional helper theorems proved.
