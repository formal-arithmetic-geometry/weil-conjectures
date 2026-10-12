## What changed

Proved `AlgebraicGeometry.coherentFormalModules_closedUnderBinaryProducts` with its
existing signature and docstring unchanged. Constructed a termwise biproduct system,
its projection cone and its limit proof as private implementation helpers. Bundled
the existing fixed-power quotient maps as a private functor and proved it additive.
Mathlib's preservation of biproducts supplies the quotient comparison isomorphism.
The existing isomorphism-invariance theorem transports the three conditions to the
vertex of the given limiting cone.

Added plain proof imports `Sheaf.AlgebraicGeometry.CoherentFormalModulesIsoInvariant`
and `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`. Public imports are unchanged.
There is no new public declaration, global instance, statement change or change record.

## Proved and sorry left

Holes closed against the repository baseline: one,
`AlgebraicGeometry.coherentFormalModules_closedUnderBinaryProducts`.
Holes added: zero. No `sorry` remains in any delivered declaration or definition.
This is a proof from existing library declarations, not a decomposition.

The first worker's proposed hole
`AlgebraicGeometry.coherentFormalModules_isCoherent_binaryProduct` and its unlanded
node `lem-weil-pbc-coherent-formal-binary-product-canonical` were removed.

The axiom check for the main theorem reports `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. The latter is inherited from the existing
`AlgebraicGeometry.Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule`;
this delivery does not close that dependency's remaining proof obligations. All
private helpers, quotient-map identity/composition laws, ideal-power factorization,
and `coherentFormalModules_of_iso` report only the three allowed foundational axioms.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections` and the old
proof dependency `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`.
The proof uses naturality of ideal products and additive quotient functors instead
of affine sections. This identifies a removed dependency; it does not claim that
no other target imports the removed module.

Kept `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` for termwise coherence.
Removed the first worker's unlanded canonical-limit node, which was not a baseline
dependency. No unit realization is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The first worker's claim that the canonical-limit intermediate was necessary was
incorrect. Isomorphism invariance makes that intermediate equivalent to the whole
binary-product closure statement, so it was a relabeling, not a strict reduction.
Its doc comment also attached the original declaration's documentation to the new
hole. Both defects are eliminated by removing that declaration.

The old affine-section route was unnecessary below the unit level: fixed-power
reduction is additive by cancellation of the cokernel projection, and Mathlib's
`preservesFiniteBiproductsOfAdditive`,
`preservesBinaryBiproducts_of_preservesBinaryProducts`, and `Functor.mapBiprod`
give the quotient comparison directly.

## New nodes

None. The existing item node's `proof`, `proof_deps`, and `proof_origin` now describe
the actual five-step proof. Its statement and all non-proof fields are preserved.

## Second reading by S1

1. Compared the delivered module with the repository file using `diff` and the
   declaration parser. The existing theorem's signature is byte for byte identical,
   its docstring and visibility are unchanged, and both public imports are unchanged.
   The interface comparison is empty. All added constructions are private; no other
   module is adapted. Verdict: no accidental change visible to importers.

2. Compiled the final module with the prescribed local compiler. Examined every
   construction: `sumSystem` explicitly has biproduct objects and diagonal maps;
   `sumLift` explicitly lifts both component maps; the limiting-cone uniqueness
   proof uses componentwise projection equations. The quotient functor uses the
   existing cokernel maps, not an arbitrary existence witness. No forbidden command
   or local `sorry` remains. Printed axioms for the main theorem and every helper;
   the only extra axiom is the reported inherited `sorryAx` in coherent closure.
   Verdict: a kernel-checked proof relative to the existing library obligations.

3. Rejected and removed the canonical-limit split because it moved the complete
   claim into another hole. No split-off statement remains. Independently searched
   the library and upstream checkout for coherent formal products, Mathlib source
   for additive preservation, and ran LeanFinder on additive functors preserving
   binary biproducts plus Loogle on `"mapBiprod"`. The searches led to the actual
   generic Mathlib comparison used in the repaired proof. Verdict: no duplicate
   mathematical statement or new open node is delivered.

4. Read [Stacks Section 0EHN](https://stacks.math.columbia.edu/tag/0EHN) and
   [Lemma 087X](https://stacks.math.columbia.edu/tag/087X). The Noetherian scheme and
   quasi-coherent ideal hypotheses are unchanged. The definition's indexing
   `op n` gives the positive level `n + 1`; the proof uses exponent `n + 1` and the
   transition from `op (n + 1)` to `op n`. Checked each of coherence, annihilation,
   and quotient-transition compatibility separately. Projection naturality proves
   annihilation; cokernel factorization and the two given transition equalities
   prove compatibility. Zero factors, zero/unit ideals, and the empty scheme
   require no additional assumption or exceptional branch. Both projections of
   the constructed cone give its genuine universal property. Removed the unused
   affine-section import and listed its node above. Read `dag/units/sk-thm-p1.json`:
   this support node is below its realized steps; none is bypassed or changed.
   Verdict: the shorter route respects the unit and the edge cases.

5. Compared the node with the completed Lean proof. Its steps are exactly:
   construct the termwise limit; use coherent biproduct closure; use equal-power
   factorization for annihilation; use quotient additivity for transitions; use
   isomorphism invariance for the arbitrary limiting vertex. `proof_deps` is the
   union of those steps' cited existing nodes, and `proof_origin` records the
   repaired route. No new node or statement-change record is necessary.
   Verdict: DAG, Lean, and report agree.

Second-reading changes: replaced the relabeled hole by the complete biproduct
argument, removed its declaration and new node, pruned the affine-section import
and dependency, updated the item node, and corrected the proof/holes accounting.
