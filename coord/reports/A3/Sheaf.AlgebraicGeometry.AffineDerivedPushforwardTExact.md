## What changed

Completed `AlgebraicGeometry.schemeDerivedDirectImage_tExact_and_conservative_of_affine`
in `Sheaf.AlgebraicGeometry.AffineDerivedPushforwardTExact` without changing its signature.
Added two proved private helpers: `qc_single` puts a quasi-coherent module in degree zero,
and `affine_reflects_module_zero` detects vanishing of such a module from its affine
ordinary direct image. The main proof transfers quasi-coherence along the affine
cohomology comparison, proves pointwise equivalence of cohomology vanishing, applies
Mathlib's `DerivedCategory.isLE_iff` and `isGE_iff`, and invokes existing affine
conservativity for the final clause.

Added proof-only imports
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` (detection of
zero objects by all cohomology) and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` (the empty free
sheaf supplies quasi-coherence of zero sheaves). Updated the existing node's second
proof step to describe the actual zero-endomorphism argument. Its proof dependencies
and the unit route are unchanged. Both existing affine input modules remain imported.

Searches: LeanFinder for affine direct image detecting zero quasi-coherent modules
returned unrelated affine-transition and sheaf-equivalence results; Loogle for
`DerivedCategory.IsLE` found `isLE_iff` and `isGE_iff`; grep confirmed those lemmas in
Mathlib and found no shorter theorem for this scheme derived direct image in either
library root. The source library's proved
`DerivedCategory.isZero_of_forall_isZero_homology` supplies the needed object-level
cohomology detection. No new intermediate statement was required.

## Proved and sorry left

Proved the module's sole original sorry:
`AlgebraicGeometry.schemeDerivedDirectImage_tExact_and_conservative_of_affine`
(blueprint: `lem-sc-affine-derived-pushforward-t-exact`). Both private helpers are
proved. There are no sorries left in the delivered module and none added elsewhere.
The proof uses the existing stated theorems
`AlgebraicGeometry.schemeHigherDirectImage_of_affine` and
`AlgebraicGeometry.schemeDerivedDirectImage_isIso_of_affine`; their existing sorries
remain in their own modules, outside this delivery. Local single-file compilation
passes without errors or warnings.

## No longer needed

None. All original imports and all three recorded proof dependencies are used.
No node or module of the planned route is bypassed. A temporary explicit import of
`Mathlib.CategoryTheory.ObjectProperty.ContainsZero` was removed after confirming
that the retained imports already supply it; it was never an import of the original
module.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The DAG's converse vanishing argument is
valid; the implementation uses the zero endomorphism of the degree-zero object
instead of its zero morphism to a separate zero object. This avoids needing a separate
quasi-coherence proof for that second object and proves the same step. The unit record
has no realized node here, and the proof retains the original unit route and inputs.


## Second reading by A3

1. Compared the sole delivered module with the repository by diff and checked the
   existing theorem signature byte for byte: unchanged. No definition or existing
   declaration was altered; the additions are two proved private helpers and two
   plain, proof-only imports. No change record is needed. Verdict: pass.
2. Compiled the module locally without errors or warnings. A scratch copy with
   `#print axioms` checks both helpers and the public theorem. The only axioms are
   `propext`, `Classical.choice`, `Quot.sound`, and (for the reflection helper and
   main theorem) `sorryAx` from the existing imported affine input statements.
   No sorry or prohibited declaration occurs in this delivery. Verdict: pass.
3. No statement was split off and no new sorry or node was added. Read both
   private helpers: the empty free sheaf is zero, the single object's cohomology
   is the given module in degree zero and zero elsewhere, and conservativity
   applied to its zero endomorphism detects its vanishing. These arguments cover
   the zero module, empty schemes, and all negative and positive degrees without
   extra assumptions. Verdict: pass.
4. Rechecked the shortest-route search using Loogle `DerivedCategory.singleFunctor`
   and grep for quasi-coherence of single objects and reflection of zero direct
   images in both library roots. Found the already-used single-functor cohomology
   isomorphism and proved homology detection, but no shorter matching affine
   derived theorem. Every retained import is needed for the signature or proof.
   All old proof dependencies are used, so `No longer needed: None` is complete.
   Read `dag/units/sk-thm-picard-duality.json`: this node is not a realized unit
   step; the existing unit route and affine inputs are retained. Verdict: pass.
5. Compared the old and delivered node: only the second proof step and
   `proof_origin` differ. The step accurately describes the implemented
   zero-endomorphism argument; `proof_deps` remains the union of the inputs
   actually used. Lean statement and node statement are unchanged. Verdict: pass.

Second reading changed only this report by adding the independent review. No
proof repair was necessary.
