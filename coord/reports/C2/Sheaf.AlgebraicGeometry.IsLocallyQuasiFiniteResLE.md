## What changed

Closed the proof of `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_resLE` in
`Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteResLE` without changing its signature.
Added the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`.
The existing finite-type and fibre-isolation lemmas give Mathlib's pointwise
`QuasiFiniteAt` predicate. Its composition criteria transfer this predicate across
the restriction square; the fibre criterion then supplies isolation for the
restricted morphism. Choose affine opens in the restricted schemes and apply the
existing affine-pair theorem to construct the exact Stacks witness.

Updated the declaration docstring and the node's proof, proof_deps, and proof_origin
to this argument. The unit `sk-thm-p1` has neither this node nor these dependencies
among its realized statements or steps; its route is preserved. Source read:
Stacks https://stacks.math.columbia.edu/tag/01TD and
https://stacks.math.columbia.edu/tag/01TH, notably (1) implies (2) and (2) implies (4).

## Proved and sorry left

Closed one of one local holes:
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_resLE`
(node `lem-weil-pbc-lqf-restriction-to-opens`). No sorry remains in the delivered
module. No holes added and no new statements split off.

The proof uses the existing declarations
`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`
(node `lem-weil-pbc-lqf-locally-finite-type`),
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber`
(node `lem-weil-pbc-quasi-finite-at-point-isolated`), and
`AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber`
(node `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs`).
Those declarations still contain sorry in the repository read for this task;
this delivery closes the upper hole from the stated dependencies, rather than
claiming an axiom-free proof of all the supporting theory.

## No longer needed

Removed the redundant direct proof import `Sheaf.RingTheory.QuasiFiniteAtPrime`;
its definition remains available through the required public statement import
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`. Thus its module and node are still
needed transitively, and no whole module is claimed to leave the target closure.

Removed the direct proof-dependency edge to `def-weil-affine-spectrum`
(`Mathlib.AlgebraicGeometry.Scheme`); there is no explicit construction or
identification with Spec in the new proof. That definition remains needed
transitively by affine-open and affine-pair theory. All other original proof
nodes remain used. No further node or module can be pruned from the closure
by this delivery.

The original plan's comparison of the same affine pair, section rings, induced
ring maps, and corresponding primes across both open inclusions is unnecessary.
Instead the affine-pair theorem is applied directly to the restricted morphism.

## Where the brief, the DAG or earlier work was wrong

No statement error found. Mathlib's global restriction instance alone indeed
uses a different predicate, as the DAG warns. However, its proved pointwise
fibre criterion and composition lemmas provide the missing transport directly
once local finite type is available, so the lengthy ring-identification glue
in the original plan is unnecessary.

The cited local literature files and blueprint unit source file are absent on
this machine. The unit record was read, and the Stacks tags were read online.
LeanFinder, Loogle, and grep searches through the launcher found the precise
Mathlib criteria used above. Initial local compilation passed without warnings;
the final delivery dry run performs compilation and the axiom/preflight checks.

## Second reading by C2

1. Compared the sole delivered Lean module against the repository with `diff`.
   The existing theorem signature is byte-for-byte unchanged; there are no new
   declarations or changed definitions. The only interface import remains the
   original public import of `QuasiFiniteMorphism`. Verdict: pass.
2. Compiled the module locally through `lcompile.py`, without errors or warnings.
   Inspected the complete proof: no `sorry`, forbidden declaration, hollow
   definition, or arbitrary data chosen from an unproved existence theorem occurs.
   A scratch copy with `#print axioms` reports exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter comes from the existing supporting
   theorems listed above, not a new hole. Verdict: pass as a reduction using the
   existing open dependencies, not an axiom-free completion of their theory.
3. No statements were split off and no new nodes or holes were added. Read the
   three supporting theorem signatures and the definitions of
   `IsQuasiFiniteAtPoint` and `IsLocallyQuasiFinite`; the affine-pair output supplies
   exactly the existential fields required. Empty source opens are vacuous;
   the chosen affine neighbourhoods contain the specified point, and the second
   lies in the required inverse image. No extra finite-type hypothesis was added.
   Verdict: pass.
4. Read Mathlib's pointwise fibre criterion and both composition criteria, and
   searched independently for composition/restriction criteria with `msearch.py`
   grep and for equivalent Stacks predicates throughout `lean/`. Mathlib itself
   uses the same restriction-square rewrite in `ZariskisMainTheorem`. No existing
   theorem directly returning this Stacks predicate gives a shorter route.
   Every remaining proof import supplies an explicitly used theorem; the added
   Mathlib import is correctly private to the proof. The removed direct ring
   import and the sole removed old dependency `def-weil-affine-spectrum` are
   reported above, with their continuing transitive use made explicit. Read
   `sk-thm-p1.json`'s `realized` fields: no realized statement or step is bypassed.
   Verdict: pass.
5. Compared node JSON fields: only `proof`, `proof_deps`, and `proof_origin`
   change. The new dependency list is exactly the union of the steps' `uses`.
   Each step describes the Lean argument, including local finite type for the
   restricted morphism, transport across both open immersions, and the final
   affine witness. The node's statement and Lean record remain unchanged.
   Verdict: pass.

Second reading changed only this report by adding the independent review and
explicit axiom-check result. No correction to the proof or node was needed.
