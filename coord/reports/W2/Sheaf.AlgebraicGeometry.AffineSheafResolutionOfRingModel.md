## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_affine_sheaf_resolution_of_ring_model`
with its signature and public imports unchanged. Its module and an updated copy of its existing DAG node are delivered.
Added proof imports of `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`,
`Mathlib.LinearAlgebra.FreeModule.Finite.Basic`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.Defs` (for the proved scalar-action comparison).
The private helpers prove preservation of kernels by tilde, compatibility of the affine
pushforward scalar action, preservation of quasi-coherence along the affine isomorphism,
and the natural affine counit. None is left unproved.

The complex Q is constructed termwise by tilde followed by canonical affine restriction.
The proof establishes its upper bound, chooses and reindexes finite bases to produce its
free-sheaf isomorphisms, and composes the mapped f with the termwise invertible counit.
Exactness uses quasi-coherent kernels and full faithfulness rather than stalks.
The existing DAG node's proof, proof_deps and proof_origin now record this route.
The unit has no realized nodes at this level; its finite-free replacement route is retained.

Searches: LeanFinder found quasi-coherence interfaces, not the target theorem; Loogle
returned `AlgebraicGeometry.tildeFinsupp`; grep found the existing kernel-preservation
argument in `AffineDerivedTildeHomologyComparison` and the scalar-action calculation
in `Modules.AffineHom`. The delivery uses those existing mathematical arguments,
with the general affine counit and the cochain assembly completed locally.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_affine_sheaf_resolution_of_ring_model`
(node `lem-pc-affine-sheaf-resolution-from-ring-model`).
One original hole closed; zero holes added; no sorry remains in the delivery.
This is a proof, not a decomposition. All four private helpers are proved.
The proof covers the zero ring, empty affine scheme, zero terms and unbounded-below P;
no nontriviality or lower bound was added.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.ModuleStalkExact`. The three original
public imports remain needed by unchanged statements. The following planned proof dependencies are removed from this
node, and their proof-only modules are not imported here:

- `lem-weil-pbc-spec-tilde-stalk-localization` (Mathlib's tilde.toStalk proof route).
- `lem-weil-pbc-localization-module-exact` (Mathlib's LocalizedModule.map_exact proof route).
- `lem-weil-pbc-module-stalk-exact`, module `Sheaf.Algebra.Homology.ModuleStalkExact`.

Mathlib.AlgebraicGeometry.Modules.Tilde remains imported for the actual functor and
adjunction; pruning its stalk lemma as a proof dependency does not remove that module.
These are dependencies pruned from this item; other targets may still need their modules.
The closed existing node `lem-weil-pbc-quasi-coherent-module-kernel` replaces the
stalk-exactness route. No other planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The item is true and its signature required no correction. The DAG's stalk/localization
proof plan was longer than necessary: the proved quasi-coherent-kernel theorem already
lets full faithfulness and the invertible counit establish exactness of tilde.
Importing the general affine-pushforward result from DirectImage.AffineMorphism would
close an import cycle, so preservation of quasi-coherence along this scheme isomorphism
is proved directly from restriction and pushforward composition comparisons instead.
No changed definition, forced adaptation, new node, or change record is needed.

The interrupted earlier attempt already contained the complete proof. This continuation
compiled it successfully, checked the dependency signatures and unit realization, restored
the original public theorem docstring, and corrected the pruning report. The final delivery
dry run checks the axioms of all declarations as well as the project preflight.

## Second reading by W2

1. **Statements and accidental changes.** Compared the delivered module and node with the
repository versions. The public theorem signature is byte-for-byte unchanged; only its proof,
proof-only imports, and the corresponding DAG proof metadata changed. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no `sorry`, `axiom`,
`unsafe`, `opaque`, `extern`, `implemented_by`, or `sorryAx`. A scratch `#print axioms` for
the target reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Split statements and searches.** No statement was split off and no new node was added.
The recorded LeanFinder, Loogle, and repository searches found no existing theorem duplicating
the target. Verdict: pass.
4. **Pruning and route.** The proof uses the quasi-coherent-kernel route and removes the
stalk/localization dependency imports listed above; the affine tilde/global-sections route and
the unit's finite-free replacement route remain intact. Verdict: pass.
5. **DAG agreement.** The node's proof steps, `proof_deps`, and `proof_origin` match the
delivered proof, and the module's imports match the declarations actually used. Verdict: pass.

Changed during second reading: added this review record only. No Lean declarations, statements,
definitions, or DAG statements were changed.
