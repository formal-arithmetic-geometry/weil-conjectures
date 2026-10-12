## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_affineBaseChange_tensorComparisons`
without changing its signature or visibility. Added a proof-only import of
`WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde` for the explicit
pushforward/global-sections scalar comparison and tensor/extension-of-scalars equivalence.
Two proved private helpers construct the tensor-pullback comparison for tilde modules
and then for quasi-coherent affine modules. The first witness uses the global-sections
isomorphism for pushforward of tilde; the second restricts the pullback comparison's
scalars. Tensor balancing proves its formula for arbitrary z.

The existing DAG route is retained: pullback-tilde comparison and the Mathlib
pushforward-tilde leaf. No new nodes or declaration-interface changes; the second reading narrows an unused
public import, with its change record below. The helpers require no
extra hypotheses on the rings; zero rings and the zero module are included.
Compilation passed locally; the dry run supplies the declaration/axiom probe.

Search: LeanFinder queried global sections of pullback of tilde and tensor scalar
extension (generic pullback adjunctions only); Loogle found `tilde.isoTop` and its
hom formula. Source grep found `pushforwardSpecMapCompΓIso`,
`ModuleCat.tensorEquivExtendScalars`, and `fromTildeΓ_app_toOpen` in the adopted
source library. The existing `exists_tensorPullback_tilde_iso` provides the unit
formula for the project's tensor pullback rather than Mathlib's pullback.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_affineBaseChange_tensorComparisons`
(node `lem-weil-pbc-affine-base-change-tensor-comparisons`).
Both private helpers `tensorTildeSections` and `tensorQCSections` are proved.
No `sorry` remains in this module; no holes are added or split off.
This is a proof from existing library declarations, not a decomposition.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`, which neither
the statement nor the proof uses, replacing it with the signature dependency
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`. Both original proof-dependency
nodes remain used. No whole module is asserted to leave the targets' closure;
`AffinePushforwardBaseChange` independently imports the removed module. Exploratory split files were discarded and are
not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The paired comparison can be proved directly from
the existing unit-compatible tensor-pullback tilde isomorphism and Mathlib's
affine tilde/global-sections isomorphisms. Explicit ring parameters on
`fromTildeΓ` avoid expensive elaboration of nested spectrum identifications.

## Second reading by D2

1. Compared the only delivered Lean module with the repository using `diff`.
   The existing theorem signature, visibility, and docstring are byte-for-byte
   unchanged. The additions are two private proved helper theorems, a proof-only
   source-library import, a local heartbeat option, and the proof. No definitions
   or target statements change. Verdict: pass.
2. Independently compiled the module with `lcompile.py`: no errors or warnings.
   There is no `sorry`, axiom, unsafe declaration, opaque declaration, external
   implementation, or data definition in the delivered module. The construction
   uses explicit linear equivalences; existential witnesses are eliminated only
   in proofs, never chosen as data from an unproved mere existence statement.
   The delivery dry run checks axioms of every delivered declaration. Verdict:
   pass, the dry-run axiom probe passed (no forbidden axioms).
3. No statements are split off and no holes are added. Both helpers are proved
   strict parts of the comparison argument. Checked the zero-ring/zero-module
   cases: no nontriviality, injectivity of a ring map, or flatness assumption is
   used. The balancing identity holds for arbitrary z and m. Verdict: pass.
4. Read TensorPullbackTilde and the adopted PullbackTilde source. Existing
   pullbackSpecΓEquiv handles Mathlib pullback, whereas this statement specifies
   tensorPullback and its chosen unit; it is therefore not a direct replacement.
   The proof uses the existing unit-compatible tensor-pullback comparison rather
   than reproving it. Grep of affine base-change and quasi-coherent modules found
   no shorter exact comparison. Both old proof dependencies are used; sk-thm-p1
   realized nodes and its unit route are untouched. Removed the unused
   open-restriction import, as recorded above. Verdict: pass after repair.
5. Read the item node, both old dependency nodes, the global-sections comparison
   node, and dag/units/sk-thm-p1.json. Expanded the item's proof steps and added
   lem-weil-pbc-pushforward-spec-global-sections to proof_deps to record the
   explicitly used source-library equivalence. No new nodes are needed; the public import removal is documented in
   coord/changes/AffineBaseChangeTensorComparisons-imports.md. Verdict: pass after repair.

Second-reading changes: removed the unused open-restriction import in favor of
its actual adjunction dependency; expanded DAG proof metadata to match the
construction; removed one duplicate blank line. No mathematical proof repair
was necessary. Closed one original hole, added zero holes, split off zero.

Public import change record: `coord/changes/AffineBaseChangeTensorComparisons-imports.md`.
