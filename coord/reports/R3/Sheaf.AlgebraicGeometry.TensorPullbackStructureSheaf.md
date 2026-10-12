## What changed

Proved `AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit_isIso` in
`Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`, with its signature and the
structure-sheaf morphism definition unchanged. Added the proof-only import
`WeilConjectures.Mathlib.Topology.Category.TopCat.Opens` for finality of inverse image
on opens. Updated the node proof to the global-sections argument.

The adjunction sends the defined morphism to the structure-sheaf map. For any module M,
precomposition with this morphism corresponds to pushforward of global sections, via
the adjunction and `unitHomEquiv`. Mathlib proves that map bijective for a final site
functor, giving the isomorphism by the coyoneda criterion. The unit characterization
is `Adjunction.homEquiv_unit`.

Searched with msearch leanfinder, loogle and grep, and read Mathlib PullbackFree and the
source library Modules/Sheaf and TopCat/Opens. This adapts Mathlib's existing argument
without identifying the chosen adjunction with the abstract pullback adjunction.
The unit record sk-thm-p1 does not realize this node as a unit step; its route is preserved.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit_isIso`
(node `lem-weil-pbc-module-pullback-structure-sheaf`).
No sorry remains in the delivered module; no holes added or split off.
Local compilation passed without warnings.

## No longer needed

None of the original imports was removed: both support public definitions or signatures.
No existing proof-dependency nodes or modules are pruned (the original proof_deps was empty).
The explicit tensor multiplication and balanced-relation argument in the docstring
requires no separate intermediate declarations with this proof.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof and proof_deps despite the chosen tensor adjunction being
needed. Its proof_deps now records `lem-pc-module-pullback-adjunction`.
The finality instance mentioned as unlocated in the earlier node audit is in
`WeilConjectures.Mathlib.Topology.Category.TopCat.Opens`, rather than Mathlib itself.
No statement or definition was changed; no new nodes.

## Second reading by R3

1. Compared the delivered module with the repository version. The existing declarations and theorem signature are unchanged byte for byte; only the proof, proof-local options, and the required finality import differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. A scratch copy with `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for both declarations. No `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition is present. Verdict: pass.
3. Checked the proof against the imported adjunction and Mathlib's final-site global-sections bijection. The Hom-equivalence calculation and `isIso_iff_coyoneda_map_bijective` argument prove exactly the stated conjunction. No split-off statements were added, and the node statement is true and unchanged. Verdict: pass.
4. Reviewed the route and imports. The tensor pullback adjunction and `PullbackFree` declarations are used; `PullbackFree` must remain public because `unitToPushforwardObjUnit` occurs in the public theorem signature. The unit route is preserved and no proof dependency or module can be pruned. Verdict: pass.
5. Checked the DAG node against the Lean proof. Its proof steps, dependency on `lem-pc-module-pullback-adjunction`, origin, and declaration match the implementation; the unit `sk-thm-p1` route remains recorded. Verdict: pass.

Changed the theorem docstring to describe the actual global-sections proof and added this review. Retained the necessary public import after testing that making it private breaks elaboration of the public signature. No Lean proof or signature repair was needed.
