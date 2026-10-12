## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_restrict_eq_of_pullback_eq` in
`Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality`, with its entire signature unchanged.
Added proof-only imports of `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`,
`Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.

Five private, fully proved helpers supply stalk-map detection after pullback, determination
of unit maps by their value at global 1, finite-generator neighbourhood equality, transport
along a natural isomorphism, and detection by restriction along a scheme isomorphism.
The main proof combines them and preserves the original direct restriction functor.
Updated the existing node's proof, proof dependencies, and proof origin to match this route.
No definitions, existing signatures, visibility, or other modules were changed.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.Scheme.Modules.exists_restrict_eq_of_pullback_eq`
(node `lem-pc-finite-free-stalk-map-eq-shrink`). No `sorry` remains in the delivered module;
no new hole or node was added. This is a complete proof from the existing library lemmas,
not a decomposition into newly holed statements. Imported lemmas retain their existing
transitive proof dependencies; this delivery does not claim those dependencies are closed.

The module compiles cleanly through the mandated local compiler. The proof handles arbitrary
N without finiteness assumptions; `Finite I` suffices in its finite-generator helper.
When r=0, the intersection over the empty index type is top and the coproduct extensionality
has no cases. All three new imports have passed the import-direction check.

## No longer needed

No original import was removed. Each added proof import is used. No module is claimed to be
pruned from the target import closure.

Removed the original proof edges to `def-weil-pbc-free-module` and
`def-weil-pbc-module-stalk`: their recorded declarations are the ordinary-module Free class
and the general presheaf-module stalk functor. The proof instead directly uses Mathlib's
free sheaf coproduct API and the recorded ringed-space module stalk functor
`def-pc-module-stalk-functor`. Both original nodes remain statement dependencies, so this
edge correction is not a claim that their nodes leave the whole target DAG.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically correct but does not explicitly list the fact that the
canonical local-scheme map has an isomorphic ring stalk map. The Lean proof uses the existing
`lem-weil-pbc-spec-local-ring-canonical-morphism` for that fact. Its use as a tool preserves
the finite-germ route of this unit; the unit record has no separate realized nodes to bypass.
The original free-module and module-stalk proof edges did not name the precise sheaf-level
interfaces used by the argument, as explained above. No mathematical statement was changed.

Searches actually run: leanfinder for finite-free sheaf maps equal on a stalk (eight hits,
including freeHomEquiv and hom_ext, no complete local-equality theorem); loogle for
`TopCat.Presheaf.germ, _ = _` (twelve hits); msearch grep for
`fromSpecStalk_module_stalk|free_hom_ext|restrictUnitIso|germ_eq`, plus local rg searches.
Read the source signatures of the tensor stalk comparison, tensor adjunction, canonical
local-morphism theorem, restriction and free-sheaf APIs, and Mathlib germ_eq.
The cited blueprint file is not materialized in this checkout; the existing node and full
original declaration docstring contain the finite-generator proof followed here.

## Second reading by G1

1. I compared the delivered module with the repository version. The target declaration's
signature and all existing declaration signatures are byte-for-byte unchanged; only the
proof and proof-only imports were added. Verdict: pass.

2. I compiled the module with the mandated local compiler and checked the target's axioms.
Compilation is clean, there are no `sorry`, forbidden declarations, or hollow definitions,
and `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. I checked the private helpers and the existing library before accepting them. They are
fully proved implementation helpers, introduce no public statement or split-off node, and
the searches recorded above found no existing theorem duplicating the result. Verdict: pass.

4. I followed the proof from the target downward. The added imports are proof-only and each
is used; the route keeps the finite-generator and local-germ unit argument. The node's proof
and proof dependencies were updated to the declarations actually used, while the original
target and unit statements remain unchanged. Verdict: pass.

5. I checked the node against the Lean proof and the unit record. The theorem, proof steps,
dependencies, origin, and report agree; no new node or statement was introduced. Verdict: pass.

I changed only the proof/imports, corrected the node's recorded proof route and dependencies,
and added this second-reading record.

## Earlier second reading (a previous round; superseded)

The delivered module was reread against node `lem-pc-finite-free-stalk-map-eq-shrink` and its
original declaration. The theorem signature is byte-for-byte unchanged, and the proof closes
its only `sorry`. The finite free source is handled through the existing `ιFree` coproduct
and `isColimitFreeCofan`; the empty rank case remains included. The only proof dependencies
used are the tensor-pullback stalk comparison, the tensor-pullback adjunction, the canonical
local scheme stalk-isomorphism theorem, the ringed-space stalk functor, and the source-library
restriction/free APIs. No new statement or node is introduced.
