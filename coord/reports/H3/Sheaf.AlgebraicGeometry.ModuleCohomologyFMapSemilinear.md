## What changed

Proved `AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_semilinear`
with its original signature and docstring. The only changed module is
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapSemilinear`; its imports are unchanged.

A fully proved private helper transports commutation with scalar multiplication
through the forgetful homology comparison. It uses Mathlib's
`ShortComplex.homologyMap_comp` and `ShortComplex.homologyMap_mapNatTrans`, applied
to `ModuleCat.smulNatTrans`.

The main proof follows the existing node's argument. `D.sections` makes the
components of `D.a.inv`, and consequently `D.a.hom`, identities on underlying
additive groups. The pushforward scalar action is restriction along `h.appTop.hom`.
Linearity of the sections of `D.lambda` therefore gives scalar compatibility of
its composite with `D.a.hom`. The private helper transports this equation to
homology. Bijectivity of the vertical map yields the scalar equation for its
inverse. Compose this inverse with module homology of the sections of `D.β` and
the two module resolution comparisons. Naturality of the forgetful homology
comparison proves that the underlying additive map is exactly `D.map p`.

No extra hypothesis, statement change, definition change, or chosen witness from
an unproved existence theorem is introduced. There is no inverse ring map and no
surjectivity requirement on `h.appTop.hom`. The construction works also in degree
zero and for zero modules or rings.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_semilinear`
(node `lem-weil-pbc-module-cohomology-fmap-semilinear-lift`).

No `sorry` remains in the item. No holes were added or split off. The private
helper `homology_scalar_comm` is fully proved. This is a proof, not a decomposition.

Local compilation passes without warnings in approximately 19 seconds, under
the standard 60-second file limit. A local heartbeat allowance of 800000 covers
elaboration of the nested evaluation, homology, and resolution comparisons; it
does not alter that wall-clock limit.

## No longer needed

None. The sole import `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap` is needed by
both the original statement and the proof. The proof needs exactly the existing
node's dependency `def-weil-pbc-module-cohomology-fmap`; no planned dependency,
node, module, or unit step is bypassed. No additional Sheaf imports were added.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned scalar check on cycles and homology can
be carried out using Mathlib's natural-transformation homology comparison, so no
new deferred comparison theorem is necessary. The node's existing proof plan and
proof dependencies still describe the implemented argument. The unit route is
unchanged.

## Second reading by H3

1. **Interface unchanged — pass.** Compared the entire delivered module with the
   repository version using `diff -u`. The sole existing declaration,
   `AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_semilinear`,
   retains its signature byte for byte, its visibility and its docstring. The
   changes are its proof, one fully proved private helper, a noncomputable section,
   and declaration-local elaboration options. No definition or public import changed.
2. **Proof and axioms — pass.** Compiled the module locally with `lcompile.py`:
   clean, no warnings, 15.2 seconds. Compiled a scratch copy with `#print axioms`
   for both `homology_scalar_comm` and the public theorem: each uses only
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Read every proof step and checked the source of the Mathlib homology and
   scalar natural-transformation lemmas. There are no sorries, prohibited
   declarations or attributes, hollow definitions, or choices from deferred
   existence proofs in this delivery. The semilinear map is constructed explicitly
   from the existing additive composite.
3. **Split statements and edge cases — pass.** No statements are split off and
   no holes are added. The private helper transports precisely a given scalar
   commutation equation through homology comparison, using
   `ShortComplex.homologyMap_comp` and `homologyMap_mapNatTrans`.
   Its argument covers arbitrary rings and zero short complexes. The public
   proof works at degree zero and for zero modules or rings; the inverse scalar
   equation uses injectivity of the additive isomorphism and does not require
   surjectivity or injectivity of the ring homomorphism.
4. **Route and pruning — pass.** Independently searched Mathlib through
   `msearch.py` with scalar-commutation and additive-chain-map terminology, and
   searched the library with `rg`. The returned `homologyMap_smul` family concerns
   scalar multiplication of morphisms in one linear category and does not replace
   the comparison between different scalar rings. The upstream higher-direct-image
   semilinear comparison uses different cohomology objects and extra geometric
   assumptions, so it cannot replace this theorem for arbitrary resolution data.
   The implemented route directly uses Mathlib's natural-transformation homology
   comparison, followed by inverse scalar compatibility and linear resolution
   comparisons. The sole public import is required by the original signature.
   The old sole proof dependency remains used; `## No longer needed` is complete.
   Read `dag/units/sk-thm-p1.json`: no unit realization or route is bypassed.
5. **DAG agreement — pass.** Read the item's node and its sole proof dependency.
   The existing node's scalar-compatibility proof plan describes the implemented
   sections/homology/resolution argument; `proof_deps` is exactly
   `def-weil-pbc-module-cohomology-fmap`, and `proof_origin` already identifies
   this scalar check for arbitrary resolution data. No node update is required.

**Changes by the second reader:** added this review section only. No mathematical,
Lean, import, node, statement or definition repair was needed. Confirmed one hole
closed and zero holes added: proved 1 of 1, with no decomposition or split-off lemma.
