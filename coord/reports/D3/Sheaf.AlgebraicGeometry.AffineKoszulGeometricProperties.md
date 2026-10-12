## What changed

Proved `AlgebraicGeometry.affine_koszul_geometric_properties` in
`Sheaf.AlgebraicGeometry.AffineKoszulGeometricProperties`, with its signature unchanged.
Added proof-only imports of `Mathlib.LinearAlgebra.ExteriorPower.Basis` and
`Sheaf.AlgebraicGeometry.KoszulRestrictionZero`.

Four proved private helpers establish finite freeness after open restriction,
vanishing of exterior powers above r, strict perfectness with bounds -r and 0,
and zero stalks at points of an open where a module sheaf restricts to zero.
The perfectness clause uses the explicit restricted complex on the top open and
Mathlib's derived-localization factorization. The support clause uses the existing
Koszul restriction theorem at shift zero, exact-functor homology comparisons,
and a direct argument with germs. Updated the node proof and proof dependencies
to record this route. No signature, definition, visibility, or public import changed.

## Proved and sorry left

Closed the single hole in `AlgebraicGeometry.affine_koszul_geometric_properties`
(node `lem-pc-affine-koszul-geometric-properties`). There are no sorries left in
this module and no holes added or split off elsewhere.

The existing imported `AlgebraicGeometry.isZero_restrict_shift_koszul`
(node `lem-pc-koszul-restriction-zero`, module
`Sheaf.AlgebraicGeometry.KoszulRestrictionZero`) still has its own sorry;
it is used as a stated dependency, not proved by this delivery.
The existing `ExteriorAlgebra.koszul_differential`
(node `lem-weil-pbc-koszul-differential`, module `Sheaf.Paper.KoszulDifferential`)
also remains open. Its degree assertion supplies `koszul_contract_mem` in the
existing Koszul complex construction, so the strict-perfectness helper and the
main theorem inherit `sorryAx` through that construction as well. No arbitrary
existence witness is chosen: the differential is the explicit Mathlib contraction.
Perfection itself is established from Mathlib's exterior basis and free-sheaf
isomorphisms rather than a new holed perfectness statement. Empty tuples,
positive cochain degrees, q > r, the zero ring, and empty opens are covered by
the proof without nontriviality assumptions or positive-rank assumptions.

Validation: single-file compilation through lcompile.py, without errors or warnings.
The delivery dry run also performs its axiom and declaration probes.

## No longer needed

No existing imports, nodes, or modules are pruned. All four original public imports
are required for the statement or the proof. Removed the experimental proof import
`Mathlib.Topology.Sheaves.Stalks` because its declarations are already available.
No separate new stalk-contraction, strictly-perfect-model, or homology-stalk
comparison nodes are needed: the first is supplied by KoszulRestrictionZero and
the remaining comparisons and finite-basis arguments are proved here.
`Sheaf.AlgebraicGeometry.AffineFiniteFreePerfectCore` was considered but is not imported:
its chart model differs from the actual complex in this theorem and is unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The original DAG listed definitions
but did not identify the available Koszul restriction theorem. This delivery
uses `lem-pc-koszul-restriction-zero` as a tool for the same contraction argument,
then writes the exact restriction and germ steps explicitly. This does not
bypass any realized unit step; the unit's statement and steps are untouched.
No new nodes, arbitrary witness choices from unproved existence statements,
or forced adaptations are introduced.


## Second reading by D3

1. PASS: Compared the sole delivered module with the repository using `diff -u`
   and checked the existing theorem signature byte for byte. It is unchanged;
   all four public imports, visibility, and existing docstrings are unchanged.
   Only two proof imports, four proved private helpers, and the theorem proof
   are added. No definitions or other modules are delivered.
2. PASS: Compiled the delivered file with `lcompile.py` (17.5 seconds), without
   errors or warnings. A scratch copy with `#print axioms` for all five theorems
   compiled in 15.8 seconds. The finite-free, exterior-vanishing, and germ helpers
   use only `propext`, `Classical.choice`, and `Quot.sound`. Strict perfectness
   and the main theorem additionally inherit `sorryAx` from existing open
   dependencies: the Koszul differential degree proof in the construction and,
   for the main theorem, KoszulRestrictionZero. There is no textual `sorry` in
   this module, no added hole, forbidden declaration, or witness chosen from
   unproved mere existence. Read the explicit contraction construction upstream.
3. PASS: No statements are split off and no new nodes are introduced. Checked
   the helpers at r = 0, q = 0, q > r, positive degrees, the zero ring, and empty
   opens: the exterior index becomes empty exactly when needed, and the stalk
   premise requires membership in the open. Searched the library for alternative
   finite-free and stalk-vanishing results, and Mathlib's exterior basis and
   restriction/stalk lemmas; independently confirmed `Module.Basis.exteriorPower`
   with Loogle. The existing affine-model perfectness theorem uses a different
   chart model and does not give a shorter proof for this displayed complex.
4. PASS: The top-down proof first proves perfection from the Mathlib exterior
   basis and tilde/free isomorphisms, then reduces support to the existing
   vanishing dependency using exact homology comparison and a germ argument.
   Both new imports are proof-only. Each original public import supplies a type,
   constructor, or functor appearing in the unchanged signature. Both old
   proof_deps remain used, so `No longer needed` omits no old dependency.
   Read `dag/units/sk-thm-picard-duality.json`: its realized statement and step
   lists are empty and unchanged; no realized unit step is bypassed.
5. PASS: Compared the delivered node against the repository. Only `proof`,
   `proof_deps`, and `proof_origin` change. The two proof steps describe the
   Lean argument, and proof_deps is exactly their union. Confirmed the exterior
   basis and tilde/free nodes are Mathlib leaves and the Koszul vanishing node
   names the imported declaration. Statement, source, unit, and Lean signature
   records are unchanged. No new-node fields or change records are needed.

Second reading changed only this report: documented the inherited open Koszul
differential degree proof and added these independent checks. The Lean proof
and node were retained unchanged.
