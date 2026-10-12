## What changed
Proved `AlgebraicGeometry.exterior_dual_pairing_functional` with its original signature and
docstring. On Over U the components are Mathlib's `exteriorPower.alternatingMapToDual`
evaluated on the given dual sections. Naturality is proved on pure wedges using exterior
restriction, naturality of the dual sections and `RingHom.map_det`. The sheafification unit
remains locally bijective after restriction; `homEquivOfIsLocallyBijective` extends the
constructed presheaf morphism to the exterior sheaf. Its inverse law gives the formula.
`exteriorSheaf_dual_ext` gives uniqueness. Updated the node to record this exact route.

## Proved and sorry left
Closed the one original hole: `AlgebraicGeometry.exterior_dual_pairing_functional`
(node `lem-sc-exterior-dual-pairing-functional`). No sorries remain, and none were added.
No new object is chosen from an unproved existence theorem: the functional is constructed
as the inverse of the proved Hom equivalence. The construction uses no freeness assumption
and makes no exceptions for degree zero, empty opens or zero rings.

## No longer needed
Removed the direct proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: the original public import
of `WeilConjectures.AlgebraicGeometry.Modules.Dual` already provides that interface.
No original DAG proof dependency or module is pruned: the original construction plan is
implemented. Added only the proof imports `ExteriorSheafDualExt`, Mathlib exterior pairing,
and preservation of local bijectivity under restriction. No new nodes.

## Where the brief, the DAG or earlier work was wrong
No mathematical error was found. The existing global pairing theorem cannot supply a
shorter proof: its module depends through `DeterminantDualAlternatingFamily` on this item.
The original plan is sufficient. Type inference on the restricted scalar modules required
explicit determinant equalities rather than unrestricted rewriting.

## Second reading by U1
1. Compared the sole delivered module with the repository using diff and checked the
   existing theorem signature byte for byte with Python. Signature, visibility,
   definitions and docstring are unchanged. All added imports are proof-only imports;
   no change record or forced adaptation is required. Verdict: pass.
2. Independently compiled the delivered file with lcompile.py (27.7 seconds, no errors
   or warnings). Compiled a scratch copy containing the full proof and printed its
   axioms (21.6 seconds): exactly propext, Classical.choice and Quot.sound, no sorryAx.
   Scanned the delivered Lean for sorry and forbidden declarations: none. The local
   functional is constructed by the inverse of a proved Hom equivalence; the exterior
   restriction is uniquely characterized, not an arbitrary existence witness.
   Verdict: pass.
3. No statements or nodes were split off or added, so no new statement needs a
   duplicate search. Read Mathlib ExteriorPower/Pairing.lean: alternatingMapToDual
   and its evaluation lemma are precisely the tuple-level determinant pairing.
   The empty tuple gives determinant 1; pure wedges still span in degree zero.
   The zero ring and empty open require no exceptional assumptions. Verdict: pass.
4. Read the entire proof top downward, the exterior-sheaf construction, the proved
   exteriorSheaf_dual_ext, and the local/global determinant pairing modules. Searched
   the library for exterior/dual/determinant alternatives: the global construction
   depends back on this item, so it is not a shorter independent route. Each added
   import supplies a used interface (extensionality, ring pairing, or preservation
   of local bijectivity). The removed InternalHom import is already supplied by Dual.
   No old proof dependency is abandoned; No longer needed is complete. Read
   dag/units/sk-thm-picard-duality.json: its realized entries are unchanged and this
   helper preserves the existing determinant construction route. Verdict: pass.
5. Compared the delivered node with the original: only proof, proof_deps and
   proof_origin changed. Checked each proof step against the Lean: sectionwise
   determinant, naturality on wedges, restriction of the sheafification unit,
   extension by homEquivOfIsLocallyBijective, and uniqueness by exteriorSheaf_dual_ext.
   The added extensionality dependency is recorded. The ring pairing node supplies
   the pairing whose tuple-level precursor the proof uses. Verdict: pass.

Second-reading changes: appended this independent review; no Lean or node repair was
needed. Closed holes: AlgebraicGeometry.exterior_dual_pairing_functional (1 of 1).
Added holes: none. Split-off statements: none. Pruned nodes/modules: none.
