## What changed

Proved `AlgebraicGeometry.affine_algebra_reductions_cartesian` with its signature unchanged.
The proof glues the maps supplied by the proved affine-algebra local correspondence,
proves the quotient ring square is a pushout, transports it to affine scheme charts,
assembles the cartesian squares over an open cover, and verifies transition compatibility
by comparing section maps. All helpers are private and proved in the assigned module.
Repair: removed the two duplicate declarations `affine_over_ext` and
`exists_over_map_of_algebra`. Their replacements are combined into the stronger
`unique_over_map_of_algebra`, which supplies both the morphism and its uniqueness
for the specified section maps. Transition compatibility now applies this uniqueness
clause directly. This is a genuine strengthened helper, not a rename of either duplicate.
Updated the node's proof route to agree with Lean.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.affine_algebra_reductions_cartesian`
(node `lem-weil-pbc-affine-algebra-reductions-cartesian`). No holes added, none left.
Both the main theorem and the helpers compile with no warnings. The delivery dry run
performs the axiom probe and preflight. No data are selected from an unproved existence.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec` and proof dependency
`lem-weil-pbc-affine-morphism-relative-spec`. The proof does not require that module's
full anti-equivalence, quasi-coherence, relative-spectrum realization, or chart theorem.
It imports only `Sheaf.AlgebraicGeometry.AffineAlgebraLocalMaps` for the local construction,
and `Mathlib.RingTheory.Ideal.Maps` for descent along a surjective ring map.
All original statement imports remain necessary for the unchanged signature.
The maintainer should determine which modules become unreachable globally; other targets
may still use the full relative-spectrum theorem. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned duplicate-helper check was correct. The two existing helpers in
`Sheaf.AlgebraicGeometry.AffineStructureAlgebraFullyFaithful` are private:
importing that module and checking their source names gives `Unknown identifier`.
They therefore cannot be used by an ordinary import, and changing their visibility
would violate the forced-adaptation rule. The repair generalizes the helper in the
assigned module to existence together with uniqueness, uses both clauses, and removes
the two duplicated declarations. No other module is adapted.

No statement error found. The relative-spectrum dependency is broader than necessary:
its proved local-map component suffices. The original quotient-square step needed explicit
ring descent, top-section transport, and open-cover assembly; these are now proved.
The calculation includes zero rings, empty charts, and the zero and unit base ideals,
and requires no flatness. The referenced Stacks source files are not present on this machine;
the source and proof text supplied in the existing node and module were used.


## Second reading by A2

1. Compared the delivered module and node with the repository versions. The target declaration and all existing public signatures are unchanged byte for byte; only proof text, proof imports, and the node's proof route changed. Verdict: pass.
2. Compiled the module with `lcompile.py` and probed `#print axioms AlgebraicGeometry.affine_algebra_reductions_cartesian`; it succeeds with only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, axioms, unsafe, opaque, extern, or implemented_by declarations. Verdict: pass.
3. Searched the library for the helper and target statements and inspected the imported source. The private helper is a genuine existence-and-uniqueness result, and the quotient pushout and affine pullback helpers are strictly intermediate claims; none duplicates an existing public declaration. Their statements are true and exactly what the proof uses. Verdict: pass.
4. Read the proof top-down. It uses the shorter local-map correspondence, direct ring descent, affine pullback transport, and open-cover assembly. The removed relative-spectrum import and dependency are unused; no other import is redundant. Verdict: pass.
5. Compared the node's `proof`, `proof_deps`, and `proof_origin` with the Lean proof. They now name the local-map route and the direct quotient/pullback helpers, and the unit route remains intact. Verdict: pass.

The second reading changed only this review record; the reviewed Lean proof and node needed no repair. An additional Mathlib search for surjective pushout/kernel criteria found no direct replacement for the ring descent argument. No statements or definitions were changed, no holes were added, and the sole original hole was closed.
