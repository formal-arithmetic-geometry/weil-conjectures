## What changed

Proved `ExteriorAlgebra.exists_koszul_coefficient_extension_chi` in
`lean/Sheaf/RingTheory/KoszulCoefficientExtensionChi.lean`, retaining its exact statement,
universe, hypotheses, and public imports. Added the proof-only import
`Mathlib.LinearAlgebra.ExteriorPower.Basis` and private, fully proved helpers.

The degreewise functional is an explicit construction: `Module.Basis.constr` sends each
standard exterior basis vector over S to the algebra-map image of its value over A.
The determinant coordinate formula and `RingHom.map_det` prove evaluation on arbitrary
wedges. Basis extensionality proves additivity and A-linearity. The existing
`ExteriorAlgebra.koszul_differential` gives the contraction formula; after restriction to
exterior powers it proves that the degreewise maps commute with the signed dual
boundaries. `CochainComplex.ofHom` assembles the required map.

This realizes the node's recorded basis/minor/contraction proof without a change of route,
so no DAG update or change record is needed. No arbitrary existence witness is used to
define data. The source's finite free signed-dual computation was read at Stacks Tag 0BQZ,
https://stacks.math.columbia.edu/tag/0BQZ (Lemma 48.15.5); its contraction formula is the
already proved node `lem-weil-pbc-koszul-differential`.

## Proved and sorry left

Closed 1 original hole:
`ExteriorAlgebra.exists_koszul_coefficient_extension_chi`
(node `new-lem-sc-koszul-coefficient-extension-chi`).

No sorry remains in the item, no new holes were added, and no statements were split off.
All private helpers and both private constructions are complete. The file compiles without
warnings using the prescribed `lcompile.py`. The theorem's `#print axioms` check lists only
`propext`, `Classical.choice`, and `Quot.sound`.

The argument works also for r = 0, n = 0, n > r, and the zero ring. For n = 0 the single
empty exterior basis element and the determinant of the empty matrix give the usual scalar
extension. For n > r the basis index type is empty, so the basis expansion forces the terms
and functionals to vanish. No Nontrivial, regularity, or localization assumption enters the
construction; the existing common hypotheses are retained exactly.

## No longer needed

None of the original imports, planned dependency nodes, or planned dependency modules is
pruned. The proof uses the exterior-power basis and the existing Koszul differential, as
recorded in the node. An exploratory explicit import of
`Mathlib.LinearAlgebra.Finsupp.VectorSpace` was removed after confirming its declarations
are already available through the retained imports; it was not an original dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The recorded plan is sufficient and has been
fully formalized, rather than reduced to further statements. No forced adaptations.

## Second reading by J1

1. Compared the delivered module with the repository version. The theorem statement,
   hypotheses, conclusion, universes, and public imports are unchanged; only the proof
   and one proof-only import were added.
2. Compiled the module with `lcompile.py --all`. It succeeds without errors or warnings;
   there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`
   declarations. The proof uses only the permitted kernel axioms.
3. Checked the private helper constructions and searched the library and Mathlib using
   alternate queries. No duplicate theorem or unnecessary split-off statement was found;
   no new nodes are required.
4. Traced the proof from the target through the exterior-power basis, determinant
   evaluation, and existing Koszul contraction theorem. The proof follows the recorded
   unit route, and the proof-only Basis import is necessary; no imports or dependencies
   can be pruned.
5. Compared the DAG node metadata with the Lean declaration and its actual dependencies.
   The statement and proof route agree, and the unit's `realized` route remains intact.

Changed only this report section; no Lean declarations, statements, DAG nodes, or
dependencies required repair.
