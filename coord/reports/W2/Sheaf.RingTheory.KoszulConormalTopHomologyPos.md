## What changed

Proved `ExteriorAlgebra.koszul_conormal_comparison_isIso_top_homology_pos` in
`Sheaf.RingTheory.KoszulConormalTopHomologyPos`, preserving its signature and visibility.
All new helpers are private and proved. Evaluation on the ordered top wedge identifies
the incoming image with I; complementary determinant functionals supply each generator.
The conormal basis and normalization give a surjective top component with exactly that
kernel. The next term vanishes, and a concrete cokernel argument proves the homology map
is an isomorphism. No regularity assumption is used.

Added proof-only imports `Mathlib.LinearAlgebra.ExteriorPower.Basis` and
`Mathlib.LinearAlgebra.Determinant`. The public import stays unchanged.
Updated the node's proof, proof dependencies and proof origin to describe the Lean proof;
the explicit contraction formula now records `lem-weil-pbc-koszul-differential` directly.

Read the unit record `sk-thm-picard-duality`: its realized lists are empty; this proof
preserves the local Koszul route. Read the source's signed dual calculation in
[Stacks Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ),
`lemma-regular-immersion-ext`. The local Stacks .tex file is absent on this machine,
so the source was read on its official page. The returned delivery duplicated the private
`top_functional_det` theorem of `KoszulConormalComparisonMap`. Removed that helper entirely:
`top_evaluation_injective` now applies Mathlib `AlternatingMap.eq_smul_basis_det` directly
to the two alternating maps, then uses equality of their values on the standard basis.
The existing private theorem cannot be accessed by importing its module. No comparison-map
import or change to that module is required, and no Koszul regularity is assumed.

## Proved and sorry left

Closed the module's only hole:
`ExteriorAlgebra.koszul_conormal_comparison_isIso_top_homology_pos`
(node `lem-sc-koszul-conormal-top-homology-pos`). One hole closed, zero added.
No `sorry` remains in the delivery, and no new modules or nodes are introduced.
This is a proof, not a decomposition. The zero ring, I=A, and rank one are covered
by the same algebraic formulas; no division by a nonzero element is used.

Repaired local compilation passes without warnings in approximately five seconds.
`#print axioms` for the public theorem reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the duplicated private `ExteriorAlgebra.top_functional_det` helper.
No original imports, proof dependency nodes or modules are pruned: both steps of the
original route are implemented. An initially added `Mathlib.LinearAlgebra.Dual.Basis`
import was removed because `Mathlib.LinearAlgebra.Determinant` already exports it.
The second reader removed the added proof-only import
`Mathlib.Algebra.Homology.ShortComplex.QuasiIso`: its declarations are already available
through the existing imports, as verified by compiling without it.
No conormal-basis-existence, Koszul regularity, comparison-existence, below-top-vanishing,
or dual-complex self-duality theorem is needed for this proof. None was imported.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing-tool return: the earlier proof duplicated a private theorem already
stated in `Sheaf.RingTheory.KoszulConormalComparisonMap`. The duplicate is now removed,
and its sole use is replaced by the existing public Mathlib determinant theorem.
No mathematical error was needed to change the statement or route. The node's prose
statement does not explicitly write positive rank, whereas its title and Lean declaration
do; this delivery preserves `hr : 0 < r` and leaves the separate rank-zero item alone.
The old dependency list described the contraction computation through the complex's
definition; the delivered proof makes its use of `koszul_differential` explicit.

## Second reading by W2

1. Interface: PASS. Compared the sole delivered module with the repository using
   diff and checked the public theorem signature byte for byte. Its visibility,
   docstring, hypotheses and conclusion are unchanged. No definitions, public
   imports or other modules change; no change record is needed.
2. Proof and axioms: PASS. Independently compiled the delivered file without
   warnings. Compiled a fresh scratch copy with `#print axioms` for all ten private
   helpers and the public theorem; every result lists only `propext`,
   `Classical.choice`, and `Quot.sound`. No sorry or forbidden declaration remains.
   The local existential witnesses are obtained from proved facts, and no data
   is defined by choosing a witness of an unproved existence theorem.
3. Split statements: PASS (none). Zero holes added, no new public statements or
   nodes. Read the private arguments: complementary pairing is the empty-wedge
   pairing in rank one; both signs square to one in characteristic two as well.
   The singleton top basis proof also covers rank zero, while the incoming-range
   lemma explicitly needs positive rank. For I=A and the zero ring all quotient
   values vanish and the ideal/image argument still works. Library and Mathlib
   searches found no shorter top Koszul homology result; the existing private
   determinant helper is not duplicated. The proof already uses Mathlib's
   determinant, exterior basis, pairing, and cokernel transport results directly.
4. Route and pruning: PASS. Read the proof from its public conclusion through
   the surjective component, kernel/image equality, and outgoing-zero helpers.
   No unused old proof dependency remains. Confirmed by independent scratch
   compilations that removing either added proof-only import fails (basis and
   determinant/dual-basis declarations respectively). The existing public import
   supplies the theorem's signature. The unit realized fields are empty, its
   statement and step are unchanged, and the local Koszul route is preserved.
5. DAG: PASS. Compared the node with the repository: only proof, proof_deps and
   proof_origin differ. Their four steps follow the actual proof, including the
   explicit use of koszul_differential and the Mathlib pairing/basis declarations.
   Their uses union agrees with proof_deps; the statement and Lean signature
   records stay unchanged. The existing prose's omission of positive rank is
   already reported above and is not used to alter the formal statement.

Changes in this independent second reading: appended this review and refreshed
scratch axiom/import checks. No further Lean or node repair was necessary; the
received proof already contains the duplicate-helper repair and import pruning
recorded above. One original hole closed, zero added, no modules pruned.
