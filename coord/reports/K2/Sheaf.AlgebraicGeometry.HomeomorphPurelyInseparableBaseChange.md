## What changed

Proved `AlgebraicGeometry.isHomeomorph_baseChange_of_isPurelyInseparable` in
`Sheaf.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange` without changing its
signature or public imports. The existing purely inseparable universal-homeomorphism
instance supplies the property of `Spec K → Spec k`; the pullback-first-projection
instance supplies it for the canonical projection; `Scheme.Hom.isHomeomorph` concludes.
Removed the redundant direct proof import of
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`, already publicly
imported by its `.Algebra` module. The original three-step mathematical route stays.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.isHomeomorph_baseChange_of_isPurelyInseparable`
(node `lem-pc-homeo-pure-insep`). Holes closed: 1; holes added: 0.
No sorry remains in the delivered module. No intermediate statements were split off.
The proof uses existing proved source-library declarations, not sorry dependencies.

## No longer needed

Removed the redundant direct proof import
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`.
Its module remains a transitive dependency through `.Algebra`; no DAG node or module
becomes unreachable. All original mathematical proof dependencies remain needed.
The public `BaseChangeConventions` import remains: it supplies the pullback instance
needed by the unchanged public statement.

## Where the brief, the DAG or earlier work was wrong

None. The DAG's three steps already describe the implemented argument.
Typeclass inference performs the first two steps using existing proved instances.
The unit record has no realized statement or step bypassed by this proof.

## Second reading by K2

1. Compared the delivered module with the repository version. The theorem statement and
   all existing declarations are unchanged byte for byte; only the proof and a proof-only
   import were changed.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. There are
   no remaining `sorry`s, definitions containing `sorry`, axioms, unsafe declarations, or
   other prohibited constructs. A scratch `#print axioms` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. The proof uses the existing universal-homeomorphism
   instances and `Scheme.Hom.isHomeomorph`.
3. The sole closed statement is exactly the existing target node
   `lem-pc-homeo-pure-insep`; no statement was split off, and no new node is needed.
4. The proof follows the node's route: purely inseparable field extensions give the
   universal-homeomorphism instance, base change gives the pullback instance, and the
   underlying map is a homeomorphism. The removed direct import was redundant because
   `.Algebra` publicly imports it.
5. The DAG node's statement, proof dependencies, and proof origin remain consistent with
   the Lean proof; the unit route is preserved and no unit step is bypassed.

The second reading changed no Lean code; it added this review record.
