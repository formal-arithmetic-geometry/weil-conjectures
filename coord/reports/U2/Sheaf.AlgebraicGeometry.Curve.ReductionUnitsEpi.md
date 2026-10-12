## What changed

Proved `AlgebraicGeometry.Scheme.epi_upperStarGmSheafToGmSheaf_reduction` in
`Sheaf.AlgebraicGeometry.Curve.ReductionUnitsEpi` without changing its signature.
Three proved private helpers establish unit reflection for surjective scheme maps,
affine unit lifting for surjective closed immersions, and local surjectivity of
`gmSheafToLowerStarGmSheaf` for a surjective closed immersion. The main proof applies
inverse image and the adjunction counit, using topological invariance for reduction.
Updated the item's DAG proof and proof dependencies to record this shorter route.
Replaced the proof import of `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`
with `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme` for the proved criterion that
a nowhere vanishing global function is a unit. Public imports remain unchanged.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.epi_upperStarGmSheafToGmSheaf_reduction`
(node `lem-sc-reduction-units-epi`). No holes added or left in the delivery.
The module compiles cleanly, and `#print axioms` for the theorem reports precisely
`propext`, `Classical.choice`, and `Quot.sound`.
The proof works for arbitrary schemes, including the empty and already reduced
cases: it assumes neither Noetherianity nor nilpotence of the entire nilradical.

## No longer needed

Removed proof import `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`.
The proof no longer needs node `etale-proposition-etale-reduced`, its declaration
`AlgebraicGeometry.isReduced_of_etale`, or the calculation identifying the
base-changed nilradical. It also removes `def-weil-pbc-scheme-reduction` from
proof dependencies (it remains a statement dependency).
No other imports or unit steps were removed. Whether the removed module is still
reachable elsewhere is for the maintainer's closure calculation.

## Where the brief, the DAG or earlier work was wrong

No statement error. The DAG's nilradical computation and geometric-series
argument can be replaced by a shorter, fully proved argument: surjectivity on
points reflects the nonvanishing locus of a function, so any function lifting a
unit through a surjective closed immersion is already a unit. The existing
Mathlib affine characterization supplies surjectivity on functions. Its
base-change lemmas supply the closed-immersion and surjectivity instances on each
affine etale cover member. No blueprint unit statement or realized step is bypassed;
`dag/units/sk-prop-h2.json` has no realized nodes requiring the discarded lemma.

## Second reading by U2

1. **Interface: PASS.** Compared the delivered Lean file with the repository by
   `diff -u`. The sole existing theorem's signature is byte for byte unchanged;
   its original docstring and both public imports are unchanged. The only Lean
   changes are three proved private helpers, the theorem's proof, and replacement
   of a proof-only import. No definitions or change records were added.
2. **Proof and axioms: PASS.** Independently compiled the delivered module with
   `lcompile.py`: clean exit 0, no warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.epi_upperStarGmSheafToGmSheaf_reduction` reports only
   `propext`, `Classical.choice`, and `Quot.sound`. Inspected the helpers and final
   proof: no sorry, forbidden declaration, hidden data choice, or changed object.
   Unit reflection uses the exact preimage identity for basic opens; affine
   lifting uses surjectivity on global functions; the local proof constructs
   lifts after restriction to the affine cover. The final adjunction formula
   composes the inverse image of an epi with an invertible counit.
3. **Split statements and small cases: PASS.** No statements were split off and
   no holes were added. The three private lemmas are fully proved. Surjectivity
   on points is essential for unit reflection and is explicitly assumed; the
   affine hypothesis needed for function lifting is also explicit. These proofs
   work for empty schemes, identity immersions, and arbitrary nil thickenings,
   without any finiteness or uniform nilpotence assumption. Independently
   searched `lean/Sheaf`, the upstream modules, and Mathlib for unit reflection,
   `appTop`, and surjectivity on units. The existing ring-level theorem
   `IsLocalRing.surjective_units_map_of_local_ringHom` needs a unit-reflecting
   ring map and does not eliminate the geometric reflection or covering argument.
4. **Route and pruning: PASS.** Read the comparison-map definition in
   `WeilConjectures.AlgebraicGeometry.Sites.Gm`, the reduction theorem, the
   topological-invariance equivalence theorems, and `dag/units/sk-prop-h2.json`.
   The proof takes the direct affine route and then the existing equivalence;
   no realized unit step is bypassed. Both old proof dependencies omitted from
   the new proof, `etale-proposition-etale-reduced` and
   `def-weil-pbc-scheme-reduction`, are listed under No longer needed; the latter
   remains a statement dependency. The retained proof imports supply the
   reduction surjectivity, the unit criterion, and the sheaf equivalences.
   The original blueprint source file is absent on this machine; this review
   checks the local node statement and recorded unit route instead.
5. **DAG agreement: PASS.** Read the changed node and the statements/Lean records
   of all its proof dependencies. Its four proof steps follow the actual helper
   proofs and counit argument; `proof_deps` is the union of their `uses`, and
   `proof_origin` identifies the replacement of the nilradical computation by
   unit reflection. Node statement, statement dependencies, and Lean signature
   remain unchanged. No new node fields or change records are required.

Second reading changed only this report by adding the independent review.
The Lean proof and node metadata required no repairs. One original hole closed,
zero holes added, zero split-off statements: a proof, not a decomposition.
