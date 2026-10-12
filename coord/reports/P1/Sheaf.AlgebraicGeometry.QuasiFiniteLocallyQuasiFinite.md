## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact`
with a complete Lean proof from the three existing proof dependencies. No signature,
definition, docstring, or import changed.

Forward: unpack `IsQuasiFinite` into local finite type, quasi-compactness, and isolated
fibre points. Choose an affine target neighbourhood of `f x` and an affine source
neighbourhood inside its preimage using `Scheme.isBasis_affineOpens`. Apply
`isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber` and package exactly the witnesses
required by `IsQuasiFiniteAtPoint`.

Reverse: use `locallyOfFiniteType_of_isLocallyQuasiFinite`, then the first component of
`quasiFiniteAtPoint_isolated_in_fiber` at every point. Package these with the given
quasi-compactness into `IsQuasiFinite`. This realizes the existing DAG plan unchanged,
including its finite-type convention; no node update is needed.

Local compilation passed without warnings. Searches of the source library and Sheaf
modules found no existing proof of this equivalence. LeanFinder and Loogle confirmed
available affine neighbourhood tools; the basis theorem suffices for the only glue.

## Proved and sorry left

Proved the module's only theorem:
`AlgebraicGeometry.Scheme.Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact`
(node `pqf-lem-qf-locqf-qc`). No `sorry` remains in the delivered module, and no new
statement with `sorry` is introduced.

The proof uses the existing separate items
`AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber`
(node `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs`),
`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`
(node `lem-weil-pbc-lqf-locally-finite-type`), and
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber`
(node `lem-weil-pbc-quasi-finite-at-point-isolated`). Their existing sorries are unchanged.

## No longer needed

None. The public definition import and all three proof imports are used. All planned
proof dependencies remain necessary; no nodes or modules are pruned. The unit record
has no realized steps for this item, and the original route is retained.

## Where the brief, the DAG or earlier work was wrong

None. The finite-type convention is already expressed definitionally in
`IsQuasiFinite` as local finite type together with quasi-compactness. The affine-pair
lemma's finite-type witness and induced algebra match the definition exactly.

## Second reading by P1

1. PASS: compared the delivered module with the repository using `diff -u`.
   Only the sole theorem's proof body differs: the existing signature, definitions,
   docstring, module header, and imports are byte for byte unchanged. There are no
   other delivered modules or change records.
2. PASS: independently compiled the file through `lcompile.py`, without errors or
   warnings. Inspected the entire proof: no remaining `sorry`, forbidden declaration,
   or hollow definition. A scratch copy with `#print axioms` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes from
   the three existing open proof dependencies listed above; this is a completed
   reduction, not an axiom-free proof of the whole dependency closure.
3. PASS: no statement was split off or newly introduced, so there are no new
   statements, small-case obligations, duplicate lemmas, or new nodes to review.
   The argument makes no nonemptiness assumption: the pointwise steps are vacuous
   for an empty source, and affine neighborhoods are chosen only for actual points.
4. PASS: read the imported definitions and all three component lemmas, searched
   Sheaf and the upstream source with `rg`, and made independent LeanFinder and
   Mathlib grep searches about finite type and isolated fibre points. Mathlib's
   `LocallyQuasiFinite` omits local finite type and is a different predicate; no
   directly applicable shorter equivalence was found. Each of the three proof
   imports is used once where needed; the public import supplies the signature's
   predicates. `No longer needed` correctly lists none. Read the unit's `realized`
   field (empty statement and step lists); the original unit route is retained.
5. PASS: read node `pqf-lem-qf-locqf-qc`. Its proof, proof dependencies, and origin
   describe precisely the two directions now written in Lean. The definition and
   finite-type convention dependencies are realized by unpacking and repacking
   `IsQuasiFinite`, and the three theorem dependencies are explicit applications.
   No DAG change is needed and no new node is present.

Changes by the second reader: appended this review and recorded independent search
results. No Lean proof, signature, import, or node needed repair.
