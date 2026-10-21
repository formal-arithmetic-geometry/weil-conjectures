## What changed

Proved `Algebra.exists_integral_normal_residue_etale_splitting` with its statement unchanged.
The proof uses the finite separable residue subfields and finite intermediate residue model already
stated in the DAG. It then uses the existing, sorry-free geometric-point splitting theorem for a
finite algebra. Restriction of geometric points from D to C is bijective, so its idempotents split
B tensor D. Quotient factors have a unique geometric point; the existing integral geometric-point
criterion supplies singleton fibres and the canonical purely inseparable residue maps. A permutation
places the prescribed prime in factor zero. Five private helpers implement residue-map agreement,
purely inseparable uniqueness, restriction of points and quotient-factor bookkeeping.

Only private proof imports were changed. No definition, public signature, public import, source
module or consumer changed. The original seven-step docstring remains as a source proof plan;
the updated node records the actual geometric-point route.

## Proved and sorry left

Closed one of one original holes:
`Algebra.exists_integral_normal_residue_etale_splitting`
(node `lem-dl-a1-integral-normal-residue-etale-splitting`).
No sorry remains in the item; no hole is added or split off.
The proof still uses the already-stated declarations
`separableClosure.finiteDimensional_of_normal_of_finite_aut` and
`Algebra.exists_integral_finite_residue_model`, as intended by stage 3. This delivery does not
claim that their existing holes are closed. The cleaned module compiled successfully in 19.0 seconds with no warnings after
removing the unused proof imports; the final delivery checks compile and probe the packet.

## No longer needed

The following private proof imports were removed:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`
- `Mathlib.AlgebraicGeometry.PullbackCarrier`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.RingTheory.Spectrum.Maximal.Basic`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `Mathlib.RingTheory.TensorProduct.Nontrivial`
- `Sheaf.AlgebraicGeometry.IntegralFibreEtaleSplitting`
- `WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`

The following former proof dependencies are no longer used by this item:

- `lem-weil-pbc-integral-fibre-etale-splitting`
- `def-weil-affine-spectrum`
- `def-weil-finite-integral-morphism`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-spec-clopen-idempotent`
- `lem-weil-pbc-fibre-product-points`
- `lem-weil-common-extension-fields-tensor-nontrivial`
- `lem-weil-common-extension-fields-maximal-ideal`
- `def-weil-radicial-morphism`
- `lem-weil-pbc-fibre-product-point-residue-field`

`def-weil-affine-spectrum` remains a statement dependency. No module or declaration is withdrawn;
other callers may still need all of these nodes. In particular the source library remains intact.
The top-level tool approvals for `lem-weil-pbc-integral-fibre-etale-splitting` and
`lem-weil-pbc-fibre-product-point-residue-field` are removed because neither is used.

## Where the brief, the DAG or earlier work was wrong

The statement and the original mathematical plan were sound. The plan omitted a shorter route
through `Algebra.exists_etale_completeOrthogonalIdempotents_forall_tensor_eq`, already proved in
the adopted source library. This avoids constructing scheme pullbacks or applying the radicial
criterion. The unit realizes neither this node nor these auxiliary proof steps as a required
blueprint step, so the unit route is preserved. Edge cases: a chosen q guarantees the geometric
point set is nonempty; no reducedness, injectivity of A to D, perfectness, finite generation of D,
or finite-dimensionality of the full residue extensions is used. In characteristic zero the
purely inseparable embedding uniqueness criterion still applies.

## New nodes

`lem-dl-a1-geometric-point-etale-idempotents` attaches the existing source theorem
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_tensor_eq` in
`WeilConjectures.Mathlib.RingTheory.Etale.FiniteSplitting`.

`lem-dl-a1-integral-geometric-point-existence` attaches
`RingHom.PointsOver.exists_ker_eq` in
`WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint`.

`lem-dl-a1-unique-geometric-point-pure-residue` attaches
`RingHom.PointsOver.isPurelyInseparable_of_forall_eq'` in the same module.

These are existing source declarations, not new Lean theorems or split-off holes. Their exact
signatures and complete arguments are recorded in the nodes. The pinned source sorry map
`local/sorry_map_slopmaster2_2104a988.jsonl.gz` records all three with both own and transitive
sorry flags false. No duplicate DAG or blueprint statement was found. Each node records the
three required kinds of Mathlib search. No change record is needed because all interfaces stay
identical.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
