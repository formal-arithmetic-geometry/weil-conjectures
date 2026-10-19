## What changed

Proved `AlgebraicGeometry.Scheme.kummer_coefficient_base_change` without changing
its signature, the existing integral-lift predicate, or any target. The comparison
uses explicit finite dual-basis projections on the sheafified tensor and the
additive cohomology functor. The coefficient boundary is constructed by the tensor
universal property; naturality of the actual Kummer connecting homomorphism proves
the integral-lift formula for every specified lift and basis.

Added three proved helper modules: `KummerFiniteFreeComparison`,
`KummerFiniteBiproducts`, and `KummerIntegralRootComparison`. Updated the parent
node's proof, proof dependencies and proof origin to this route, and withdrew its
obsolete top-level tool approvals. No existing definition or public signature was
changed. The unit route is retained: this proves its finite-free coefficient step.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Scheme.kummer_coefficient_base_change`.

The new public helper theorems are also proved:

- `AlgebraicGeometry.Scheme.kummer_dual_basis_sheaf_comparison`;
- `AlgebraicGeometry.Scheme.kummer_finite_free_comparison`;
- `AlgebraicGeometry.Scheme.integral_cohomology_biproduct`;
- `AlgebraicGeometry.Scheme.kummer_biproduct_shortExact`;
- `AlgebraicGeometry.Scheme.kummer_integral_root_comparison`.

Zero holes remain in the four delivered modules; zero holes are added elsewhere.
This is one original hole closed, with no postponed statements or decomposition.
The proof uses the already stated Kummer module-coefficient interface, including
its existing cohomology actions; it does not claim to close holes in that dependency.

The finite-basis arguments allow an empty basis and the empty scheme. The integral
coordinate construction works for m=0 and m=1 as well: reduction is the usual
integer coordinate map when m=0 and all reduced coordinates vanish when m=1.
No division by the rank, a nonzero scalar, or a chosen nonzero section occurs.

## No longer needed

The following proof imports were removed from the item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`;
- `Sheaf.CategoryTheory.SiteCoveringAxioms`;
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`;
- `Mathlib.CategoryTheory.Abelian.RightDerived`;
- `WeilConjectures.CategoryTheory.DeltaFunctor`;
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`;
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`.

The proof does not need these former proof dependencies:
`def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-right-derived-universal-delta-functor`,
`lem-weil-pbc-bounded-below-injectives-kinjective`,
`def-pur-sheaf-tensor-product`, `def-kun-constant-sheaf`,
`lem-pc-sheaf-modules-tensor-closed`, `def-pc-flat-sheaf-modules`,
`lem-pc-sites-modules-coproduct-flat`, `lem-weil-pbc-tensor-over-quotient-ring`,
and `lem-pc-sites-sheaf-tensor-bilinear-universal`.

The concrete Kummer tensor interface already supplies the objects and insertions.
Its sectionwise tensor and sheafification universal property give the coordinate
maps directly. Additivity and boundary naturality are available for `Sheaf.H`
itself, so no comparison with a universal derived delta-functor is required.
Finite biproduct exactness replaces the general flat-sheaf argument, and reducing
integral coordinates modulo m replaces the general quotient-ring tensor theorem.
`lem-sc-kummer-exact` remains used by the new finite-biproduct helper, through
`WeilConjectures.AlgebraicGeometry.Sites.Kummer`.

All four obsolete top-level tool approvals of the parent node are withdrawn:
`lem-weil-pbc-right-derived-universal-delta-functor`,
`lem-pc-sheaf-modules-tensor-closed`, `lem-pc-sites-modules-coproduct-flat`, and
`lem-pc-sites-sheaf-tensor-bilinear-universal`.
These removals concern this proof's dependencies; no claim is made that other
parents cease to use the same modules.

## Where the brief, the DAG or earlier work was wrong

The retained report was stale: both comparison helpers already contained explicit
proofs and their node files were present. Current compilation exposed an extra
argument to `Sheaf.H.map_id_apply`, a nonexistent `Int.smul_eq_mul` name, and an
integer-module-instance mismatch when composing the quotient coordinate map.
The latter composition is made through additive maps and then given its canonical
integer-linear structure. These are proof repairs, with no statement changes.

The resumed dry run also exposed a redundant nested `map_zsmul` rewrite and
the difference between the bundled integer action on L and its canonical
additive integer action. The reduced-basis expansion now uses the composed
additive quotient map explicitly, and `int_smul_eq_zsmul` identifies the two
actions before applying the integral basis expansion.
The parent proof also needed its direct characteristic import, the forward
commutativity equations for the short-complex morphism, explicit additive-map
calculations, and a theorem-local transparency option for the biproduct terms.

The DAG's generic flatness and derived-delta-functor routes are unnecessary for
this concrete finite-basis calculation. The source's informal tensoring of G_m
with a residue-ring module is interpreted using the existing integral-lift clause;
G_m is never given an artificial residue-ring action.

## New nodes

`lem-pur-kummer-finite-free-comparison` records the normalized dual-basis sheaf
comparison and the finite-free cohomology tensor equivalence. Both are proved in
`Sheaf.AlgebraicGeometry.KummerFiniteFreeComparison` by explicit inverse maps.

`lem-pur-kummer-finite-biproducts` records the integral finite-basis cohomology
comparison and short exactness of the finite biproduct Kummer sequence. Both are
proved in `Sheaf.AlgebraicGeometry.KummerFiniteBiproducts`.

`lem-pur-kummer-integral-root-comparison` records the normalized isomorphism from
the finite biproduct of roots to the coefficient twist for a specified integral
lift. It is proved by reducing the integral dual basis and applying the proved
sheaf comparison in `Sheaf.AlgebraicGeometry.KummerIntegralRootComparison`.

These are separate finite-basis results from the source's finite-direct-sum
argument, not postponed copies of the original boundary-compatibility theorem.
Change record: `coord/changes/R1-kummer-coefficient-proof-elaboration.md` inventories
the local elaboration commands and all 171 existing transitive consumers. Existing
statements and definitions are unchanged; no consumer adaptation is necessary.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
