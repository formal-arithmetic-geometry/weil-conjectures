## What changed

Completed all eight proofs in `lean/Sheaf/Paper/DenseOpenPiOneSurjective.lean`, retaining every
existing declaration signature and all public imports. Added proved private helpers for
faithfully flat descent of integral closure and normal stalks, curve regularity/connectedness
and relative dimension, the fibre-automorphism monoid homomorphism, Weil-pair membership and
surjective Weil-pair lifting. No definition or statement was repaired or weakened.

The proof reuses the existing source normal dense-open connected-cover and unit theorems.
It proves surjectivity on actual fibre automorphisms using Mathlib's transitivity criterion.
Normality descends along the algebraic-closure projection by an explicit faithfully flat
principal-ideal argument. Constant-cover naturality and Frobenius compatibility give the
canonical Weil-group lift and its degree and kernel properties. The existing source Weil
and geometric lisse restriction results supply clause (4). The normal-open constructibility
statement supplies clause (5). Updated the existing node's proof, proof_deps and proof_origin
and removed the obsolete open-subgroup/decomposition tool approvals.

Validation: the retained full module compiled cleanly with lcompile.py, with no warnings,
in 8.0 seconds on 2026-10-20. The current delivery parser confirms all eight existing
statement signatures are unchanged, all eight original holes are closed, no holes were
added, and every Lean line has at most 100 characters. The earlier compile-service
interruption has cleared. No other module was changed.

## Proved and sorry left

Closed 8 of 8 original declaration holes (node `lem-wf-dense-open-pi1-surjective`):

- `AlgebraicGeometry.Scheme.FiniteEtale.isConnected_pullback_of_normal_dense_open`
- `AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_normal_dense_open`
- `AlgebraicGeometry.Scheme.FiniteEtale.weilGroup_dense_open_surjective`
- `AlgebraicGeometry.Etale.isIso_lisse_unit_of_normal_dense_open`
- `AlgebraicGeometry.ProEtale.isIso_lisse_unit_of_normal_dense_open`
- `AlgebraicGeometry.WeilSheaf.dense_open_lisse_restriction`
- `AlgebraicGeometry.ProEtale.dense_open_geometric_lisse_restriction`
- `AlgebraicGeometry.Scheme.isConstructible_middleExtension_of_curve_lisse`

Zero holes remain in the item; zero holes were added; zero statements were split off.
These are proofs from existing library declarations, as required by stage 3. In particular,
clause (5) still uses the existing named constructibility dependency; no claim is made that
all transitive library dependencies are already sorry-free.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.GaloisLisseRepresentations`
- `Mathlib.CategoryTheory.Abelian.Basic`
- `Mathlib.CategoryTheory.ObjectProperty.Kernels`
- `Mathlib.RepresentationTheory.Rep.Basic`
- `Sheaf.Paper.LisseAdicFiberFunctors`
- `Sheaf.Paper.LisseModuleSheaves`
- `Sheaf.Paper.LisseTensorScalarExtension`
- `Sheaf.RepresentationTheory.LAdic`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups`
- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`
- `Sheaf.CategoryTheory.Galois.GaloisTransitive`
- `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`
- `Sheaf.Paper.EtaleWeilFundamentalRepresentation`
- `Sheaf.Paper.EtaleWeilSheafEquivalence`
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`
- `WeilConjectures.GroupTheory.WeilGroup`

Removed proof-dependency edges from this node:

- `cor-galois-lisse-representations`
- `cor-galois-open-subgroups`
- `def-galois-fibre-functor`
- `def-weil-pbc-constructible-complexes`
- `def-wf-fundamental-representation`
- `lem-fin-etale-normal-components`
- `lem-galois-transitive`
- `lem-sc-scheme-over-field-universally-open`
- `lem-wf-profinite-closed-subgroup-intersection-open`
- `lem-wf-weil-group-exact-sequence`
- `prop-wf-weil-sheaf-representation-equivalence`
- `rem-pc-regular-normal`
- `thm-galois-fundamental`

The finite-etale action/transitivity argument replaces the open-subgroup separation argument
and the FLC comparison route. Direct normal dense-open unit results replace the
representation-equivalence proof of clause (3). Source Weil and geometric restriction results
replace the etale adic representation-equivalence route in clause (4). Direct arithmetic
surjectivity plus constant-cover compatibility replaces geometric density and the Weil exact
sequence argument in clause (2). The normal decomposition statement is not used.
Removed obsolete top-level tool_uses entries `cor-galois-open-subgroups` and
`rem-pc-regular-normal`; the remaining approved entries retain their order.
These are removals from this item's proof route; no claim is made that other targets cease
to need the named modules or statement dependencies. No module is withdrawn.

The command-scope change is recorded in `coord/changes/E3-dense-open-proof-scope.md`; downstream importers require no adaptation.

## Where the brief, the DAG or earlier work was wrong

The retained report described compile-service failures; the service now compiles the full
module. The original DAG plan overlooked existing proved source APIs for the normal cases
and lisse restriction. The finite-etale Aut action gives surjectivity directly, without the
FLC equivalence or open-subgroup detour. The normality hypothesis on the geometric fibre
can be descended by faithfully flat local ring maps, allowing a direct arithmetic Weil-pair
lift. No source statement is disputed. The unit's statement and six steps are untouched;
its realized entries are empty and no separate unit realization is bypassed.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
