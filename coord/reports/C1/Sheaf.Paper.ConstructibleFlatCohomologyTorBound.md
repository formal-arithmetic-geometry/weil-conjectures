## What changed

Proved `WeilConjectures.constructible_flat_cohomology_tor_bound` in its existing module,
with every existing public declaration, signature and public import preserved.
Added five proved private helpers for tensor additivity, K-flat preservation of
quasi-isomorphisms, vanishing after tensoring with a flat test sheaf, maximality of
the exponent-one coefficient ideal, and flatness from local field sections.
Updated the item's proof, proof dependencies and proof origin to match the Lean proof.

The shorter argument uses the fact that **every** module sheaf over the restricted
constant residue field sheaf is flat. Finite local models of cohomology are unnecessary.
The proof lifts finite relation coefficients locally to the field, applies vector-space
flatness, and descends the factorization by the existing local equational criterion.
It then compares the selected K-flat tensor construction with exact termwise tensoring
by the arbitrary test sheaf. Exact restriction and exact tensor preserve the supplied
homology vanishing degree by degree, without a truncation filtration.

## Proved and sorry left

Closed 1 original hole:
`WeilConjectures.constructible_flat_cohomology_tor_bound`
(node `lem-fix-constructible-flat-cohomology-tor-bound`).

Holes added: 0. Sorries left in the delivered module: 0. No statements split off.
All five new helpers are private and completely proved. Existing dependency theorems
remain dependencies; this delivery does not claim their transitive axioms are closed.
The complete proof compiled in 29.2 seconds after adding the direct ULift field
instance import. The final retained proof uses `let` for the propositional maximality instance.
The resumed dry run compiled the final proof cleanly and passed the preflight,
including the axiom probe and change-record check (2026-10-19).

## No longer needed

Removed proof-only imports:

- `Mathlib.Algebra.Homology.BifunctorShift`

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Paper.ProEtaleLocallyConstantSheaf`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.SfCommonStageWeilCohomology`

The following original proof dependencies are not used by this proof:

- `def-pur-localized-ringed-site`
- `def-weil-sheaf-of-modules-category`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pc-sheaf-modules-tensor-closed`
- `lem-sc-source-kflat-tensor-left-triangulated`
- `lem-sf-derived-homology-long-exact`
- `lem-sfb-localized-site-tensor-restriction`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-truncation-triangle`

The original bounded-above K-flatness theorem, tensor-closed package, slice tensor
comparison, global tensor descent package, triangulated tensor theorem, truncation
triangle, and long exact cohomology sequence are replaced by exact tensor with the
flat test sheaf. Their obsolete top-level tool-use entries are removed from this
node; the remaining entries retain their original order. The derived cohomology node
is still used through its Mathlib match `DerivedCategory.homologyFunctor`; its
unrelated `SfCommonStageWeilCohomology` module is not needed. Definitions appearing in
the theorem's statement remain available through the preserved public imports.
No claim is made that these nodes are globally unreachable through other parents.

## Where the brief, the DAG or earlier work was wrong

The initial attempt began from the original module. The retained sandbox now
contains the completed proof, which this resumed session checked against current sources.
The planned finite filtration is valid but unnecessary over a constant residue field:
local finite-dimensionality is stronger than required. The slice ring's section rings
need not be fields; the proof uses local lifts of coefficients to the actual field,
not a false assertion about those section rings. Empty covers, the zero test sheaf,
and zero-length relations are covered by the same local criterion.

The available compiled overlay initially lacked `ConstantFieldFlat` and an auxiliary
newer name from the local-equational-criterion source. The delivered proof uses the
existing compiled iff theorem and proves the required slice variant directly.
The resumed dry run exposed a missing `Mathlib.Algebra.Field.ULift` import after
pruning. Adding that direct proof import and explicitly binding the field structure
on the local name `κ` repaired the specialization without changing the interface.
No dependency interface, definition or target was changed. The unit record
`sk-rem-sf-pf-done` has no realized statement or proof-step nodes to bypass.


The dry run conservatively flags the added universe/open/local-instance commands and
requires a change record. Added
`coord/changes/C1-residue-tor-private-proof-context.md`, with the old and new context,
unchanged theorem signature, and all 170 transitive consumers. No consumer is adapted.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
