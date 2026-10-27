## What changed

Proved `TopCat.Sheaf.subsingleton_H'_top_of_spectralSpace_of_dimension_le` by induction
on the finite dimension bound. The existing punctured spectral dimension theorem,
punctured-neighborhood colimit comparison, and profinite vanishing supply the geometric
inputs. Mathlib's abelian-sheaf Mayer--Vietoris sequence supplies all exactness directly.
The proof of vanishing from top-degree surjectivity uses local Ext effacement and a
finite compact-open cover, followed by dimension shifting, rather than the longer
integer-module comparison and truncated-resolution argument. The proof helpers are private and proved. A private Mayer--Vietoris square records
its objects and arrows directly and uses Mathlib's existing pushout proof; this avoids
repeated reduction through the general pullback constructor during type checking.
The finite cover is eliminated as an existential witness, so its opens remain abstract
while the finite-union argument is checked. The finite-cover induction is proved for
abstract presheaves and instantiated with the two cohomology presheaves once; this
prevents repeated unfolding of cohomology throughout the induction. The theorem's signature, public imports and universe remain unchanged.
The node's proof and dependencies now follow this argument.

The module-command flag is documented in
`coord/changes/T6-spectral-cohomology-proof-commands.md`. New checking attributes
are local; downstream inspection found no current Lean importers. No consumers
require adaptation.

Validation: the complete module passed `lcompile.py` at the normal budget in 42.9 seconds.
No diagnostic options or heartbeat overrides remain.

## Proved and sorry left

Closed 1 of 1 existing holes:
`TopCat.Sheaf.subsingleton_H'_top_of_spectralSpace_of_dimension_le`
(node `lem-sfb-spectral-space-cohomology-dimension`). Added 0 holes; split off 0 statements.
No sorry remains in the delivered module. This is a proof from existing declared
geometric dependencies, whose own proofs remain separate items.

## No longer needed

Removed proof imports:
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`
- `Sheaf.Topology.WLocalComponents`
- `Sheaf.AlgebraicGeometry.FilteredColimitElementEventuallyZero`
- `WeilConjectures.Topology.ModuleMayerVietoris`
- `WeilConjectures.Topology.RestrictInjectiveResolution`
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`
- `WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `Mathlib.Algebra.Category.ModuleCat.EnoughInjectives`

The proof no longer needs nodes `def-weil-pbc-constant-sheaf`,
`def-weil-sheaf-of-modules-category`, `def-sc-ringed-space-module-cohomology`,
`det-pe-wlocal-components`, `lem-sc-mayer-vietoris-ringed-space`,
`lem-sc-ringed-space-restrict-injective-resolution`,
`lem-weil-pbc-injective-sheaf-mono-restriction`,
`lem-sfb-quasi-compact-restriction-acyclicity`, `lemma-weil-pbc-leray-acyclicity`, or
`lem-weil-pbc-ring-modules-enough-injectives`. The same obsolete entries were removed
from the item's top-level tool approvals, preserving the order of retained entries.
None of those existing modules or declarations is withdrawn; other consumers retain them.
The filtered-colimit zero criterion remains a mathematical dependency, implemented
by Mathlib's general same-universe `Limits.IsColimit.eq_iff'` rather than the
older wrapper whose groups live one universe higher.

## Where the brief, the DAG or earlier work was wrong

The statement is correct and unchanged, including arbitrary non-Noetherian spectral
spaces, upper dimension bounds and the empty space. The original plan's integer-module
bridge and truncated acyclic resolution are unnecessary: direct abelian Mayer--Vietoris
and local vanishing yield a shorter proof. At dimension zero the existing proved
spectral-T1 instance gives profiniteness directly, so the much stronger w-local
components theorem is unnecessary. No unit statement or unit proof step is bypassed;
this node is below the compactification-coherence unit's realized statements.

Existing whole-library and Mathlib searches found no theorem proving the spectral
cohomological dimension bound directly. The sandbox search log records the grep,
Loogle and Lean Finder queries. The Noetherian vanishing theorem cannot handle the
present hypotheses. Edge cases checked in the argument include the empty space,
empty/full compact opens, zero-dimensional spaces and the empty finite cover.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
