## What changed

Completed the existing sandbox attempt and proved
`AlgebraicGeometry.IsConnectedCurve.exists_generic_finite_coarse_trace_filtration_data`
from two new intermediate theorems. Its signature and docstring are unchanged.
`GenericFinitePrimaryDecomposition` isolates finite primary decomposition with projections
and inclusions whose composites sum to identity. `GenericPrimaryCoarseTraceRetraction`
isolates construction of a single primary filtration and its sheaf-level trace retraction.
The original module constructs the product map, applies the existing finite-morphism
cohomology edge-map theorem, and proves injectivity by the additive sum identity.

Both new modules were already present in the earlier attempt, but had no node records.
Added their DAG nodes and changed the original node's proof, proof_deps and proof_origin
to describe the actual Lean argument. There are no definitions choosing arbitrary data
from unproved existence: all choices occur inside the theorem proof.

All three modules compile together with lcompile.py --all. Import direction from the
item to CohomologyClopen is permitted. The dry-run delivery also checks their axioms.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.IsConnectedCurve.exists_generic_finite_coarse_trace_filtration_data`.
No sorry remains in the item module.

Added two holes, each the complete proof of a public named theorem in its own module:

- `AlgebraicGeometry.Scheme.exists_finite_primary_sheaf_decomposition`
  (node `lem-sc-generic-finite-primary-decomposition`).
- `AlgebraicGeometry.IsConnectedCurve.exists_generic_primary_coarse_trace_retraction`
  (node `lem-sc-generic-primary-coarse-trace-retraction`).

This is a decomposition of one hole into two, not an axiom-free proof of the geometric
construction. The first lemma involves no curve, extension, filtration or cohomology.
The second involves one primary summand and a sheaf retraction, no primary decomposition
or cohomology product injection. The genuine assembly proof supplies the missing
cohomological and additive argument; neither lower statement restates the original.

## No longer needed

Removed direct imports from the item:

- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`
- `Sheaf.RepresentationTheory.SylowModuleFiltration`
- `Sheaf.FieldTheory.OpenSubgroupFixedField`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTrace`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree`
- `WeilConjectures.SixFunctors.Finite.GlobalSections`
- `WeilConjectures.SixFunctors.Finite.Exact`

The first five are needed through the new construction lemmas (the trace definition is
publicly imported by TraceDegree), rather than directly in the item. Exact finite direct
image is still needed through CohomologyClopen. Thus these are reorganized dependencies,
not globally pruned work.

The parent no longer directly uses `lem-exc-abelian-sheaves-gmodules`,
`lem-sc-sylow-module-filtration`, `lem-exc-etale-open-subgroup-fixed-field`,
`def-weil-pbc-finite-etale-trace`, `lem-weil-pbc-finite-etale-trace-degree`, or
`lemma-weil-pbc-finite-direct-image-exact`; the lower construction or edge-map lemmas
retain the relevant dependencies. The module `WeilConjectures.SixFunctors.Finite.GlobalSections`
and node `lem-fd-finite-pushforward-cohomology` are unnecessary for this route: the already
proved abelian-sheaf edge-map formulation `lem-weil-pbc-finite-pushforward-cohomology`
in `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen` fits exactly. Other callers
may still need the removed module; no global reachability claim is made.

Second reading also removed the unused public import
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion` from the new
`GenericPrimaryCoarseTraceRetraction` module. It is not a dependency of its signature.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt compiled but lacked DAG nodes, an updated parent proof plan, and a
report, so it was not deliverable. The finite pushforward comparison originally cited is
formulated using derived global sections of ModuleCat coefficients; the existing
CohomologyClopen edge map is directly formulated for the AddCommGrpCat coefficients here.
No statement correction or departure from the unit route is needed.

The new statements were checked at the zero sheaf, empty primary decomposition,
length-zero filtration, repeated terms and zero-dimensional quotient cases. Primary
filtrations allow all these cases. A finite primary stalk has a uniform annihilating
prime power, so Bezout rescaling really gives the sheaf-level retraction. Smoothness,
affineness and connectedness of the normalization remain exactly the supplied hmodel
hypothesis; no stronger normalization assertion is silently used.

## New nodes

`lem-sc-generic-finite-primary-decomposition` records
`GenericFinitePrimaryDecomposition.lean`: primary projections and inclusions, transported
from the finite Galois module by the stalk equivalence. The docstring and node give the
Chinese-remainder proof and zero case.

`lem-sc-generic-primary-coarse-trace-retraction` records
`GenericPrimaryCoarseTraceRetraction.lean`: the Sylow filtration, fixed field, normalization
and Bezout-rescaled trace, before applying cohomology. The docstring and node give its
complete intended argument. Both follow blueprint proof paragraphs 1--2, have three
recorded search kinds, and have no exact existing blueprint or Lean match. LeanSearch
was unavailable; its failed real queries are recorded without a fabricated verdict.
No existing definition or theorem statement was changed, so there is no change record.

## Second reading by D2

1. **Existing interface: pass.** Compared the item with the repository by `diff`.
   Only its ordinary proof imports and theorem body differ. The existing theorem
   signature and docstring are byte for byte unchanged, as are all original public
   imports. There are no definitions in the delivered modules, and no existing
   declaration was weakened or supplied with extra hypotheses. No change record is needed.
2. **Kernel and holes: pass as a decomposition.** Compiled all three modules in import
   order with lcompile.py. Compiled scratch copies with `#print axioms` for each of the
   three declarations: each reports only propext, Classical.choice, Quot.sound and
   sorryAx. The main module has no sorry; the only two direct holes are precisely the
   public named theorems listed above, each with its source, proof docstring and node.
   Checked for forbidden declarations and arbitrary data definitions: none occur.
   Existential elimination and choice here are inside a theorem proof, not definitions.
3. **Split statements: pass.** Checked finite primary decomposition via an annihilator
   and Chinese remainder projections; zero stalk gives the zero sheaf and the empty sum.
   Checked the one-primary-summand statement against the existing Sylow filtration,
   open-subgroup fixed-field and trace-degree statements. A finite primary stalk has a
   uniform prime-power annihilator. The subgroup index is prime to that power, so an
   integer multiple of trace retracts restriction. Direct image preserves this identity
   without needing generic direct image to be exact. The supplied normalization model
   supplies the geometric conditions; normalization in a field supplies integrality.
   Zero modules, length-zero chains, repeated terms and dimension-zero quotients are
   valid. Neither statement is a renaming of the parent: one is just primary splitting,
   and one is the filtration and sheaf retraction for a single primary object.
   Independent leanfinder searches for equivariant primary projections and restriction
   trace retractions, a loogle search `IsPGroup, Function.Injective`, and msearch grep
   for primaryComponent/IsPGroup/directProductOfNormal found group ingredients but no
   matching sheaf construction. Also searched lean/Sheaf and lean/WeilConjectures.
   The existing FiniteEtaleFlat retraction lives on the source of the finite etale map;
   it does not replace this degree-rescaled retraction on its target. Neither remaining
   geometric construction can be closed by a short application of a found theorem.
4. **Route and pruning: pass.** Read the parent proof from the top, its former
   dependencies, the replacement CohomologyClopen edge map, and the unit record
   dag/units/sk-prop-cd-affine.json. The primary splitting, Sylow filtration, fixed field,
   trace and normalization route is retained; no unit statement or step is bypassed.
   The unit's realized arrays are currently empty and this support node is not a unit
   key node; no unit record is changed. The assembly uses the existing additive
   finite-pushforward comparison and the sum identity, rather than introducing a
   cohomological hole. All seven old proof dependencies are accounted for in
   No longer needed: six are retained below the construction/edge-map lemmas and the
   ModuleCat finite-pushforward comparison is replaced. There is no claimed global
   pruning. Removed the unused public EtaleTorsion import from the new retraction
   module; its statement assumes a finite primary stalk, not M.IsTorsion.
5. **DAG agreement: pass after metadata cleanup.** Read all three nodes alongside
   their modules. Parent proof_deps are exactly primary decomposition, primary
   retraction and the abelian finite-pushforward edge map. Its proof steps describe
   the actual projections, component retractions and finite-sum injectivity argument.
   The new nodes contain source, searches, creation, blueprint ancestry, chapter/unit,
   full proof plans and Lean records. Recorded each new Lean signature verbatim,
   including line breaks, and removed unused cohomology/torsion stmt_deps from the
   sheaf-level retraction node. The two new proof plans still cite their actual
   construction dependencies.

Second reading changed only the unused import and new-node metadata described above,
and added this review. It closed no further holes. Final count remains one original
hole closed and two strictly smaller holes added: a decomposition, with net minus one
hole closed, rather than an axiom-free proof.
