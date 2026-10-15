## What changed

Proved `Algebra.isIndPrincipalZariski_of_bijective_localRingHom` in
`Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso`, with its signature unchanged.
Three proved private helpers implement local denominator clearing, finite clopen
refinement, and patching through the Chinese remainder isomorphism.

The local step uses the already proved
`Algebra.factors_through_principal_localization`. The topology step uses the already
proved `WLocalSpace.closedPointsHomeomorph` and Mathlib's
`TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`.
Patching uses `CompleteOrthogonalIdempotents.bijective_pi`. The final step applies
the already proved `CommAlgCat.exists_filtered_colimit_of_factorization`.
Finite presentation follows directly from Mathlib's localization and finite-product
instances; no intervening etaleness argument is needed.

Added proof imports of `Sheaf.RingTheory.FactorsThroughLocalization`,
`Mathlib.RingTheory.Finiteness.FinitePresentationLocal`,
`Mathlib.Topology.Separation.DisjointCover`, and `Mathlib.RingTheory.Idempotents`.
Change record: `coord/changes/ind-principal-local-ring-iso-proof-imports.md` records
the redundant public-import removal, new scope commands, and all downstream users.

Updated only the existing node's `proof`, `proof_deps`, and `proof_origin` to follow
this implementation. No definition, existing signature, or target statement changed.

`lem-factors-through-localization-of-smooth` belongs to the projective-line unit and
is used as a general algebraic tool: its exact finitely-presented localization
factorization is the first part of the present node's own argument. It is already
proved; no unit statement or realized unit step is bypassed. The realized nodes of
`sk-thm-properbasechange` were checked and are unaffected.

Validation: the final module compiles through the prescribed `lcompile.py`, without
warnings, in about three seconds. A temporary `#print axioms` check reported exactly
`propext`, `Classical.choice`, and `Quot.sound` for the public theorem. The check was
removed from the delivered module. Both added Sheaf imports passed
`tools/import_direction.py may`.

## Proved and sorry left

Closed the original hole in
`Algebra.isIndPrincipalZariski_of_bijective_localRingHom`
(node `lem-weil-pbc-local-rings-ind-zariski`): 1 of 1 original holes proved.
No `sorry` remains in the item, no holes were added, and no theorems were split off.
All three private helpers are proved. The public theorem itself has only the three
allowed axioms, including through its dependencies.

Edge cases are included by the proof: empty generator and relation families use
empty products; the profinite refinement allows `Fin 0`; the orthogonal-idempotent
and Chinese remainder arguments work for that empty family and force the target
ring to be trivial; the finite-presentation instance includes an empty product.
Only target w-locality is used; source w-locality and w-locality of the map are
not assumed. No arbitrary unproved existence theorem supplies definition data.

## No longer needed

Removed these imports (the redundant public import is still publicly available
through the retained definition imports):

- `Mathlib.GroupTheory.MonoidLocalization.Away` (formerly public).
- `Mathlib.RingTheory.FinitePresentation` (provided by the retained proof imports).
- `Mathlib.RingTheory.Localization.Away.Basic` (provided by the localization tool).
- `Mathlib.RingTheory.Spectrum.Prime.Topology` (provided by the w-local API).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.RingTheory.Etale.Basic`.
- `Mathlib.RingTheory.Etale.Pi`.
- `Sheaf.RingTheory.WLocalClopenPartitions`.

The proof no longer needs the following former proof-dependency nodes:

- `lem-weil-pbc-spec-localization-away-basic-open`: no spectrum identification of
  a principal localization is needed.
- `lem-weil-pbc-w-local-partition` and its module
  `Sheaf.RingTheory.WLocalClopenPartitions`: the proved upstream connected-component
  homeomorphism and Mathlib refinement directly construct the needed partition.
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`: units in each quotient
  are checked using a maximal ideal of a proper principal ideal.
- `lem-weil-pbc-open-immersion-etale`.
- `lem-weil-pbc-etale-algebra-finite-presentation-localization`.
- `lem-weil-pbc-etale-algebra-finite-product`.

The last three are replaced by direct finite-presentation instances. This is
pruning of this item's proof dependencies; modules may remain needed by other
parents or transitively through the unchanged definition module.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature defect was found. The original plan's use of
etaleness to establish finite presentation is unnecessary. The original unproved
partition theorem is also unnecessary: the source library already proves the
closed-point/connected-component homeomorphism. The local generator and relation
clearing is already packaged in the proved principal-localization factorization
lemma, while the additional generator equalities with the original map are cleared
explicitly in this delivery.

The referenced blueprint Markdown and Stacks source files are not installed in
this checkout. The source argument was read from the assigned declaration's
complete docstring and its DAG node, and every Lean interface actually used was
read from the library or pinned Mathlib source.

## Second reading by D4

1. **Interfaces: pass.** Compared the complete delivered module with the repository.
   The existing public theorem signature is byte for byte identical, including all
   hypotheses and the conclusion. No definition was changed or added. The only
   additional declarations are three proved private helpers. The public-import and
   scope-command changes are declared in the existing change record; the removed
   public import remains publicly reachable through the retained definition import.
2. **Proof and trust: pass.** Independently compiled the delivered module with
   `lcompile.py` (exit 0, no warnings). Compiled a scratch copy containing
   `#print axioms` for `Algebra.local_factorization`, `Algebra.clopen_refinement`,
   `Algebra.patch_factorization`, and the public theorem. Each reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Checked that
   there is no `sorry`, forbidden declaration, or hollow definition. All chosen
   data comes from proved results.
3. **Split statements and edge cases: pass.** No statements were split off and no
   holes were added. Read each private helper and the declarations used for principal
   factorization, the closed-point homeomorphism, clopen refinement, and Chinese
   remainder patching. An empty generator family uses product one; the refinement
   permits `Fin 0`; the completeness equation and Chinese remainder theorem include
   the empty partition and zero ring. In each quotient, the maximal-ideal argument
   correctly proves the selected denominator is a unit. Independent LeanFinder and
   Loogle searches and `rg` searches of the library found no replacement eliminating
   these steps; there is no duplicate open theorem.
4. **Route, imports, and pruning: pass.** The final step applies the already proved
   filtered-colimit criterion, and finite presentation uses the direct localization
   and finite-product instances. All added proof-only imports are plain `import`.
   Checked the pinned Mathlib finite-product instance in `FinitePresentationLocal`
   and the topology and idempotent APIs. The six old `proof_deps` absent from the new
   proof are all listed under `No longer needed`. Read the proper-base-change unit's
   `realized` statement and three steps: none is bypassed. Principal localization
   factorization is a general proved tool, not a replacement unit route.
5. **DAG: pass.** Compared the node JSON with the repository: only `proof`,
   `proof_deps`, and `proof_origin` changed. Verified that `proof_deps` is exactly
   the union of the proof steps' `uses`, and checked the named dependencies against
   their Lean or Mathlib declarations. The seven proof steps describe the actual
   local construction, partition, patching, finite presentation, and colimit proof.
   No new nodes are required for an unproved statement.

Second reading changed only this report, adding the independent checks and verdict.
The Lean proof and node record needed no repair. The delivery closes one original
hole and adds zero holes; it is a proof, not a decomposition.
