## What changed

Replaced the proof hole in `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTraceComparisonLimitIsos` with a proof of both specified coefficient-cone maps. The statement and public imports are unchanged. The new public helpers `diagonalOrdinaryRlim_isIso_of_epi` and `diagonalUnitComparison_isIso` are completely proved; all other helpers are private and have no holes.

The projection equations identify the ordinary cones after forgetting scalars. The quotient transitions are constant sheaves of surjective quotient maps, and the root transitions are epic by Kummer theory. The constant-ring module equivalence transfers the Milnor difference-map assertion and exact products to the actual fixed-scalar categories. The normalized Roos comparison then proves that the given derived unit, and hence each actual coefficient-cone map, is invertible. No arbitrary endpoint isomorphism is substituted for the specified maps.

Updated the item's DAG proof to record these steps and their actual dependencies. The blueprint unit's passage-to-the-limit route is preserved. No other existing module, definition, statement, or node is changed. The completed proof is split across `Sheaf.Paper.DiagonalTraceOrdinaryLimitEpi`, `Sheaf.Paper.DiagonalTraceUnitComparisonIso`, and the item module to meet the per-file compilation limit. Profiling first led to abstract categorical helper proofs and local irreducibility for the large restriction/comparison definitions; the residual kernel cost of the two concrete comparison steps is then separated between files.

Compilation: `lcompile.py --all` compiled the three modules in import order. The delivery command rechecks the final files. All diagnostic profiler/trace options have been removed.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTraceComparisonLimitIsos` (node `new-sfb-diagonal-trace-comparison-limit-isos`), the item's only original hole.

New public helper declarations proved: `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalOrdinaryRlim_isIso_of_epi` and `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalUnitComparison_isIso`. Added holes: none. Remaining holes in the delivery: zero. This is a proof from existing library declarations, rather than a decomposition into new assumptions; existing dependencies can still depend on their own unfinished proofs.

The argument covers the zero tower and empty schemes. In the generic derived-unit step, all degrees other than zero of a single tower are zero, and the degree-zero transitions are exactly those supplied. Invertibility of l on X is obtained by pulling back the given global unit on S, then mapping to residue fields. No nonemptiness or new geometric hypothesis is used.

## No longer needed

The proof does not use `lem-pur-twist-sheaf-locally-free` / `Sheaf.Paper.PurTwistSheafLocallyFree`: only its smaller root-transition ingredient `lem-pur-twist-root-transitions` is needed. Removed the former from the item's proof dependencies; its pre-existing statement-dependency entry is unchanged. This is no claim that the broader module can be withdrawn globally.

No existing Lean import was removed, and no module is withdrawn. The public import of `Sheaf.Paper.DiagonalTraceComparisonPartial` is required by the statement. The item's additional imports are private proof imports; each new module publicly imports only the definitions used in its public statement.

## Where the brief, the DAG or earlier work was wrong

The DAG's one-step Milnor plan omitted the interface bridge: its Milnor declaration is about a concrete Roos complex for ringed module sheaves, whereas the coefficient maps use fixed-ring module sheaves and an arbitrary normalized total right derived inverse limit. The proof supplies the constant-ring equivalence, kernel/short-exact Roos argument, and normalized comparison to the given derived unit. The mathematics and the item's statement require no correction.

The extra existing nodes for constant-ring module equivalence, exact products, normalized Roos comparison, and strict-tower Grothendieckness are used as general tools for this same Milnor step; they do not replace the unit's geometric route.

## New nodes

`new-sfb-diagonal-trace-ordinary-rlim-epi` (`Sheaf.Paper.DiagonalTraceOrdinaryLimitEpi`) records the fully proved Milnor/Roos comparison for epimorphic fixed-scalar towers. It is the common ordinary-to-derived step used by both cones, not a new assumption.

`new-sfb-diagonal-trace-unit-comparison-iso` (`Sheaf.Paper.DiagonalTraceUnitComparisonIso`) records the fully proved unit-map conjunct, including its ordinary cone and quotient-transition arguments. The item retains the root-line argument and combines both conclusions. Neither node adds a hole or changes the unit's route. No change record is needed because no other existing module or node is changed.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
