## What changed

Changed only `lean/Sheaf/AlgebraicGeometry/CondensedFieldLfpLocalTriviality.lean` and
its existing DAG node, plus the proof-scope change record named below. All existing
public statements, universes, visibility, public imports and the public projection
construction are unchanged.

The coefficient comparison is constructed from its specified adjoint. Projection
naturality gives the continuous-function ring map. A private generic compatibility
lemma identifies the pushed-forward monoid structure with the underlying ring-sheaf
structure, so the monoidal adjunction transposes it to a ring map. On an affine, the
constructive component-map equivalence supplies a terminal comma object. Its Kan
cocone leg identifies sections with functions on connected components. Continuous maps
to the finite normed extension E factor through those components. The sheafification
unit is invertible on weakly contractible affines, and uniqueness of left adjoints
transfers this computation to the existing inverse image. Affine weakly contractible
covers detect invertibility. Adjoint equations then give the required uniqueness.

The stratum application now transports finite presentations and finite free modules
along the existing coefficient pullback isomorphism. This uses only finite biproduct
and cokernel comparison isomorphisms, the existing local-freeness theorem, and
mapModComapIso. The ring-isomorphism comap equivalence is constructed directly, so
it requires no extra commutativity typeclass.

New proof-only imports: `Sheaf.Paper.ProEtalePointComponentsMaps` (with `import all`
to reuse its proved constructive helpers), `Sheaf.Paper.ProEtaleSheafificationWcontractibleSections`,
`WeilConjectures.CategoryTheory.Sites.MonObj`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts`,
`Mathlib.Analysis.Normed.Module.FiniteDimension`, and
`Mathlib.Topology.MetricSpace.Ultra.TotallySeparated`.
The affine weakly contractible covering module remains a direct proof import.

Compilation: the complete delivered module compiles cleanly through lcompile.py
(about 15 seconds). Empty affine objects are covered by the same component-quotient
and empty-function bijections. The stratum argument also covers empty strata, rank
zero, and zero-row/zero-column presentations: no positivity or nonemptiness is used.

Change record: `coord/changes/B3-condensed-field-private-proof-scopes.md`.

## Proved and sorry left

Closed two of the original three holes:

- `AlgebraicGeometry.ProEtale.existsUnique_condensedFieldContinuousMapIso`.
- `AlgebraicGeometry.ProEtale.exists_finiteFree_cover_on_condensedField_strata`.

The only remaining sorry is
`AlgebraicGeometry.ProEtale.exists_finiteFree_cover_of_condensedField_lfp`, matching
`lem-weil-pbc-condensed-lfp-local-triviality`. Its original statement and complete
rank/descent and Gaussian-elimination proof docstring are retained. The node retains
steps 3–7 for that obligation. The stratum theorem depends on this existing hole.
No new sorry, statement module, or DAG node is added. All new private lemmas are proved;
all private data constructions have concrete bodies. These are two closed holes,
not a decomposition into new holes. Dependencies may still contain existing holes.

## No longer needed

Removed these unused direct proof imports:

- `Sheaf.AlgebraicGeometry.FpqcDetectsOpenness`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`.
- `Mathlib.RingTheory.Ideal.GoingDown`.
- `Mathlib.AlgebraicGeometry.Properties`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`.
- `Sheaf.Paper.CondensedPointBasisEvaluation`.
- `Sheaf.Paper.GeometricFieldProEtaleEvaluation`.
- `Sheaf.Paper.ProfinitePointPullback`.

The coefficient-realization proof bypasses
`lem-weil-pbc-condensed-point-basis-evaluation` and its module
`Sheaf.Paper.CondensedPointBasisEvaluation`; its direct DAG edge is removed.
The fpqc descent proof is already contained in the coefficient-sheaf construction,
so the direct `lem-weil-pbc-fpqc-detects-openness` edge is also removed.
These are removals from this item's direct requirements, not a claim that the nodes
are globally unreachable. In particular the remaining local-freeness plan retains
its geometric-evaluation, exact-pullback, going-down, and rank-partition dependencies;
they were not proved or imported speculatively in this delivery. There are no module
withdrawals. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The abstract basis-evaluation statement alone does not normalize the specific adjoint
required in this item's statement. Rather than choose an unspecified section
isomorphism, the proof computes the actual Kan comparison using the constructive
component-map equivalence and its pointwise formula. This retains the connected-component
route while proving its normalization. No existing statement was found false or changed.

A performance issue arose when asking Lean to infer the comma-object index in the
terminal Kan cocone lemma. Giving that object explicitly removed the expensive
elaboration; no timeout, heartbeat, or profiler limit was raised. The complete module
compiles well within the prescribed single-file limit.

## Second reading by B3

1. **Signatures and accidental changes — pass.** I compared the sandbox module with the
   repository version. The six public imports, `profiniteTestProjection`, and all three
   public theorem signatures are unchanged byte for byte; additions are private helpers
   and proof bodies. The node change updates only the proof route, dependencies, and
   origin to record the implemented argument.
2. **Proof and axioms — pass.** The delivered module compiles with `lcompile.py`; it has
   exactly one remaining `sorry`, the named local-freeness theorem. No forbidden commands
   or hollow definitions occur. Axiom inspection gives only the permitted axioms together
   with `sorryAx` inherited through still-open imported statements; the two completed
   declarations introduce no new sorry.
3. **Split statements and truth — pass.** No new public statement or DAG node was added.
   Every private helper is a proved compatibility, Kan-extension, or transport lemma used
   by the two completed theorems. The component quotient and empty-function arguments
   cover empty affines and rank zero, and the finite-dimensional normed-field hypothesis
   supplies total disconnectedness as used.
4. **Pruning and route — pass.** The proof uses the constructive component-map and
   weakly-contractible sheafification declarations, retains the affine-cover route, and
   removes only unused direct imports and corresponding obsolete proof edges listed above.
   The unresolved rank/descent theorem remains the sole open obligation, so no lower hole
   was added to disguise it.
5. **DAG agreement — pass.** The changed node's proof text, step uses, `proof_deps`, and
   `proof_origin` describe the code: the coefficient comparison is proved by the canonical
   adjoint/Kan route, and the stratum result by finite-presentation/free-module transport.
   The unit `sk-thm-properbasechange` and all of its realized steps remain in force.

I changed only this report section after the first delivery review; no Lean or DAG repair
was needed beyond the already recorded proof and dependency updates.
