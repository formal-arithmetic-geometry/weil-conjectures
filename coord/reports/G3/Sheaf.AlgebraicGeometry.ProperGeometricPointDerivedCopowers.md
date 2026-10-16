## What changed

Proved `AlgebraicGeometry.Etale.proper_geometricPoint_preservesCopowers` with its original
signature and visibility. The proof now uses two already proved source-library declarations:

- `AlgebraicGeometry.Etale.hasFiniteCohomologicalDimensionMorphism_of_isSepClosed_of_locallyOfFiniteType`,
  applied to `p` and the identity structure map on `Spec k`;
- `AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar`, specialized to the
  constant family at `E`.

The finite coefficient ring is additively torsion by `isAddTorsion_of_finite`. Properness
supplies the finite-type and qcqs hypotheses, and algebraic closedness supplies separable
closedness. The single new import is proof-only:
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts`.
The two original public imports are byte for byte unchanged.

The second reading removed all three initially proposed supporting modules and their nodes:
the source library already proves the categorical, classical-coproduct and dimension results
needed here. Two new DAG nodes attach the source declarations actually used; neither adds a
Lean declaration. No existing statement or definition changed, and no change record is needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.proper_geometricPoint_preservesCopowers`
(node `lem-etale-proper-geometric-point-derived-copowers`).

Holes closed: one of one. Holes added: zero. Split-off statements left with sorry: none.
No new Lean declarations are delivered. This is a proof, not a decomposition.

The final module compiles cleanly through `lcompile.py`. A scratch copy with `#print axioms`
for the target, both source declarations, and the general source finite-dimension coproduct
theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The proof includes empty schemes, empty indexing types, and the zero coefficient ring.

## No longer needed

Removed all six original direct proof imports:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`
- `Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension`
- `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`

The first four remain transitive imports of the proved source route. The last two leave this
item's import closure: their open declarations are unnecessary for this Lean proof. No global
pruning claim is made, since other users may still reach them. Global progress and pruning
remain the maintainer's pinned sorry-ledger calculation.

All five original direct `proof_deps` were replaced by the two source attachment nodes:

- `thm-sc-finite-type-torsion-cd`: its separate holed Lean realization is unnecessary;
  the same mathematical bound remains an ancestor of the source relative-bound node.
  Its existing `tool_uses` approval is therefore retained.
- `lem-weil-pbc-etale-module-cohomology-forget`: not used by the final direct-image argument;
  the source dimension proof uses the relative coefficient comparison instead.
- `lem-weil-pbc-cohomology-filtered-colimit`: retained indirectly through the source
  higher-direct-image filtered-colimit argument.
- `lem-pur-kinjective-degreewise-existence`: retained indirectly through the source coproduct
  proof, and recorded on its attachment node.
- `lem-kun-finite-cd-acyclic-complex`: its holed statement is no longer used. The source
  finite-dimension theorem has its own proved dimension-shifting argument, recorded through
  `lem-kun-pointwise-finite-cd-exact-complex`.

The initial sandbox's three new supporting modules were never part of the repository; their
removal eliminates duplicate proposed code and is not counted as pruning landed modules.

## Where the brief, the DAG or earlier work was wrong

The first worker missed the exact source-library theorems in
`DerivedCategory.FiniteCohomologicalDimension` and `Etale.Derived.Kunneth.Coproducts`, plus the
separably-closed finite-type dimension theorem in `Kunneth.CohomologicalDimension`.
The target needs only a specialization of those proved results. Reconstructing the acyclic
comparison and point-equivalence reflection introduced duplicate code and an avoidable
transitive dependence on `sorryAx`.

The revised proof remains the proper-factor finite-coefficient coproduct argument, below the
unit level. `dag/units/sk-prop-sf-cbc.json` has no realized statements or steps; its compact-support
base-change route is untouched. No false target or supporting statement was found.

## New nodes

`lem-etale-finite-type-sep-closed-derived-dimension` attaches the existing proved source
`AlgebraicGeometry.Etale.hasFiniteCohomologicalDimensionMorphism_of_isSepClosed_of_locallyOfFiniteType`.
Its record includes the exact written signature, ambient coefficient variables, source proof,
and the existing relative torsion dimension dependency. No Lean file is added.

`lem-etale-qcqs-finite-dimension-derived-coproducts` attaches the existing proved source
`AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar`. Its proof record follows the
source reduction to classical coproducts and its proved finite-dimension derived-category
argument. No Lean file is added.

## Second reading by G3

1. Compared the delivered module against the repository with `diff` and compared its theorem
   signature byte for byte. Verdict: the existing declaration, universes, hypotheses,
   conclusion, visibility and public imports are unchanged. No other existing Lean file changes.
2. Compiled all four initial modules, then compiled the final shorter module. Inspected for
   forbidden declarations, hidden holes and data chosen from unproved existence. Verdict:
   the delivered file has no holes or new data definitions. `#print axioms` for the final target
   and the source theorems reports only the three permitted axioms, with no transitive sorry.
3. Read each initial supporting statement and proof, including the acyclic-unit naturality,
   filtered finite-subsum passage, empty-scheme case and positive characteristic of the zero
   ring. Repeated Mathlib searches with different wording using LeanFinder, LeanSearch and
   grep, and searched both local library roots. Verdict: the initial statements were true,
   but duplicated source results. Removed them and attached the existing proved declarations.
   The source statements require no nonempty index type, nonempty scheme, nonzero ring,
   invertible torsion order, or constructibility hypothesis. No statement is split off.
4. Checked the shortest source route and the unit's `realized` record. Verdict: replace the
   longer global-sections/reflection argument by finite dimension of p and the source
   coproduct-preservation theorem. Only the necessary proof import remains. Listed every
   removed original import and the disposition of all five old proof dependencies above.
   The proper-factor route and unit-level plan are preserved.
5. Checked both new source attachment records and the updated target node against the Lean
   proof and source signatures. Verdict: `proof_deps` equals the union of step uses, sources
   and origins identify the proved declarations, and the source attachments add no holes or
   duplicate Lean statements. Original immutable node fields stay unchanged.

Second-reading changes: replaced the proof by the short source specialization; removed all
three proposed supporting modules and their nodes; added two source attachment nodes;
updated the target proof record, docstring, pruning inventory and report. No mathematical
statement, definition, target interface or consumer was changed.
