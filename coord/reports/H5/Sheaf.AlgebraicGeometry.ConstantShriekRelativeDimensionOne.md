## What changed

Kept the signature of
`AlgebraicGeometry.Etale.constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one`
unchanged and replaced its proof hole by a complete Lean reduction. The proof now contains:

- Noetherian induction on closed subsets, quantifying over all closed scheme structures;
- homology base-change and constant-pullback comparisons;
- the good-curves generic diagram and descent along its finite surjective base cover;
- a proof that a dense open in a Noetherian curve has zero-dimensional complement,
  and the resulting quasi-finiteness of the original curve boundary;
- constructibility of the constant complex and quasi-finite boundary pushforward;
- the proper-model calculation, including identity compactifications and composition
  with each finite etale map;
- open-closed localization and the closed-surjective-cover argument, with the empty
  open's derived compact-support object proved zero.

Added `Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible` and proved its
cohomological calculation in Lean. It assembles the finite coproduct of proper
models by induction, using open-closed localization for one clopen component at
a time, and then applies localization to the inverse image of W. The empty
coproduct's compact-support object is proved zero. This removes the need for an
extra Mayer-Vietoris or compactification-independence hypothesis.

The repair removes the duplicate local `constantSingle_constructible` theorem
from the assigned module. The identical theorem in
`GoodCurvesPreimageConstructible` is now public (with its required public import)
and the assigned proof uses that declaration directly, satisfying the import-prune
review.

The only remaining hole is geometric, in
`Sheaf.AlgebraicGeometry.GoodCurvesPreimageBoundary`: identify the finite inverse
image of W with an open in the proper models and prove quasi-finiteness of its
closed complement. Its statement contains no coefficients, sheaves, cohomology,
constructibility, generic descent, original curve boundary, proper-model
pushforward, or Noetherian induction. The Lean proof combines this geometric
step with the cohomological arguments, rather than renaming the original claim.

The source read was `literature/stacks-project/more-etale.tex`, Tag 0GKX,
`lemma-constant-shriek-rel-dim-1`, including the two localization triangles and the
finite sum of proper smooth models. The unit's route through classical
constructibility is retained. All three modules compiled cleanly in import order:
the geometric statement (2.9 seconds), the cohomological intermediate (52.7 seconds),
and the assigned module (46.1 seconds). A normalized
comparison confirms that the original theorem signature is unchanged.

The helper's visibility and the GoodCurves module's public imports changed; its
statement is unchanged. No consumer adaptation or change record is needed.

## Proved and sorry left

Original holes closed: **1**, in
`AlgebraicGeometry.Etale.constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one`.
The assigned module now has **0** `sorry` tokens.

The duplicate `constantSingle_constructible` proof was removed and replaced by a
call to the existing theorem exported from `GoodCurvesPreimageConstructible`.

Also proved the new intermediate declaration
`AlgebraicGeometry.Etale.goodCurvesPreimage_constantShriek_constructible`, node
`lem-weil-pbc-good-curves-preimage-constructible`, in
`lean/Sheaf/AlgebraicGeometry/GoodCurvesPreimageConstructible.lean`.

Holes added: **1**, in
`AlgebraicGeometry.Etale.goodCurvesPreimage_boundary`, node
`lem-weil-pbc-good-curves-preimage-boundary`, in
`lean/Sheaf/AlgebraicGeometry/GoodCurvesPreimageBoundary.lean`.
Its proof is exactly `by sorry`, with the full source argument in its docstring and node.
This is a decomposition: one original hole closed, one strictly smaller hole added,
net zero holes by the per-delivery count. No claim of a complete axiom-free proof is made.

What remains in the geometric lemma: distribute the pullback over the finite
coproduct, compose its component open immersions into the proper models, identify
the image open and its map to the base, prove properness and Noetherianity of the
finite coproduct, and apply the existing good-curves-boundary quasi-finiteness
assertion using fibrewise nonemptiness. All finite-union, constant-complex,
quasi-finite shriek and localization arguments are now Lean proofs.
For finite-family point arguments, `sigmaOpenCover` with `exists_eq` handles
`Fin n` directly; `sigmaMk` ties the index universe to the scheme universe.
The finite-cover thickening comparison is fully proved in the assigned module.

Edge cases checked against the statement and source: empty index family or empty W
(the source is empty and its compact-support object is zero), empty T_i, zero module,
zero coefficient ring, zero-dimensional proper fibres (a nonempty open in their smooth
geometrically connected fibre is the whole fibre), and nilpotent base structures.
The main induction handles nilpotents directly and does not assume a reduced base.

## No longer needed

Removed these direct imports from the assigned module:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale` (already exposed by diagram statements).
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` (the proved source API is used).
- `WeilConjectures.ConstructibleSheaf.Defs` (exposed by the constructibility APIs).
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `WeilConjectures.ConstructibleSheaf.KernelCokernel` (the proved triangulated
  constructible-homology API supplies the needed Serre calculation).
- `Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometry`.
- `Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`.
- `Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly`.
- `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` (the source definition
  and proved comparison are used).

The only newly exposed dependency is
`WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` in
`GoodCurvesPreimageConstructible`, required because its shared helper is public.

Removed direct proof dependencies:
`def-sbc-smooth-morphisms` (still a statement dependency),
`def-weil-constructible-subset`,
`lem-weil-pbc-constructible-stratification-assembly`,
`lem-weil-pbc-finite-type-noetherian-finite-presentation`, and
`lem-weil-pbc-reduced-induced-closed-subscheme`.
The induction uses the proved source open-closed constructibility criterion, and
Mathlib's canonical closed complement, so the bespoke stratification assembly and
reduction argument are unnecessary. Local finite presentation is supplied by
smoothness or the locally Noetherian finite-type instances.

`lem-weil-pbc-good-curves-boundary-quasifinite` moves from the parent's direct
proof dependencies into the geometric lemma's plan; it is not globally unnecessary.
`lem-weil-pbc-etale-shriek-relative-mayer-vietoris` and
`lem-weil-pbc-etale-shriek-compactification-independence` are not used in either
Lean proof or the remaining geometric obligation. The finite-union calculation uses
open-closed localization, and every triangle already accepts the prescribed
compactifications. The parent's explicit compactification-independence import is
replaced by the composition isomorphism for its prescribed compactification.

Removed the obsolete approved tool-use entry
`lem-sbc-smooth-connected-generic-geometry`. The proper-model step uses the fibrewise
geometric-connectedness hypothesis directly. No unit-level statement or step is pruned,
and no global closure-size reduction is asserted without the ledger's measurement.

## Where the brief, the DAG or earlier work was wrong

The node `lem-weil-pbc-good-curves-boundary-quasifinite` records
`Sheaf.AlgebraicGeometry.GoodCurvesBoundaryQuasiFinite`, but its Lean source is absent
from this checkout. A compile probe also reports that its compiled object does not
exist on the compile server. Thus one of the promised declared proof dependencies
cannot currently be imported. I did not recreate or weaken that existing statement.
The geometric lemma's source proof still cites it for the second boundary; its declaration
needs to be restored before the next worker can call it.

The returned duplicate-helper finding was correct: the assigned module repeated
word-for-word the `constantSingle_constructible` theorem already present in
`GoodCurvesPreimageConstructible`. Exporting and reusing that theorem fixes the
issue without changing either statement.

The existing docstring's separate passage to a reduced base is unnecessary. The
formal closed-subset induction quantifies over every closed immersion, including
nonreduced ones, so base change and open-closed gluing apply without that passage.
The theorem statement itself is unchanged and was not found false.

## New nodes

`lem-weil-pbc-good-curves-preimage-constructible` is the cohomological calculation
on the finite preimage of W, conditional on constructibility of the proper models.
Its proof is Lean code: finite-coproduct induction and open-closed localization,
using `lem-weil-pbc-good-curves-preimage-boundary` for the geometry.

`lem-weil-pbc-good-curves-preimage-boundary` isolates the geometric embedding and
its quasi-finite complement. It remains `sorry`. The existing boundary node
asserts quasi-finiteness after an open is supplied, whereas this statement also
constructs that open from the pullback and records the compatibility over V.
Both new statements follow the indicated portions of Tag 0GKX. LeanSearch,
LeanFinder, Loogle and grep searches were run and recorded; source/DAG and blueprint searches found
no matching declaration. Both nodes record the proper-finiteness blueprint ancestry
and the precise source portion. No existing public signature or definition changed,
so there is no change record.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
