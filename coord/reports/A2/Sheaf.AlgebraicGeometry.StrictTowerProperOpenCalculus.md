## What changed

The four alpha obligations use the existing projector and alpha-pasting declarations:
`alpha_cartesian`, `alpha_vertical`, `alpha_horizontal`, and `alpha_baseChange`.
`gamma_evaluation` is assembled from `MateEvaluationScalars.evaluation_gamma`, naturality
in `originIso`, and cancellation of the prescribed comparison isomorphisms, with the
single-level coefficient-realization step stated separately.

The calculus statements and public definitions are unchanged. Its original proof of
`pi_components` is preserved. A generic private cohomology argument avoids ambiguous
coefficient universes in `gamma_isIso`; local irreducibility of `finiteSource` and
`finiteTarget` keeps their large comparison composites folded in that proof.

`TowerOpenBetaNormalization` loses only its unused public import of the calculus.
This is necessary to use the declared downstream proof lemmas without an import cycle.
The change record is `coord/changes/A2-tower-open-beta-import-cycle.md`.
The original sources of StrictTowerOrdinaryProperOpenArrows, ProperOpenAlphaPasting,
and TowerMateEvaluationScalars are copied unchanged only to rebuild their artifacts
against this import repair. Their current holders are S9, V2, and X2, respectively;
the import-only repair belongs to Y3.

## Proved and sorry left

Four of the five original holes are proved directly from the declared dependencies:
`AlgebraicGeometry.ProEtale.StrictTower.alpha_cartesian`,
`AlgebraicGeometry.ProEtale.StrictTower.alpha_vertical`,
`AlgebraicGeometry.ProEtale.StrictTower.alpha_horizontal`, and
`AlgebraicGeometry.ProEtale.StrictTower.alpha_baseChange`.

The fifth, `AlgebraicGeometry.ProEtale.StrictTower.gamma_evaluation`, is a decomposition:
the combination of evaluation, the origin isomorphism and finite transport is proved,
while the following strictly smaller coefficient-realization square remains:
`AlgebraicGeometry.ProEtale.StrictTower.singleLevelFiniteProperOpenTransport`, in
`Sheaf.AlgebraicGeometry.SingleLevelFiniteProperOpenTransport`, node
`lem-cbc-single-level-finite-proper-open-transport`.
It has no strict tower, evaluation index or chosen etale-origin witness. The item has
zero remaining sorries; one new named theorem has one sorry. Net change is four holes.
No existing holes in imported modules or unchanged consumer copies are counted as new.

Validation: the final calculus file compiles cleanly via `lcompile.py` in 36.8 seconds.
The complete sandbox run compiled beta normalization, all three unchanged consumers,
and the new statement module before the last calculus normalization fix. The final
calculus compile uses those rebuilt dependencies. The delivery tool runs its own
consumer, signature, node and independent-reader checks.

## No longer needed

Remove `public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` from
`TowerOpenBetaNormalization`: none of its declarations uses calculus declarations.
This is an import-cycle repair, not withdrawal of a mathematical node.
The parent now reaches finite site transport and etale clopen normalization through the
new single-level realization node, rather than directly. Both remain needed there.
The new statement module does not import `FiniteClopenMateSiteTransport`: that theorem
is recorded in its future proof dependencies, and is not used by the placeholder body.
No mathematical module or DAG node is withdrawn; pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The declared proof dependencies form a Lean import cycle through the redundant beta
normalization import described above. The beta node itself has no calculus dependency.
The finite site-transport theorem is stated for fixed-ring sheaves; the evaluated
single-level arrow is stated for modules over a constant ring sheaf. Their normalized
coefficient-realization square is additional glue, isolated in the new node. It is
not the parent statement under another name: evaluation and origin transport remain
in the proved parent argument.

Edge cases of the retained lemma were checked mathematically: the zero object and
empty schemes give zero maps; cartesian squares give the specified beta mate; an
identity proper map gives the clopen refinement projection; scalar maps need not be
flat. Every comparison is the one fixed by sheafification-unit sections and adjunction
units, so the equation asserts equality of maps, not only invertibility.

The current blueprint `latest` points to `main-20261023-1620`; its current
`thm-cbc-complete-proetale` proof no longer has the final comparison-compatibility
sentence named by the old DAG provenance. This delivery preserves the assigned Lean
statements and the existing unit route and cites the actual Stacks normalization
arguments for the additional coefficient-realization lemma.

The new child has no dependency path back to the parent. A full closure walk
encountered an existing shared-DAG cycle, left untouched: relative projective
functoriality (`prop-nagata-relative-proj-functoriality`) to relative Proj existence,
Proj affine restriction, affine Proj scalar extension, and back to functoriality.

The launcher reset the reference clock during provider/pause recovery: the original
`.budget` start was 1792758213.0978527 (the A2 claim is dated 12:23:27 UTC), while on
resume it was 1792768722.3701437, with budget 7200 and session 86400 unchanged.
These files were not edited by the worker; the original work and sandbox were retained.

## New nodes

`lem-cbc-single-level-finite-proper-open-transport` states the coefficient-realization
square between the normalized finite etale comparison and the single-level clopen
mate. It records the sheafification-unit, clopen projection, exact localization and
proper-adjunction transpose argument, using the existing beta, scalar and site
normalization nodes. Mathlib semantic, type/name and source searches find only generic
scalar-restriction and mate lemmas; the latest blueprint search found no duplicate.
The node has one public theorem in its own new module. The import repair is recorded
in `coord/changes/A2-tower-open-beta-import-cycle.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization` (holder Y3): remove only the
original line 11, `public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`.
The unchanged source graph rejects the planned parent import:

```text
NO: Sheaf.AlgebraicGeometry.ProperOpenAlphaPasting already reaches
Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus; importing it from
Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus closes a cycle
```

This is the `tools/import_direction.py may` diagnostic; there is no independent
original theorem type error claimed. The cycle goes through the ordinary-arrow and
beta-normalization modules. Dropping that unused import is the complete adaptation.
All existing beta declarations and the three consumer source files are unchanged.

## Forced adaptations

### Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization
Only imports removed (Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus), e.g. to break an import cycle; nothing else changed. CODEX verifies that the removal is needed.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
