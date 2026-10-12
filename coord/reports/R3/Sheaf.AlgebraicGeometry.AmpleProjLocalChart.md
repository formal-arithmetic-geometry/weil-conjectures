## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_sectionRing_proj_affine_charts`
in `Sheaf.AlgebraicGeometry.AmpleProjLocalChart` from the existing canonical-map theorem
and a new, strictly smaller ring-localization comparison theorem. The original signature,
visibility, definitions, and unit route are unchanged.

The Lean proof retains the canonical map and fraction formula, derives compactness and
quasi-separatedness from ampleness, transfers affineness along the inverse-image equality,
and applies the new comparison to `Proj.awayToSection ≫ f.app`. Mathlib's Proj chart ring
isomorphism lets us cancel `awayToSection`; the restriction formula transfers the resulting
ring isomorphism to `appTop`. Mathlib's affine global-sections criterion then proves the
restricted scheme map is an isomorphism. These combining steps compile without holes.

Added the proof-only imports `Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective`
and `Mathlib.AlgebraicGeometry.Morphisms.IsIso`. Updated the item's DAG proof route.
The new comparison theorem records the remaining Veronese, cohomology, and fraction
presentation identifications, with a full natural-language proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_sectionRing_proj_affine_charts`
(node `lem-sc-ample-proj-local-chart`). No sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.sectionRing_localization_bijective`
(node `lem-sc-section-ring-localization-bijective`), in its own module
`Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective`.
This is a decomposition: one upper hole closed, one lower hole added; net zero holes.
The new statement concerns a ring map on an arbitrary quasi-compact quasi-separated
scheme and assumes neither ampleness, affineness, a cover, nor a morphism to Proj.
It is the localization step of the argument, not the original conclusion renamed.
Existing dependency holes, including `invertS_cohomology`, were not modified.

Edge cases checked mathematically: the empty nonvanishing open has zero section ring,
and localization at a nilpotent section is also zero. Degree zero is excluded by `hd`.
No data is defined by choosing a witness of an unproved existence theorem.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.InvertSCOhomology` and replaced
its direct dependency at this node with `lem-sc-section-ring-localization-bijective`.
The cohomology theorem remains a proof dependency and import of the new comparison,
so it is not claimed as pruned from the targets' transitive closure.
No other node or module is pruned; the remaining original imports are used.

## Where the brief, the DAG or earlier work was wrong

The plan's phrase "elementary reindexing" conceals Lean identifications among tensor
powers of tensor powers, structure-module tensor factors, degree-zero cohomology, the
additive fraction presentation, and homogeneous localization. The new theorem isolates
this precise bridge; the existing `invertS_cohomology` does not directly supply the ring
map comparison in the target's encoding. No statement has been disputed or weakened.

LeanSearch was unavailable (HTTP Internal Server Error); LeanFinder, Loogle and local
search were used. The cited Stacks source files are absent in this clone; the authoritative
online Tags 01Q1 and 09MR were read instead.

## New nodes

`lem-sc-section-ring-localization-bijective` states bijectivity of a ring map out of the
homogeneous localization under the canonical restriction-and-division formula. Its source
is Stacks 01PW(2), used in 01Q1, or equivalently the degree-zero case of 09MR. The node
records the remaining tensor/Veronese and fraction-presentation bridge, the existing
cohomology dependency, and uniqueness by the freely generating section. Its Lean module
is `lean/Sheaf/AlgebraicGeometry/SectionRingLocalizationBijective.lean`.
No interface changes, forced adaptations, or change records.

## Second reading by R3

1. Compared the delivered `AmpleProjLocalChart.lean` with the repository version. The existing theorem signature and all existing declaration statements are byte-for-byte unchanged; only proof imports and proof terms changed. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py`; both compile without errors or warnings. The target theorem has no `sorry`; the sole remaining `sorry` is the named split theorem `sectionRing_localization_bijective`, with no sorry in any definition or forbidden axiom construct. Verdict: pass.

3. Read the split statement and its docstring and checked it on the empty open and nilpotent-section cases. It is a genuine localization comparison strictly below the target, with the required node and source, and is not a duplicate of an existing declaration. Verdict: pass.

4. The proof follows the unit route: canonical map and restriction formula, ampleness compactness/separatedness, localization comparison, Proj chart isomorphism, and affine global-sections criterion. The proof-only cohomology import was removed from the target module and retained only behind the split theorem. Verdict: pass.

5. The target node's proof, proof dependencies, and proof origin match the Lean proof, and the new node records its module, declaration, source, route, and split status. Verdict: pass.

Changed during second reading: no mathematical or interface changes; added this review record only. The dry-run preflight is expected to classify the delivery as CODEX because it adds the required split node and module.
