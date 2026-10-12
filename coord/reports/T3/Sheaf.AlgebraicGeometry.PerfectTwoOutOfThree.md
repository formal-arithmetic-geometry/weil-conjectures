## What changed

Kept the signature and docstring of `AlgebraicGeometry.Scheme.isPerfect_two_out_of_three`
unchanged. Its proof now obtains common affine models, constructs a strictly perfect cone
model, and uses the definition of perfectness pointwise. The other two cases are actual
Lean proofs using rotation and inverse rotation. Private proved helpers establish
isomorphism invariance and invariance under every integer shift directly from local models.

Added three modules and their matching nodes:

- `Sheaf.AlgebraicGeometry.PerfectCommonAffineModels`: proved common affine refinement,
  termwise restriction of finite-free retracts, and the derived restriction comparison.
- `Sheaf.AlgebraicGeometry.PerfectAffineConeModel`: proved the bounded mapping-cone
  construction, the termwise finite-free retract equation, finite-basis reindexing, and
  triangle comparison from one chain-map representation lemma.
- `Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`: the remaining named step,
  representing a derived arrow between two strictly perfect complexes on an affine open
  by an actual chain map. Its complete proof in words follows the affine derived
  equivalence and Mathlib's projective-source representation API.

All four files compiled together without errors or warnings with `lcompile.py --all`.
The intermediate statements include arbitrary schemes and the original localization
universe, with no quasi-separatedness or Noetherian hypothesis. Common intersections
are refined to affine opens instead of assumed affine. Bounds, shifts of either sign,
zero-rank free modules, zero complexes and empty opens are covered by the same formulas.
No definitions, existing signatures, existing visibility, or other modules were changed.

## Proved and sorry left

Closed the sole hole in the item:
`AlgebraicGeometry.Scheme.isPerfect_two_out_of_three`
(node `lem-pc-perfect-two-out-of-three`). Its proof combines local models, cone closure,
and shift/rotation arguments, without any remaining hole in that module.

Also proved `AlgebraicGeometry.Scheme.perfect_common_affine_models`
(node `lem-pc-perfect-common-affine-models`) and
`AlgebraicGeometry.Scheme.perfect_affine_cone_model`
(node `lem-pc-perfect-affine-cone-model`), with all private helpers proved.

Added exactly one hole:
`AlgebraicGeometry.Scheme.perfect_affine_map_representative`
(node `lem-pc-perfect-affine-map-representative`), in its own new module.
Its entire proof is `by sorry`. This is a decomposition, not an unconditional proof of
perfect two out of three: one upper hole closed and one lower hole added. The lower
statement concerns only chain-map representation; it contains neither triangle closure,
local cover refinement, cone boundedness/retracts, nor the rotation cases. Existing holes
in imported modules remain their existing items.

## No longer needed

Removed the item's proof imports of
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` and
`Sheaf.Paper.AffineProjectiveComplexDerivedHom`, replacing them with the common-model
and affine-cone modules. The affine equivalence remains needed transitively in the new
arrow-representation module; it is relocated, not pruned.

The proof no longer needs node `lem-sc-affine-projective-complex-derived-hom` or module
`Sheaf.Paper.AffineProjectiveComplexDerivedHom` along this route. Replace its planned
chain-map-representation use with the existing Mathlib node
`lem-pc-ring-derived-map-representative`, using
`Mathlib.Algebra.Homology.DerivedCategory.KProjective`. This avoids the one-point-site
internal-Hom machinery entirely. Its exclusive descendants can be pruned by the queue;
modules still reached by other targets are not claimed globally unnecessary.

Also removed redundant direct proof imports from the new modules:
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` from
`PerfectCommonAffineModels` (already publicly supplied through `PerfectComplex` ->
`DerivedCategory` -> `DerivedHomMayerVietoris`), and
`Mathlib.CategoryTheory.Triangulated.Functor` from `PerfectAffineConeModel`
(already supplied through the derived-category imports). These are redundant edges;
neither module is globally pruned by this removal.

The original nodes `def-pc-perfect-complex`, `def-weil-abstract-derived-category`,
`def-weil-triangulated-category`, `lem-pc-affine-qcoh-derived-equivalence` and
`lem-sf-triangle-morphism-iso` are retained directly or transitively. No unit realization
or unit proof step was bypassed; the unit's realization lists do not identify this
node as a unit statement or unit step.

## Where the brief, the DAG or earlier work was wrong

The planned use of `lem-sc-affine-projective-complex-derived-hom` does not directly fit:
its actual Lean signature is an internal-Hom comparison on the one-point sheaf site,
not surjectivity of the map from chain maps of `ModuleCat` complexes to derived arrows.
Mathlib's `CochainComplex.IsKProjective.Qh_map_bijective` and the existing node
`lem-pc-ring-derived-map-representative` provide the appropriate representation API.
No statement was disputed or weakened.

The local affine representation and open-site transport were described in the original
plan but not exposed by its cited signatures. The common-refinement and cone portions
are now fully implemented; only the specific affine arrow representation is isolated.
The original declaration docstring is retained verbatim, while its DAG proof describes
the actual implementation and replaces the unsuitable internal-Hom dependency.

The referenced local Stacks TeX files are absent on this machine. Read the official
Stacks pages for Tags 08CR and 08EB. Tag 08CR's second proof is the local chain-map/cone
argument; the affine refinement here makes its chain-map step global on an affine open.
LeanSearch returned service errors, recorded honestly as unavailable; LeanFinder,
Loogle, logged source grep, and direct searches of both library roots were used.

## New nodes

`lem-pc-perfect-common-affine-models` records the proved common affine refinement for
any two perfect objects at a point. Its module constructs restricted complexes and
finite-free splittings and composes exact derived restriction comparisons.

`lem-pc-perfect-affine-cone-model` records the proved strictly perfect model of the
third term after affine restriction. Its module constructs the actual mapping cone
and its bounds and retracts, then compares distinguished triangles.

`lem-pc-perfect-affine-map-representative` records the one remaining hole: representation
of a derived arrow by a chain map on an affine open. Its node and docstring describe
termwise section complexes, counit isomorphisms, lifting through the affine equivalence,
and the projective-source chain-map API. No change record is required: every existing
interface is identical and only private proof imports changed.

## Second reading by T3

1. **Interfaces: pass.** Read all four delivered modules and diffed the item against
   the repository version. The only existing public declaration is
   `AlgebraicGeometry.Scheme.isPerfect_two_out_of_three`; its signature and original
   docstring are byte for byte unchanged. Both derived-category instance hypotheses,
   arbitrary scheme and localization universes, distinguished-triangle hypothesis,
   and all three implications remain. The only existing-node changes are `proof`,
   `proof_deps`, and `proof_origin`. There are no definition changes or forced adaptations.
2. **Proof and axioms: pass with the declared hole.** All four modules compiled locally
   in import order. A scratch module printed axioms for all four public theorems:
   common affine models uses only `propext`, `Classical.choice`, `Quot.sound`;
   the item, cone model, and map representative additionally use `sorryAx`.
   Source inspection found exactly one `sorry`, the entire proof of
   `perfect_affine_map_representative`, and no forbidden declaration or attribute.
   There are no new definitions and no data selected from an unproved existence
   theorem. The final delivery tool also probes every declaration, including helpers.
3. **Split statements: pass.** The sole remaining hole is strictly a chain-map
   representation step, not a renamed two-out-of-three theorem. Finite-free retracts
   on an affine open are quasi-coherent, and their section modules are finite projective.
   The termwise counits identify the complexes themselves, not just their cohomology.
   Full faithfulness of the affine derived equivalence and K-projectivity of the bounded
   source then give the asserted chain-map equality. Checked empty affine opens,
   zero complexes, rank-zero retracts, negative bounds, and shifts in both directions:
   none require a new hypothesis. This is substantially narrower than the item.
   Repeated searches with different wording: LeanFinder query “Fullness of localization
   on bounded complexes of finite locally free modules over affine schemes” found no
   exact result; Loogle confirmed `CochainComplex.IsKProjective.Qh_map_bijective`;
   logged grep checked `IsStrictlyPerfect|Qh_map_bijective|exists_iso_of_arrow_iso`.
   Direct searches of both library roots and inspection of the affine derived-Hom
   evaluation and projective-complex internal-Hom modules found no duplicate.
   No quick proof of the remaining localized-site transport step was available.
4. **Route and pruning: pass after import cleanup.** Read `IsPerfect` and
   `IsStrictlyPerfect`, the restriction comparisons, cone term isomorphism and
   retract equation, conjugated arrow equality, and rotation/shift cancellation.
   The proof constructs the cone and common refinement explicitly. The cone bounds
   are `[min(aA-1,aB), max(bA-1,bB)]`; shifted bounds are `[a-n,b-n]`.
   `dag/units/sk-thm-picard-duality.json` has empty realization lists, and no unit
   realization anywhere names the item; the unit's route is unchanged. Every old
   proof dependency is accounted for under No longer needed: the internal-Hom node
   is replaced, while affine equivalence, triangle-isomorphism, and the definitions
   remain transitively used. Removed two redundant proof imports as listed above;
   retained public imports only where signatures need them, and the remaining hole's
   planned proof imports. The result remains a decomposition: one existing hole
   closed, one new hole added, net zero holes removed before any closure pruning.
5. **DAG: pass.** Read all four node records, compared the existing node's changed
   fields, and checked the new records' ids, chapter/unit, source, searches, creation,
   blueprint ancestry and Lean signatures. Each `proof_deps` equals the union of its
   step `uses`. The Mayer–Vietoris node also records the exact-restriction helper
   declarations actually used; its long exact sequence theorem is not being applied.
   The cone comparison uses Mathlib's `exists_iso_of_arrow_iso`, the combined TR3 and
   triangle-morphism-isomorphism argument recorded by its dependencies. The affine
   representative plan uses the existing ring representation node, not the unsuitable
   internal-Hom node. Verified the source route against the official Stacks pages:
   [Tag 08CR](https://stacks.math.columbia.edu/tag/08CR) gives local representatives
   and a strictly perfect cone; [Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
   supplies the affine derived equivalence used in the remaining lemma's proof.

Second reading changed only the two redundant proof imports and this report. No proof,
statement, definition, or node needed repair. The remaining chain-map lemma is accepted
as a true, sourced, strictly smaller open step, not as an unconditional proof of the item.
