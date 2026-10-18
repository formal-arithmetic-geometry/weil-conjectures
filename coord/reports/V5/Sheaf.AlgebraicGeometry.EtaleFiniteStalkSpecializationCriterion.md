## What changed

Proved `AlgebraicGeometry.Scheme.finiteLocallyConstant_of_finite_stalks_of_bijective_specialization`
with its original signature and all original public imports unchanged. Added four proved
helper modules, one per new node, and updated the parent node's proof route.

The proof lifts the finite stalk's operation table to sections, proves specialization
invariance directly on germs using strict-localization limit cones, finds an open inside
the invariant locus by generic points of finitely many components, and detects the
constant-sheaf adjunct as an isomorphism using localized geometric points. Taking one
neighbourhood for every ordinary point gives the required covering, including the empty
cover for an empty base. No existing definition or statement was changed, so no consumer
adaptation or change record is required. The blueprint unit's own route is preserved.

All five modules compile together through `lcompile.py --all` without errors or warnings.
Each new statement was searched using LeanSearch, Loogle and grep; the finite-stalk
presentation also used LeanFinder. Search results supply component lemmas, not an existing
one-line proof of any of the new statements.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finiteLocallyConstant_of_finite_stalks_of_bijective_specialization`.
Original holes: 1; closed: 1; added: 0; remaining in the five delivered modules: 0.
No obligation was split off with `sorry`.

The new proved declarations are:

- `AlgebraicGeometry.Scheme.exists_etale_finite_stalk_section`.
- `AlgebraicGeometry.Scheme.etale_section_germ_bijective_specializes_iff`.
- `AlgebraicGeometry.Scheme.exists_open_subset_of_specialization_invariant`.
- `AlgebraicGeometry.Scheme.exists_constant_iso_of_bijective_section_germs`.

The specialization calculation uses the existing named dependencies
`exists_geometricPoint_strictHenselization_lift` and
`existsUnique_etaleModuleStalkSpecialization`; their existing holes remain their own
items. Thus this is a proof from the declared dependency interfaces, not a claim that
the entire transitive import closure is already axiom-free.

## No longer needed

Removed these original proof-only imports from the item module:

- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`.
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`.
- `WeilConjectures.AlgebraicGeometry.GeometricStalkComparisonConstant`.
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `Sheaf.AlgebraicGeometry.GeometricSpecializationStrictLocalLift`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`.

The geometric-specialization lift is still genuinely used in the new specialization
helper, and strict-henselization definitions and structural maps remain required through
its statement imports. Those are relocated dependencies, not abandoned mathematics.

The route does not use the following original proof obligations, and removes their
parent-node tool approvals:

- `lem-weil-pbc-inverse-image-stalk-germ` / module
  `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`: no sheaf inverse image is used;
  pointed neighbourhoods themselves are pulled back and compared by limiting cones.
- `lem-weil-pbc-geometric-stalk-comparison-constant` / module
  `WeilConjectures.AlgebraicGeometry.GeometricStalkComparisonConstant`: the direct germ
  calculation also handles equal underlying points, so an independent stalk comparison
  and its constant-label compatibility are unnecessary.
- `lem-weil-pbc-constant-sheaf-geometric-stalk` / module
  `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`: its recorded statement
  is for abelian-group sheaves on a scheme. The proof instead uses Mathlib's general
  constant-presheaf stalk isomorphism and sheafification-stalk isomorphism directly on
  the localized site for module-valued sheaves.
- `def-weil-pbc-inverse-image` / module
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: unnecessary for this proof.
- `def-constructible-constant`: the `Sheaf.IsConstant` predicate is unnecessary; the
  conclusion and the adjunct use `constantSheaf` itself.

The old parent proof dependencies concerning finite-colimit representatives and
cofiltered pointed neighbourhoods are now dependencies of the proved presentation
helper. The ones concerning stalk detection are dependencies of the proved iso helper.
The affine shrinking step is supplied directly by the affine open cover of U; it does
not require `lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink` as a separate input
here. Some of these modules can still occur transitively through other dependencies;
the pruning above describes the actual proof route, not an assertion about their use
by unrelated targets.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan separated pullback naturality,
constant-label naturality, and independence of the geometric point. The limiting-cone
germ calculation proves the needed bijectivity equivalence directly and also covers
independence by applying it to a reflexive underlying specialization.

Edge cases checked in the proofs: zero ring and zero stalk in the finite operation
table; equal underlying points with different geometric fields in specialization;
quasi-sobriety without T0 in the topological helper; arbitrary (possibly infinite) M in
the iso helper; and the empty base via the point-indexed empty cover. No extra finite,
nonempty, separatedness, or Noetherian hypotheses were inserted into the helpers.

## New nodes

`lem-weil-pbc-etale-finite-stalk-local-presentation`:
`lean/Sheaf/AlgebraicGeometry/EtaleFiniteStalkLocalPresentation.lean` proves the finite
operation-table lifting argument from Mathlib's eventual equality and cofilteredness.

`lem-weil-pbc-etale-section-germ-specialization`:
`lean/Sheaf/AlgebraicGeometry/EtaleSectionGermSpecialization.lean` proves the direct germ
comparison. Private concrete cone constructions extend the affine spectrum cone,
construct the relative strict-localization map, and use the diagonal to fix its
projection to the chosen etale neighbourhood. Every private helper is proved.

`lem-weil-pbc-specialization-invariant-neighborhood`:
`lean/Sheaf/AlgebraicGeometry/EtaleSectionGermNoetherianNeighborhood.lean` proves the
purely topological component-removal step assuming only quasi-sobriety and finitely many
irreducible components.

`lem-weil-pbc-etale-section-germ-iso`:
`lean/Sheaf/AlgebraicGeometry/EtaleSectionGermIso.lean` proves the final constant-sheaf
trivialization with localized stalks and the universe-lifted conservative family.
All four nodes contain complete proof steps, source references, real search records,
and the exact Lean signatures. None introduces a deferred proof.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
