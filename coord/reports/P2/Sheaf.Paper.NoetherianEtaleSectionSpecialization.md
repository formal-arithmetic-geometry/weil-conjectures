## What changed

Partial proof delivery of `Sheaf.Paper.NoetherianEtaleSectionSpecialization`.
All existing theorem statements, definitions, public imports and visibility are unchanged.
Three proved private helpers convert the existing smooth-duality interface to the exact
shifted locally trivial sheaf interface, assemble invertible coefficients from stalks,
and show the canonical section base-change map is an isomorphism.

`geometry` uses the source deformation smoothness, separatedness and fibre-square
APIs and finite-type Noetherian permanence. For the conormal comparison it applies
`WeilConjectures.PurityConventions.regularNormalBundle`. The supplied weak regular
sequence is regular because its ideal is proper: the affine open contains the section
point, which belongs to the kernel ideal sheaf support.

`lines_and_fibres` pulls the smooth dualizing line to both sections and applies smooth
base change at zero and one. Its cover is refined by points so each constant module
is identified with the coefficient ring using a geometric stalk.
`isIso_specialization` composes these isomorphisms.
`normalMap_condition` is the zero-fibre commutativity calculation.
`baseChange_geometry` uses the existing local extended-Rees pushout computation,
then pullback pasting, cancellation and extensionality for the specified normal map.

Added proof-only imports `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality`
and `WeilConjectures.ConstructibleSheaf.Pullback`. The former supplies the existing
source interfaces underlying the stated smooth-tensor and smooth-base-change nodes;
the latter supplies preservation of local constancy under inverse image.
The node proof and origin now record these implementations. The remaining plan and
its dependency union are retained because two clauses are still open.
Added proof-only import `Sheaf.Paper.PurityConventions` for the general conormal theorem.

Validation: the complete file compiled cleanly through lcompile.py after import pruning
(47.9 seconds). A further diagnostic compile passed in 32.0 seconds. Axiom inspection
of `normalMap_condition` and `baseChange_geometry` showed only `propext`,
`Classical.choice`, and `Quot.sound`. `lines_and_fibres` and
`isIso_specialization` still depend on existing upstream smooth-duality holes.
The resumed attempt also compiled before cleanup (18.4 seconds), and the final
cleanup compiled successfully in 16.0 seconds. An exploratory
internal hole in `existsUnique_normalized` was removed by restoring its original whole
proof `sorry`; the unused imports for that exploration were removed.
No downstream adaptation or signature repair is included.

Resumption check (2026-10-19): retained the earlier sandbox and compared it with the
current shared sources. Only proof bodies, private proved helpers, proof-only imports,
and the node's proof/proof_deps/proof_origin differ. The two remaining holes are still
the original whole theorem proofs; no additional holes or split-offs were introduced.

## Proved and sorry left

Closed 5 of the 7 original holes, with no holes added and no split-offs.
Names below are in `AlgebraicGeometry.Etale.NoetherianSectionSpecialization`.

- Proved `geometry` from the general regular normal-bundle theorem.
- Proved `lines_and_fibres` from the existing smooth-duality declarations.
- Proved `isIso_specialization` from `lines_and_fibres`.
- Proved `normalMap_condition`.
- Proved `baseChange_geometry`.

The 2 remaining original sorry declarations all belong to
`lem-pur-noetherian-etale-section-specialization`:

- `existsUnique_normalized`: the centered-chart comparison, normalization and
  connected-geometric-line uniqueness/gluing argument remain open.
- `baseChange_compatibility`: the canonical mate-pasting identities and their use
  with normalized uniqueness remain open.

The private helpers `section_line`, `invertible_exponent`, and `isIso_sectionMap`
are proved. No sorry occurs in a definition or new declaration.

## No longer needed

Removed the following redundant direct proof imports. Some remain available
transitively; this is not a claim that their entire modules leave the target closure.

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.CategoryTheory.Adjunction.Unique`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction`
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.Paper.RingedTopoiDerivedTensorPullback`
- `Mathlib.Topology.Connected.Basic`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural`
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`
- `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.RingTheory.Flat.Basic`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.Algebra.MvPolynomial.Basic`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`
- `Sheaf.AlgebraicGeometry.SmoothTensorDuality`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction`
- `WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`
- `WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness`

No complete DAG node or module is declared obsolete: the uncompleted normalization
and naturality clauses retain the original plan. In particular the local
chart, affine-space duality, connected-fibre and mate-pasting dependencies remain
needed by the open clauses, despite not being used directly by the five completed
proofs. Their dependency records are retained for subsequent workers.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The planned low-level Rees calculations and
smooth duality do not need to be rebuilt in this module: the source library already
provides the necessary Rees pushout and smooth-duality interfaces. The Lean proofs
reuse them and supply the actual interface conversions and pullback calculations.
The earlier attempt overlooked `regularNormalBundle` in `Sheaf.Paper.PurityConventions`:
it has no field-base hypothesis, and supplies precisely the general conormal assertion.
This delivery uses it, with the proof of properness needed to turn the weakly regular
sequence into a regular one. No new nodes or change records.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
