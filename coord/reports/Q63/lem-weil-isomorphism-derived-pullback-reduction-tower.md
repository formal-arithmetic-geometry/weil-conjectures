## Worker report

The returned head 43baf5f8cdcd contained a stage-1 split with no Lean binding. The
reviewer's report replacement used an unsupported fix path. This delivery repairs
both report headings and supplies the missing stage-2 module
`Sheaf.Paper.IsomorphismReductionTower`, with main declaration
`WeilConjectures.isomorphismReductionTower`. It keeps the item's mathematical
statement and ten proof steps unchanged. Every postponed proof is `sorry`; every
definition has actual data or uses a uniqueness characterization.

Hypothesis and clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`. Finite extension E/Q_l:
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The coefficient nodes supply the canonical chosen integers and uniformizer.
- Scheme isomorphism: `{X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]`.
  Invertibility of ell is explicit at every residue field of X and Y.
- Small sites: `ProEt.topology`; the recorded `isoSectionwiseInverseImage`
  is inverse image under its canonical sectionwise identification by
  `proEtaleIsoPostcompose`. Site objects have size t+1, arrows size t;
  coefficient and module size is max u (t+1), with no universe equation imposed.
- Completed rings: `completedIntegralCoefficientSheafUnrestricted l E W`.
  `isoReductionCompletedMap_existsUnique` specifies the completed coefficient
  isomorphism by ALL finite projections and `isoSectionwiseConstantMap`.
  Its unique characterization is precisely inverse-image limit comparison
  followed by the limit of the constant comparisons, rather than an arbitrary map.
- Inverse image F: `isoReductionIntegralInverse` is the recorded sectionwise
  module inverse image with action transported by the inverse coefficient map.
  `isoReductionFiniteInverse` uses the constant finite-ring coefficient map.
- K-flat and flat terms: `IsoReductionFlatComplex l E Y P` is exactly
  `IsKFlatIndependentCoefficients P` AND `∀ i, IsFlatOnSite (P.X i)`.
- Positive levels: Lean n denotes paper exponent n+1, through
  `Padic.coefficientExtensionRing l E (n+1)`. Every positive level occurs.
- P_n: `unrestrictedTowerFiniteComplex`, the termwise published
  `scalarReductionExtension` along the actual completion projection.
  Quotient and transition arrows are `unrestrictedTowerUnit` and
  `unrestrictedTowerTransition`, uniquely normalized on sheafified tensors.
- Beta: the existential family gives an isomorphism of complexes of finite
  coefficient modules, for every P satisfying exactly the flat/K-flat conditions
  and every positive level. Its first conjunct evaluates beta on every local
  pure tensor, sending the coefficient through the canonical constant comparison
  and leaving the relabelled module section unchanged. This characterizes the
  stated tensor comparison followed by coefficient transport.
- The second conjunct is the quotient-map equation on every section, every site
  object and every degree. The third is the transition-map equation on EVERY
  section of the level n+1 reduction. The maps are compared after restriction
  of scalars through their actual underlying sections. Equality sectionwise is
  equality of these module chain maps, so no coefficient action is forgotten.
- The fourth conjunct is chain-map naturality as an equality of finite-coefficient
  complex morphisms, for arbitrary chain maps between the permitted complexes.
- The final conjunct quantifies two quasi-isomorphisms q,q' to arbitrary K and
  exactly the stated K-flatness of F(P),F(P'). It compares the canonical
  `unrestrictedTowerFiniteComparison` on both schemes, in the finite-coefficient
  derived category on X. `isoReductionImageComparison` applies the exact derived
  inverse image and conjugates only by its canonical localization factorization.
  `isoReductionMapQuasiIso` supplies the automatically preserved quasi-isomorphism;
  it does not add this as an extra hypothesis.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the coefficient definitions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  reexported by the recorded isomorphism interface.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `isoSectionwiseInverseImage_equivalence`,
  `isoSectionwiseConstantMap`, `isoSectionwiseModuleInverseImage` and exactness.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, with the existing unrestricted
  completed sheaf, finite quotient system and projections reexported unchanged.
- `Sheaf.Algebra.Homology.KFlat`: `IsKFlatIndependentCoefficients` and its
  resolution predicate; `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `IsFlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` supplies the
  same sheafified tensor functors and is imported through the tensor dependencies.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionExtension`, `scalarReductionDerivedExtension`,
  `scalarReductionCounit`, `scalarReductionRestriction`.
- Dependency repairs below provide the recorded augmented tower and its canonical
  comparisons without an irrelevant finite-field parameter.
- `Sheaf.Paper.PurInverseImageTensorHom`: `inverseImage_tensor_hom_iso` is the
  generic tensor comparison used by the proof; its specialization is normalized
  by the displayed pure-tensor equation, not by another tensor definition.

Edge cases checked: identity isomorphism; empty schemes (no sections or points
are assumed to exist); zero complex and zero quotient objects; all positive
levels starting at exponent one; unbounded complexes (degree-zero coefficient
factor means no infinite totalization comparison is required); arbitrary chain
maps and two unrelated resolutions (no direct comparison map is assumed);
independent coefficient and scheme universes. No statement dispute or source
correction is needed.

Searches: `msearch.py leanfinder` with the inverse-image/reduction-tower statement
returned eight unrelated ring-map/affine-space results. `msearch.py loogle` with
`"mapHomologicalComplex", "NatIso"` returned the three generic natural-isomorphism
lifting declarations, which do not assert coefficient tower compatibility.
`msearch.py grep` for `reduction.*inverseImage|inverseImage.*reduction` in Algebra
found no exact statement. Direct rg searches in upstream WeilConjectures and
lean/Sheaf for the item id, reduction/inverse-image combinations and
`isoSectionwise` found only the generic inverse image, tensor, reduction and
four-corner constructions. The existing parent IsomorphismDerivedPullback concerns
agreement with completed derived pullback on constructible categories and omits
this node's chain-level tower equations and resolution comparisons; it is not an
exact match and is not imported (it is downstream of this construction).

## Dependency modules

`lem-weil-integral-reduction-tower-well-defined`: its recorded module requires a
`FiniteFieldDatum` D and l ≠ D.p even to form the comparisons. The consumer fixes
arbitrary schemes with ell invertible, not a finite-field datum. The dependency
repair `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted` states the
same augmented-tower invariance on the existing unrestricted completed coefficient
sheaf and scalar-extension functors, with independent universes. Its finite
comparison is the composite through the SAME universal derived scalar extension,
using its counit and inverse augmentation. Unit and transition maps are uniquely
determined by their pure-tensor formulas. The repair changes only this node's
`lean` record and keeps every original mathematical field unchanged.

`def-weil-integral-reduction-tower`: its recorded tower also requires that
irrelevant auxiliary finite-field datum. The dependency repair
`Sheaf.Paper.IntegralReductionTowerCanonical` defines the same inverse sequence
of localized termwise reductions, its canonical maps from K, and their cone,
using the unrestricted comparison interface above. The existing coefficient
sheaves, projections and tensor operations are unchanged. Its node changes only
in `lean`. Both repairs include `lean.note` explaining the unusable old interface.

## Repair validation

The reviewer replacement is now incorporated in sandbox `report.md`, the path
accepted by deliver2.py; it has the exact `## Worker report` heading. There are
no nested reviewer fix paths in the delivery. The main node now has an actual
Lean module and binding, repairing the dry-run rejection of the original
stage-1-only packet. The general `GrothendieckTopology.hasSheafify_of_essentiallySmall` instance is
disabled only for the affected elaboration commands using scoped `attribute ... in`.
This avoids its successor-universe inference; the published independent-universe
sheafification supplies the same canonical category. No instance is removed from
the exported environment, and no new universe equality is assumed.

All three delivered modules passed `scompile.py` with no errors or warnings.
The item also passed both sandbox and module-path checks. The first dry run found
truncated JSON signatures at named-argument assignments and an extra noncomputable
prefix in the definition record; all three bindings now contain the complete
signature from the declaration keyword. Preflight is performed
through `deliver2.py --no-push`, with no global build or source-tree edits.

## Second reading by Q63

No second reading by a worker: the worker delivers directly and the maintainer's
independent review is the only review. The old head's independent review is not
represented as having reviewed the new Lean modules.
