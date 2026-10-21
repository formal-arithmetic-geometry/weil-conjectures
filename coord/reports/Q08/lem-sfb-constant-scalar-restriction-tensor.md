## Worker report

This delivery states the constant-scalar restriction/tensor lemma in
`Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`. All theorem proofs are `sorry`.
Definitions and instance constructions use existing data; none contains `sorry`.
The node statement, statement dependencies and proof are unchanged.

### Hypotheses and objects

- The site is `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`.
  Its coefficient universe is `max u v`, retaining distinct site object and morphism
  universes. `B : Type (max u v)` has `[CommRing B]`.
- `ring J B` is the recorded `constantSheaf J CommRingCat` at `CommRingCat.of B`.
  `Modules J B` is the existing `SheafOfModules` over its underlying ring sheaf.
  `Fixed J B` is precisely `Sheaf J (ModuleCat B)`.
- Exact fixed-module sheafification is constructed by `fixedSheafify`, using the
  usual concrete small-site sheafification on the small model and
  `hasSheafifyEssentiallySmallSite`. It is not an added hypothesis.
  The existing independent-coefficient abelian sheafification is used on the ringed side.
- `restriction J B` uses `constantRingModuleRestriction`, preceded by restriction along
  the canonical `constantCommuteCompose` isomorphism. This identifies the constant
  commutative-ring sheaf with the RingCat presentation required by that recorded functor.
  Scalar actions and underlying maps are the actual constant-unit restriction.
- The ordinary ringed tensor is `cochainModulesMonoidal`; `fixedMonoidal` and
  `fixedSymmetric` are the recorded `sfbSheafTensorStructure`.
- `[HasDerivedCategory.{wR} (Modules J B)]` and
  `[HasDerivedCategory.{wB} (Fixed J B)]` specify the two localization presentations.
  Their universes are independent, with no equality imposed on them or on `u` and `v`.

### Every conclusion

- `additive`, `isEquivalence` and `exact` give the additive exact ordinary equivalence.
  The proof docstring of `isEquivalence` uses the recorded local action-extension inverse
  of `lem-cbc-constant-ring-module-sheaves`.
- `Ordinary.braided` is a `Functor.Braided` structure on that exact functor.
  Its parent monoidal structure includes inverse natural tensor comparisons, both
  unit comparisons, associativity and both unitor equations; braided compatibility is
  compatibility with the existing symmetries.
- `ringPure` and `fixedPure` are the actual sheafification images of local pure tensors,
  transported through the existing tensor/sheafification comparison isomorphisms.
  `Ordinary.tensor_hom` and `.tensor_inv` require both comparison directions to fix
  these local pure tensors for every object, section and pair of module sheaves.
- `fixedUnitIso` is the unit identification from `sfbSheafTensor_properties`.
  `fixedUnitScalar` is the image of the constant scalar through its inverse.
  `Ordinary.unit_hom` fixes the image of every scalar in the constant-ring
  sheafification unit. Invertibility also fixes the reverse unit map.
  `ordinary_exists` supplies this normalized coherent structure.
- `ordinary` selects the structure characterized by those generator equations.
  These equations determine the maps by the tensor and constant-module universal
  properties, so this is determined data rather than an arbitrary map chosen from
  an unspecified nonempty set. `restrictionBraided` exposes exactly this structure.
- `onComplexes` is the literal termwise extension. Its tensor comparison is the inverse
  of the existing `Functor.mapCochainComplexμIso`, using the normalized ordinary structure.
  Thus it is the natural signed direct-sum total comparison, with inverse,
  associativity and unit coherence supplied by the existing complex monoidal functor.
  `total_symmetry`, through `ComplexSymmetryCompatibility`, requires a braided structure
  whose underlying monoidal structure
  equals this existing total structure, explicitly fixing its Koszul compatibility.
- `flat_iff` uses the recorded `SheafOfModules.IsFlatOnSite` and `exactFunctor`
  for fixed-module right tensoring. Symmetry identifies left tensoring.
- `kflat_iff`, by specialization of the explicit `KFlatComparison` predicate, first compares the recorded `IsKFlatIndependentCoefficients` with
  acyclicity of total tensor against every acyclic fixed-module complex. Its other
  two conjuncts identify this condition with `IsKFlatForTotalTensor` in each category.
  That recorded definition quantifies over all quasi-isomorphisms and both total
  tensor arguments, retaining both sides of the node's equivalence.
- `onDerived` is exactly `restriction.mapDerivedCategory`; `derived_isEquivalence`
  states it is an equivalence of ordinary unbounded derived categories.
- `DerivedComparison` specializes `DerivedComparisonData` to the actual restriction
  and the recorded acyclic-test K-flat predicate. This is a subtype: its `.val`
  supplies the coherent inverse derived tensor and unit maps.
  Its `.property.1` is `derivedTensorCompatibility`, fixing the tensor map on every
  pair of K-flat representatives using the existing localization tensor maps,
  `mapDerivedCategoryFactors` and exactly `(Functor.mapCochainComplexμIso _ _ _).inv`.
  Its `.property.2.1` is `derivedSymmetryCompatibility`, the equation with the
  canonical descended Koszul braiding `DerivedMonoidal.braiding'` itself.
  Its `.property.2.2` is `derivedUnitCompatibility`, fixing the degree-zero
  regular-unit normalization through the same canonical localization maps.
  `derived_comparison` asserts existence of this normalized structure.
- `ringClosed`, `ringFlatResolutions`, `fixedFlatResolutions` and the Grothendieck
  instances supply the existing K-flat derived tensor construction without adding a
  flat-resolution hypothesis. Fixed-module flat resolutions are transported through
  the exact equivalence, as explained in the theorem's proof docstring.

### Dependency declarations used

The statement dependencies were read at their recorded declarations and docstrings:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  the item itself is stated for the associated arbitrary Grothendieck topology.
- `Sheaf.CategoryTheory.SheafTensor`: `sfbSheafTensorStructure`,
  `sfbSheafTensor_properties`, `sfbSheafTensor_comparison`,
  `sfbSheafTensor_monoidalPreadditive`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`,
  `constantCommuteCompose`; `Mathlib.CategoryTheory.Sites.Sheafification`:
  `toSheafify` and `hasSheafifyEssentiallySmallSite` (the latter from Sites.Equivalence).
- `Sheaf.CategoryTheory.ConstantRingModuleSheaves`:
  `constantRingModuleRestriction` and `constant_ring_module_sheaves`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, `cochainModulesSymmetric`, `cochainModulesPreadditive`,
  `cochainTensorLeftPreservesColimits`, `cochainTensorRightPreservesColimits`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  the existing total monoidal instance and `HomologicalComplex.tensorObj` implement it.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, `CategoryTheory.exactFunctor`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`:
  `CochainComplex.IsKFlatForTotalTensor`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`.

The size-convention dependency is a convention, not a replacement Lean object.
The proof-dependency imports retain the supplied bilinear sheafification extension,
module tensor universal property, braided sheaf generators, tensor/cone isomorphism,
cone acyclicity criterion, equivalence limit preservation and site-derived tensor
localization/extension interfaces. The proof docstrings explain the node's eight steps,
including local scalar extension, pure-tensor normalization, all total signs, the cone
criterion, and descent from flat-term K-flat resolutions to arbitrary K-flat representatives.
Additional existing construction interfaces are `Functor.mapCochainComplexμIso`,
`SheafOfModules.nonempty_monoidalClosed_independentCoefficients`,
`SheafOfModules.hasFunctorialFlatResolution_kfi`, and
`SheafOfModules.isGrothendieckAbelian_coefficientUniverse`.

### Edge cases and searches

The zero ring is allowed: no nontriviality or faithful nonzero section is assumed.
The empty site and empty covering/sum cases retain their usual sheaf and coproduct
constructions; no object or section is chosen. There is no terminal-object or
points hypothesis. All complexes are unbounded `CochainComplex _ ℤ`; tensors use
coproducts over all pairs with the required total degree, without a boundedness or
finite-support assumption on the complex. Separate `u`, `v`, `wR`, `wB` retain the
size edge cases. No statement dispute or source correction was found.

Searches through the prescribed `msearch.py Q08 <item>`:

- `leanfinder`: "Restriction from modules over a constant ring sheaf preserves tensor
  and K flat total complexes" returned eight generic restriction/flatness results,
  without the complete comparison lemma.
- `loogle`: `SheafOfModules, "tensor"` returned no hits.
- `grep`: `constant.*[Rr]estrict.*[Tt]ensor|[Tt]ensor.*constant.*[Ee]quiv`
  returned no Mathlib match.
- `rg` in the named upstream `WeilConjectures` and project `Sheaf` trees for the
  item id and constant restriction/tensor names found the existing scalar restriction,
  its equivalence and consumers, but no complete statement of this node. These
  existing interfaces are reused rather than redefined.

Local source checked: `sites-modules.tex`, Tag 0GMW,
`lemma-sheafification-tensor`, its bilinear-map hint and tensor universal property,
with the exact node's recorded eight-step proof and the listed dependency interfaces.

## Second reading by Q08

I reread the item and module together, checking each clause above, the directions of
both ordinary tensor maps, the unit normalization, the localization square and all
universes. This is a worker self-check, not an independent second worker review:
the dispatcher explicitly prohibited starting another agent and specified independent
maintainer review of the delivery. No independent reader is claimed.
The mathematical statement and dependency records required no changes.

## Returned-delivery timeout repair

The initial required dry run of the retained packet reproduced the return:
`Sheaf.Stage2.Sandbox0` timed out after 60 seconds, and the wrapper's current-server
confirmation timed out too. The full-file profile reached the signed-total comparison
and showed repeated synthesis of the monoidal structure on the complex functor.

The repair shares the existing abelian, additive and zero-morphism structures
through `ringAbelian`, `fixedAbelian`, `ringPreadditive`, `fixedPreadditive`,
`ringZeroMorphisms` and `fixedZeroMorphisms`. Each is the original structure or
its canonical parent, with no new mathematical data.

The signed-total tensorator is reused directly from
`Functor.mapCochainComplexMonoidal`, whose `CoreMonoidal.toMonoidal` construction
uses exactly `Functor.mapCochainComplexμIso`. No redundant concrete isomorphism or
complex-instance alias is constructed. `ComplexSymmetryCompatibility` writes the
original equality of the braided structure's monoidal parent with this canonical
complex-functor monoidal structure; `total_symmetry` specializes it to restriction.
The ringed-site closedness instance moves earlier to supply the specialization.
No file is split to avoid the limit.

`KFlatComparison` writes out the original three equivalences over abstract
coefficient categories; `kflat_iff` specializes it to the recorded
independent-coefficient predicate. The acyclic test and both quasi-isomorphism
tests retain all their quantifiers and the same signed total tensor.

The derived tensor and unit squares are retained verbatim in
`derivedTensorCompatibility` and `derivedUnitCompatibility`.
`derivedSymmetryCompatibility` uses the components of
`DerivedMonoidal.braiding'` directly: these are definitionally the braiding fields
of the canonical `DerivedMonoidal.braidedCategory'` used before. This avoids
constructing and comparing the entire monoidal structure while retaining exactly
the same Koszul symmetry equation. No arbitrary braiding or additional hypothesis
is introduced. The two derived-category universes remain independent.
`DerivedComparisonData` is a subtype of monoidal structures satisfying these three
explicit predicates. It stores exactly the original record's data and laws,
without its expensive generated constructors and eliminators.

The ordinary tensorator, signed totals, localization comparisons, universes,
hypotheses and conclusions are preserved. No timeout limit or linter was disabled
or raised. No source-based statement correction or new DAG node is required.

The repair self-check reread the complete file and the node, including the equality
in `total_symmetry`, all three conjuncts of `KFlatComparison`, the localization
tensor square and the unit square. The generic helpers keep each monoidal structure
canonical; they do not quantify over a replacement structure in the item's conclusions.
Their parameters are supplied by the original constructions at specialization.
The node still differs from the current read clone only in `lean`.

## Validation

The final owning module passed `scompile.py` in both required forms: sandbox
44.7 seconds and library 34.8 seconds, within the unchanged 60-second limit.
There were no errors or warnings. The previous temporary-module success was not
treated as completion when its delivery dry run still timed out; this final source
removes the expensive redundant comparison constructions identified by profiling.
Every declaration and universe is explicitly bound; the ten theorem proofs remain
`sorry`, with their source and natural-language proof docstrings. Definitions and
instance constructions contain real existing data. There are no debug options,
new DAG nodes, statement changes, or edits outside the sandbox.

All statement and proof dependencies with a recorded module have their owning
imports. The final self-check verifies all three K-flat equivalences and all three
derived comparison laws, canonical tensor and braiding choices, and independent
site and localization universes.

The final packet is checked and delivered only through the prescribed `deliver2.py`
wrapper, including its server preflight and per-file compilation.
