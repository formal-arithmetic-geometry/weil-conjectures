## Worker report

Module: `Sheaf.Paper.RingIsoQuotientSystemTransport`. Main statement:
`SheafOfModules.QuotientIsoTransport.ringIsoQuotientSystemTransport`.
The proof is `sorry`, as required for stage 2. No mathematical theorem is proved.
The remaining declarations are transparent abbreviations, a composite of existing
canonical localization isomorphisms, and structures spelling out this node's clauses.
No new ring, module category, strict system category, tensor product or derived
localization is defined. There are no new DAG nodes or dependency-module repairs.
The item's mathematical statement and proof are unchanged.

### Hypotheses and objects

- A small site is represented by `{C : Type u} [Category.{v} C]` and
  `{J : GrothendieckTopology C}`. The site-to-Grothendieck-topology convention is
  the one of `CategoryTheory.Precoverage.IsSiteForCoverings` in the recorded
  `Sheaf.CategoryTheory.SiteCoveringAxioms`. The assumptions
  `[EssentiallySmall.{w} C]`, `J.HasSheafCompose`,
  `J.WEqualsLocallyBijective AddCommGrpCat.{w}`, and
  `HasSheafify J AddCommGrpCat.{w}` express the existing module/sheafification
  size and API conditions. Site objects, site morphisms and coefficients have
  the independent universes `u`, `v`, `w`; no equality is imposed on them.
- The ring systems are `(R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})`.
  Index `n` denotes the positive level `n+1`, including the first level at `0`.
  This is exactly the reindexing of `Functor.ofOpSequence`; all composite
  transition maps are `B.map (homOfLE h).op`.
- Compatible ring isomorphisms are `(a : R ≅ S)`. Naturality gives precisely
  the commuting coefficient squares; the inverse squares follow automatically.
- `(c : Cone R) (hc : IsLimit c)` and `(d : Cone S) (hd : IsLimit d)` specify
  actual sheaf limits, not limits of unrelated sections. The conclusion provides
  `e : c.pt ≅ d.pt` and the projection equation
  `e.hom ≫ d.π.app (op n) = c.π.app (op n) ≫ (a.app (op n)).hom`.
  This specifies the induced isomorphism by limit uniqueness.
- `Modules R` is merely `ringedSiteModules` applied to the recorded forgetful
  ring sheaf `derivedChangeRingIndependentCoefficients J R`.
  `transport a` is literally `SheafOfModules.restrictScalars` along `a.inv`.
- `(A : SystemScalarAssignment (J := J))` parametrizes the already existing
  normalized universal scalar models, for every coefficient map. It does not
  posit an arbitrary tensor functor or comparison: each model's object and map
  functions are fixed as the sheafified change of rings, its ordinary adjunction
  is normalized by pure tensors, and its derived adjunction by the cochain
  universal counit. `nonempty_systemScalarModel` supplies these for every map.
  The theorem holds for every such presentation, so it is independent of choices.
- The existing `StrictRingSystem R` is used verbatim. Its `level`, `transition`,
  `identity`, `compose` and `Hom.comm` give exactly the node's semilinear systems
  and componentwise morphisms; its abelian and evaluation instances are retained.
  The landed node `def-pur-system-level-left-extension-basic` is added to
  `stmt_deps` because these notions are needed to state this item. Its existing
  module also supplies `SystemScalarAssignment` and tensor coherence interfaces.

### Conclusions, clause by clause

The conclusion `Nonempty (CoherentTransport R S a c d e A)` asserts existence of
all the specified coherent comparisons together, not a choice of unrelated maps.

- `equivalence` is an equivalence of the actual strict system categories.
  `object_level` fixes its level object to restriction along the inverse
  coefficient isomorphism. `transition_unchanged` and `map_unchanged` say on
  every section that the transitions and componentwise maps are unchanged.
  `additive`, `limits`, and `colimits` express additive exactness.
- `derivedEquivalence` is an equivalence between the ordinary unbounded
  `DerivedCategory (StrictRingSystem R)` and its S counterpart. `derived_eq`
  fixes its functor to the existing exact `mapDerivedCategory`; `localization`
  and `localization_normalized` fix the comparison to
  `mapDerivedCategoryFactors`. This is stronger data than just evaluated
  families, and is precisely the node's specified system localization.
- `level` and `level_sections` fix the ordinary evaluation comparison on the
  unchanged sections. `derivedLevel` and `derivedLevel_rep` fix the derived
  comparison by its equation on localized cochain complexes.
- The helper `Reduction B c A` specifies the ordinary whole-system reduction
  and natural evaluation isomorphisms to the actual scalar-extension functors
  for the cone projections. Its `transition` fixes every horizontal map on
  local tensors to the ring transition. Its `derived`, `counit`, `universal`,
  and `pointwise` specify the everywhere-defined left derived reduction into
  `DerivedCategory (StrictRingSystem B)`. Its `computes` clause applies to
  exactly flat-term independent K-flat complexes. `derivedEvaluation` and
  `evaluation_rep` identify its evaluated reductions by the universal counit.
- `reductionR` and `reductionS` supply these reductions for both limit cones.
  `reduction` is a natural isomorphism of whole strict systems.
  `reduction_pure` spells out at every level the formula sending the sheafified
  generator `p tensor r` to `p tensor alpha_n(r)`. The library writes the scalar
  first in `systemModelTmul`; this is the same generator with that convention.
  The equality is on local generators after the canonical sheafification map,
  so it specifies the map even when sections of a tensor sheaf are only locally
  generated by pure tensors. Because `reduction` is a morphism in the actual
  strict-system category, it commutes with every transition, not just successive
  ones. Evaluating at `r = 1`, together with the normalized scalar unit, gives
  the required augmentation `p ↦ p tensor 1`. Applying this ordinary natural
  isomorphism termwise gives the asserted strict chain-system isomorphisms for
  all flat-term K-flat P (in fact the ordinary comparison holds for all P).
- `derivedReduction` is a natural isomorphism of the whole derived-system
  reduction functors. `derivedReduction_rep` identifies it with the ordinary
  comparison and universal counits on cochain representatives. The universal
  left-derived properties and this equation give independence of resolutions.
- `ScalarSquare` packages the canonical comparisons for one commuting ring
  square: exact scalar restriction with identity sections (`restriction` and
  `restriction_sections`), tensor extension with the specified pure-tensor
  formula (`ordinary` and `pure`), and both actual Hom correspondences
  (`ordinary_transpose`, `derived_transpose`). Its `derived` and
  `representative` fix the comparison by the normalized universal counits.
  Equality of the Hom correspondences identifies both units and counits, not
  just existence of an abstract adjunction. In particular the ordinary unit is
  `p ↦ p tensor 1` and the counit multiplies the scalar into the module section.
- `projection` uses this square for every limit projection, and `quotient`
  for every transition coefficient map. `ordinary_unit` and `derived_unit`
  identify equal-index units after transport. `ordinary_composition` and
  `derived_composition` identify iterated quotient reduction using the existing
  `systemTensorCoherence A` comparisons fixed on pure tensors and universal
  counits; no arbitrary associator is introduced.
- `adjointTransition` is an actual definition: transpose the localized strict
  `systemDerivedTransition` through the recorded `systemDerivedTensorAdj`.
  The fields `transition_unitR/S` specify its equal-index identities;
  `transition_cocycleR/S` give the three-index identities with the canonical
  derived tensor comparison. `adjoint_transition` gives the transport square
  for every m≤n and every derived system. `cartesian_iff` is the asserted
  equivalence of the condition that all these adjoint maps be isomorphisms.
- Every comparison is made before an inverse limit on module systems.
  The only limits in the statement are the two coefficient-ring limits.
  There is no reconstruction assertion about an arbitrary strict system.

### Recorded dependency declarations used

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, and the associated
  Grothendieck-topology site/sheaf convention.
- `Mathlib.CategoryTheory.Functor.OfSequence`:
  `CategoryTheory.Functor.ofOpSequence`, `CategoryTheory.NatTrans.ofOpSequence`;
  systems here use their equivalent functor and natural-isomorphism formulation.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory` and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- The recorded `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly retains
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`. These are the
  generic ringed-site declarations in the dependency's recorded declarations.
  Import their smaller owning module `DerivedChangeOfRingsCochainModel` directly,
  avoiding the unrelated ordinary-module monoidal specialization.
- `Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic`:
  `SheafOfModules.StrictRingSystem`, `systemEvaluation`,
  `derivedSystemEvaluation`, `SystemScalarAssignment`, `systemDerivedTensorAdj`,
  `systemTensorCoherence`, and the associated canonical tensor functors.
- `Sheaf.CategoryTheory.SystemDerivedTransitionCoherence` and
  `Sheaf.CategoryTheory.SystemDerivedTransition` supply the actual localized
  transitions and their three-index law. `SystemRingedSequenceSite`,
  `SystemDerivedEvaluation`, `KFlatResolutionIndependentCoefficients`,
  `SheafRingCoefficientOrdinaryAdjunction`,
  `SheafRingDerivedCoefficientAdjunction`, `ChangeOfRingsKFlat`,
  and the upstream `LeftDerivedFromResolvingClass`
  are imported for the recorded proof route. The remaining proof nodes
  `lem-pur-ring-iso-derived-transport` and
  `lem-sf-exact-functor-derived-triangulated` have no recorded module to import.

### Edge cases and source reading

Read the node, its eight proof steps and statement-dependency records; read the
full recorded definitions and signatures, including the generic derived-change
model retained by the current ordinary-module module. Read the blueprint source
`main-20261015/.../def-pur-section-invariant.md`; it is a short definition of
Ls* Rg! Lambda, and the expanded system-transport content is the agent lemma
recorded in the node. Also read Stacks sites-modules.tex at the tensor-product
section and the adjoint-pullback/pushforward lemma (03EK, 03D7), and derived.tex
at the exact-functor lemma (015F). The module docstring reproduces the complete
eight-step proof route, including normalization and resolution independence.

Checked identity alpha, equal indices (including the first positive level),
three successive indices, zero complexes/modules, zero coefficient rings,
constant systems and nonflat coefficient transitions such as Z/4 → Z/2.
No flatness of coefficient maps, boundedness, surjectivity of transitions or
recovery of systems from a limit is assumed. Flatness and K-flatness appear
only where the source requires a good representative. An empty underlying site
is allowed; the index set is the fixed nonempty positive integers. Limit cones
are arbitrary limits, not assumed sectionwise chosen representatives.

### Searches

The saved `searches.jsonl` records the dispatched searches from the interrupted
turn, with their actual outputs:

- LeanFinder: “Compatible isomorphisms of inverse systems of ring sheaves induce
  exact equivalences of semilinear module systems compatible with derived quotient
  reduction”: eight hits, including inverse-system equivalences and module direct
  limit congruence, none giving this ringed-site strict/derived coherence statement.
- Loogle: `SheafOfModules.restrictScalars, CategoryTheory.Equivalence`: zero hits.
- Mathlib grep: `StrictRingSystem|restrictScalarsEquivalence|mapDerivedCategory`
  in `Algebra/Category/ModuleCat`: five hits in the ordinary module change-of-rings
  file, no strict-system transport statement.
- Project rg in `lean/Sheaf`, `lean/WeilConjectures`, and
  `dag/lean_names_upstream.json` for `ringIsoQuotientSystemTransport`,
  `CoherentTransport` and quotient-system transport terminology: no existing
  statement. Search for this node id in `lean/WeilConjectures`: no hit.
  Searches for `SystemScalarAssignment`, `systemTensorCoherence`,
  `systemModelTmul` found and reused the established interfaces, rather than
  introducing their private replacements. Read the related
  `Sheaf.Paper.QuotientSystemFlatModels`: it constructs flat reduction models
  on the sequence site, not this coefficient-isomorphism transport theorem.

### Validation

All compilation uses the prescribed `scompile.py` wrapper and the unchanged
60-second per-file limit. The first draft timed out because the very large
coherence structures generated unused constructor/size helper declarations.
Disabling those generated helpers (`genSizeOf`, `genSizeOfSpec`, `genInjectivity`,
`genCtorIdx`) allowed compilation without changing mathematical declarations.
The sole line-length warning was repaired. Subsequently the proof-valued fields
were bundled into one conjunction per record; the equation indices below give
the exact correspondence to the descriptive names used in this report. Final server-source confirmation compiled the complete module cleanly in
33.8 seconds under the unchanged 60-second limit. Delivery preflight follows.

### Coherence equation index for ScalarSquare

The single `conditions` field bundles the following equations, in order;
this reduces generated structure projections without removing any assertion.

1. `restriction_sections`: the equation described above.
2. `pure`: the equation described above.
3. `ordinary_transpose`: the equation described above.
4. `representative`: the equation described above.
5. `derived_transpose`: the equation described above.

### Coherence equation index for Reduction

The single `conditions` field bundles the following equations, in order;
this reduces generated structure projections without removing any assertion.

1. `transition`: the equation described above.
2. `universal`: the equation described above.
3. `pointwise`: the equation described above.
4. `computes`: the equation described above.
5. `evaluation_rep`: the equation described above.

### Coherence equation index for CoherentTransport

The single `conditions` field bundles the following equations, in order;
this reduces generated structure projections without removing any assertion.

1. `object_level`: the equation described above.
2. `transition_unchanged`: the equation described above.
3. `map_unchanged`: the equation described above.
4. `derived_eq`: the equation described above.
5. `localization_normalized`: the equation described above.
6. `level_sections`: the equation described above.
7. `derivedLevel_rep`: the equation described above.
8. `reduction_pure`: the equation described above.
9. `derivedReduction_rep`: the equation described above.
10. `ordinary_unit`: the equation described above.
11. `ordinary_composition`: the equation described above.
12. `derived_unit`: the equation described above.
13. `derived_composition`: the equation described above.
14. `transition_unitR`: the equation described above.
15. `transition_unitS`: the equation described above.
16. `transition_cocycleR`: the equation described above.
17. `transition_cocycleS`: the equation described above.
18. `adjoint_transition`: the equation described above.
19. `cartesian_iff`: the equation described above.

### Resumed validation

The complete final module passed the prescribed server compile twice (sandbox
25.0 seconds; library module 20.9 seconds), with no errors or warnings. Removed
an unrecorded alternative draft so the packet contains exactly its owning module.
The earlier dry run had not completed and no delivery had been pushed.

Additional searches run during resumption: LeanFinder for compatible inverse ring
sheaves and strict semilinear transport returned eight unrelated condensed-module
hits; Loogle for `SheafOfModules.restrictScalars,
SheafOfModules.pushforwardPushforwardEquivalence` returned no hits. Mathlib grep
for `restrictScalars|pushforwardPushforwardEquivalence` in
`Algebra/Category/ModuleCat/Sheaf` found the recorded restriction and generic
site-equivalence APIs, without this complete statement. LeanSearch for isomorphic
inverse ring diagrams and derived scalar extension returned eight semilinear and
module equivalence hits, without the system coherence assertion. Local searches
for the item id in `lean/WeilConjectures` and ring-isomorphism/system-transport
names in `lean/Sheaf` and `lean/WeilConjectures` found no exact existing statement.

Preflight found that `lean.declarations` listed the generated structure-field
projection `Reduction.additive`. Removed that generated projection from the
explicit declaration inventory; its Lean structure and instance attribute are unchanged.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
