## Worker report

This delivery states `lem-sfb-space-flattening-by-admissible-blowup` in
`Sheaf.AlgebraicGeometry.SpaceFlatteningByAdmissibleBlowup`, declaration
`AlgebraicGeometry.AlgebraicSpace.exists_flat_finitePresentation_spaceStrictTransform_admissibleBlowup`.
Its only theorem proof is `sorry`. The new strict-transform presentation is a structure
with actual spaces, projections, a cartesian square, a closed immersion and its complete
kernel characterization. It contains no postponed data or existence choice.

The previous BLOCKED ending concerned the already reviewed stage-1 split. I checked the
current stage-2 queue entry, the node (no Lean record), the Q127 stage-1 report and review,
and the stage-handoff instruction in brief-stage2 section 0. The accepted split remains
verbatim. No released repair note for this item was present.

The source was read directly in `spaces-more-morphisms.tex`, Tag 087E,
`lemma-flat-after-blowing-up`, including its proof, and in `spaces-divisors.tex`,
Tag 0862, `definition-strict-transform`, including the preceding discussion and Tag 0863.
The newest blueprint unit is `sk-thm-sf-ctf-stability`; its direct-images proof paragraph
(3) uses compactification before proper/open direct images. This delivery records the
existing supporting 087E node and does not change the unit or the accepted proof route.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Arbitrary scheme S and algebraic spaces Y,T over S | `{S : Scheme.{u}}`, `Y T : AlgebraicSpace S`, `g : Y ⟶ T` |
| Open subspace U of T | `U : AlgebraicSpace S`, `j : U ⟶ T`, `hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom` |
| Restriction Y times_T U -> U | `YU`, `gU`, `q`, and `hU : IsPullback q.hom gU.hom g.hom j.hom` |
| T quasi-compact | `hTqc` is a surjective representable etale atlas from a compact scheme |
| T absolutely quasi-separated | `hTqs : IsAbsolutelyQuasiSeparated T` is the existing absolute-diagonal affine-test criterion |
| U quasi-compact | `hUqc` is the same compact scheme atlas condition for U |
| g finite type | `hgft : MapIsFiniteType g`, using the recorded quasi-compact plus chartwise locally finite-type predicate |
| g quasi-separated | `hgqs : MapIsQuasiCompact (pullback.diagonal g.hom.hom)` |
| Restriction flat | `hgUflat : MapIsFlat gU` |
| Restriction locally of finite presentation | `hgUlfp : MapIsLocallyOfFinitePresentation gU` |
| A quasi-coherent ideal of O_T | `I : QuasiCoherentIdeal T`, the existing quasi-coherent subobject of the unit module |
| That ideal of finite type | `(I.val : T.Modules).IsFiniteType` |
| I restricted to U is O_U | For every etale test V whose map to T factors through j, `idealSectionImage I.val.arrow V = ⊤` |
| Blowup in this actual ideal | `B : BlowupPresentation I`, the existing descended Rees-Proj model with every affine etale scheme blowup chart |
| Strict transform of Y, retaining its centre | `D : StrictTransformPresentation g I B`; its ambient square is cartesian and its closed immersion has precisely the exceptional torsion kernel |
| Transform flat over the blowup | `MapIsFlat (D.inclusion ≫ D.toBlowup)` |
| Transform locally of finite presentation | `MapIsLocallyOfFinitePresentation (D.inclusion ≫ D.toBlowup)` |
| Transform quasi-compact | `MapIsQuasiCompact (D.inclusion ≫ D.toBlowup).hom.hom` |
| Transform quasi-separated | `MapIsQuasiCompact (pullback.diagonal (D.inclusion ≫ D.toBlowup).hom.hom)` |

The last three clauses are exactly finite presentation in the node's convention.
`YU`, `q`, `gU` name a representation of the specified fibre product, whose universal
property is imposed by `hU`; they do not add a geometric hypothesis. Similarly the
ambient space in D is fixed by its cartesian square, and its closed subspace is fixed
by its full structure-map kernel. In particular the conclusion never quantifies over
an unconstrained substitute map or an unspecified nonempty choice.

The kernel condition in the new definition uses the canonical
`idealTensorMap (toBlowup ≫ B.projection) I`. Its section-image ideal is the extended
centre ideal. On the blowup it is the exceptional invertible ideal, hence locally (t).
An element belongs to the displayed kernel exactly when, on a covering sieve, a power
of that ideal kills the element on every further etale test. Locally where the ideal
is principal this says t^n s = 0, exactly the node's torsion convention. Conversely
locally t-power torsion is killed by that sheaf-ideal power, and a covering sieve
records these local bounds. Requiring all further tests is essential: the global
sections of an ideal on a nonaffine test need not generate its stalks. The definition
therefore does not replace sheaf torsion by a weaker condition on global sections.
The closed immersion and equality of its kernel retain the entire nonreduced quotient
structure, rather than merely the underlying closed set.

Dependency declarations used, read with their signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `EtaleSite`, `structureSheaf`, `Modules`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFiniteType`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation` and their `MapIsLocally` chart tests.
  Its existing `MapIsQuasiCompact`, from `ProperCurveModuli`, supplies the scheme-test
  quasi-compactness of morphisms and diagonals.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`, Tag 0AHR(3), added to the item's statement dependencies.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using the
  unchanged `SheafOfModules.IsQuasicoherent` and the recorded etale-slice instances.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`: `QuasiCoherentIdeal`,
  `idealTensorMap`; these use the existing tensor adjunction, not an arbitrary map.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`: `moduleStructureMap`,
  normalized by the chart projections of the canonical direct image.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees`: `idealSectionImage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation`: `BlowupPresentation`,
  `blowupChartIdeal`; this already uses the recorded scheme blowup construction.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, with the full sheaf-pullback universal property.
- `def-weil-size-convention` has a metatheoretic convention record rather than a
  mathematical declaration. The delivered modules bind `universe u` and every variable
  explicitly with `autoImplicit false`, preserving the imported sites' object universe
  u+1, morphism universe u, and ring/module-section universe u.

The file imports all currently recorded proof-dependency modules. For the Mathlib leaves
it also imports finite-presentation base change/composition, affine schemes, and scheme
quasi-separatedness. The following proof nodes currently have no Lean declaration and
so have no module to import: lem-sfb-space-quasiseparated-test-calculus,
lem-sfb-space-finite-type-fp-envelope,
lem-sfb-space-closed-immersion-quasi-coherent-modules,
lem-sfb-space-relative-lfp-permanence,
lem-sfb-space-closed-pushforward-relative-flatness,
lem-sfb-space-local-properties-chart-test,
lem-sfb-space-module-flattening-by-admissible-blowup,
lem-sfb-space-strict-transform-etale-localization,
lem-trf-flattening-closed-immersion-transfer,
lem-sfb-space-separated-fp-composition,
lem-trf-locally-principal-supported-kernel. These are proof prerequisites, not notions
needed to type this theorem. The docstring contains every one of the accepted six
proof steps, including the reviewer's scheme torsion/closure comparison in step 5.

Edge cases checked before delivery:

- U=T: take the unit ideal. Its blowup is T; exceptional-ideal torsion is zero,
  so the transform is Y. Finite type and quasi-separatedness supply the two global
  finiteness clauses from the already flat locally finitely presented restriction.
- U empty: no density is imposed. The zero ideal is allowed; its blowup is empty,
  giving the empty transform, flat and finitely presented over the empty base.
- Y empty and T empty are permitted. Nothing requires nonempty atlases or a field
  point. The atlas witness can be the empty scheme.
- I=O gives zero torsion (including exponent n=0, since J^0=O); I=0 has empty blowup.
- Nonreduced bases and zero divisors in the pullback exceptional equation are allowed.
  The equation is regular on the blowup, but need not be regular on its pullback to Y;
  the definition removes exactly that torsion rather than assuming it absent.
- Exponents are local and need not admit one bound over a non-quasi-compact ambient
  test. Every refinement is tested, avoiding vacuity from nonaffine global sections.
- No separatedness of g, no Noetherian hypothesis, no global lfp of g, and no density
  of U occur in the Lean statement. The arbitrary base S need not itself be qcqs.

Searches actually run are listed below. Project `rg` searches found existing scheme
strict transforms in `WeilConjectures.Compactification.StrictTransform` and scheme-only
flattening in `Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup`; these cannot state
the algebraic-space theorem. `rg` of `AlgebraicSpace*.lean` for strict transforms found
no declaration; it did find the already landed blowup and ideal interfaces, which are
reused. A search for the item's blueprint id in WeilConjectures and Sheaf found no
declaration. DAG definition searches found scheme strict-transform nodes only.
`tools/blueprint_refs.py search 'strict transform'` found 30 blueprint nodes, all scheme
or unrelated transform settings; the narrower query 'algebraic space strict transform'
found zero. The ancestor tool returns None for this supporting chain, as the item itself
records; the new node retains its inherited place and prepends the item to its via path.

There is no statement correction, disputed statement, or dependency-interface replacement.

## New nodes

`def-sfb-space-strict-transform-presentation` defines a presentation of the actual
algebraic-space strict transform by its ambient cartesian square, representable closed
immersion, and exact canonical structure-map kernel of locally power-torsion sections.
It is Tag 0862(2), retaining the blowup centre. The module is
`Sheaf.AlgebraicGeometry.AlgebraicSpaceStrictTransformPresentation`, declaration
`AlgebraicGeometry.AlgebraicSpace.StrictTransformPresentation`. Its three logged searches
(LeanSearch, LeanFinder and Mathlib grep) are copied with their actual results into the
node. Neither the scheme strict-transform definition nor the existing blowup presentation
provides this algebraic-space closed-subspace interface. All notion dependencies cite
existing nodes. No theorem or proof obligation is added to this definition module.

## Validation

Both delivered modules compiled individually in dependency order via scompile.py against
the published live library. No errors or unexpected warnings were reported. There are no
#check probes, auto-bound variables, private definitions, local notation or local instances.
The modules use module mode and the expected public statement/private proof imports.

## Search log

- `grep` query `flattening|flatification|strict.?transform`: available, 0 hits. No hits.
- `loogle` query `"flat", "blowup"`: available, 0 hits. No hits.
- `leanfinder` query `A finite type quasi separated algebraic space over a qcqs base flat and finitely presented on a quasi compact open can be made flat and finitely presented by admissible blowup and strict transform`: available, 8 hits. AlgebraicGeometry.UniversallyOpen.of_flat, AlgebraicGeometry.LocallyOfFinitePresentation, AlgebraicGeometry.Flat, AlgebraicGeometry.instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget, AlgebraicGeometry.Flat.instHasRingHomPropertyFlat, AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact', AlgebraicGeometry.AffineSpace.instLocallyOfFinitePresentationOverSchemeInferInstanceOverClassOfFinite, AlgebraicGeometry.LocallyQuasiFinite
- `leanfinder` query `Flattening a finite type algebraic space by admissible blowup`: available, 8 hits. AlgebraicGeometry.Flat, AlgebraicGeometry.Flat.instHasRingHomPropertyFlat, AlgebraicGeometry.Proj.instLocallyOfFiniteTypeToSpecZeroOfFiniteTypeSubtypeMemOfNatNat, AlgebraicGeometry.UniversallyOpen.of_flat, AlgebraicGeometry.AffineSpace.instLocallyOfFinitePresentationOverSchemeInferInstanceOverClassOfFinite, AlgebraicGeometry.Flat.instIsMultiplicativeScheme, AlgebraicGeometry.Proj.instUniversallyClosedToSpecZeroOfFiniteTypeSubtypeMemOfNatNat, AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
- `loogle` query `"flat", "blowup"`: available, 0 hits. No hits.
- `leanfinder` query `A closed subspace of the pullback under an algebraic space blowup defined by sections killed locally by powers of the exceptional ideal strict transform`: available, 8 hits. AlgebraicGeometry.Scheme.IdealSheafData.subscheme, AlgebraicGeometry.Scheme.IdealSheafData.subschemeι, AlgebraicGeometry.Scheme.IdealSheafData.glueDataObj, AlgebraicGeometry.Scheme.IdealSheafData.comap, AlgebraicGeometry.Scheme.IdealSheafData.map, AlgebraicGeometry.specTargetImageIdeal, AlgebraicGeometry.specTargetImage, AlgebraicGeometry.specTargetImageFactorization
- `leansearch` query `Algebraic space strict transform is closed subspace defined by sections supported on exceptional divisor`: available, 8 hits. AlgebraicGeometry.RingedSpace.zeroLocus_isClosed, AlgebraicGeometry.Scheme.IdealSheafData.subscheme, AlgebraicGeometry.Scheme.zeroLocus_isClosed, AlgebraicGeometry.Scheme.IdealSheafData.support, AlgebraicGeometry.Scheme.IdealSheafData.Simps.coe_support, AlgebraicGeometry.Scheme.IdealSheafData.isClosed_supportSet, AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal, AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι
- `grep` query `strict.?transform|torsion.*ideal`: available, 0 hits. No hits.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
