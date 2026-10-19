## Worker report

The retained attempt had only a partial Lean module and search log. It allowed arbitrary
functors LZ/LW and arbitrary comparison isomorphisms, omitted the boundedness of LZ(J) and
LW(Rf_*J), and did not formally fix the coefficient pullback on the projection target.
Those parameters have been replaced by canonical constructions. The item statement is
unchanged. The theorem is `AlgebraicGeometry.Etale.scalarMate_restrict_eq_projection` in
`Sheaf.Paper.PurEtaleScalarMateProjection`.

Hypotheses and clauses, in order:

- Arbitrary schemes Z,W and morphism f: `{Z W : Scheme.{u}} (f : Z ⟶ W)`.
- Arbitrary commutative rings and their homomorphism: `{A B : Type (u + 1)}`,
  `[CommRing A] [CommRing B]`, and `(φ : A →+* B)`. This is the recorded small-etale
  size convention, not an equality imposed on independent site universes.
- Ordinary unbounded coefficient categories: `DerivedCategoryModule A T`, literally
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`.
- L_T is the existing `ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ`.
  `scalarExtension φ T` is a transparent abbreviation for that exact published functor;
  it makes no new choice. Its derived restriction is `Sheaf.derivedRestrictScalars`.
- The inverse/direct-image functors and adjunctions are the exact recorded
  `L(upperStar (ModuleCat A) f)`, `R(lowerStar (ModuleCat A) f)` and
  `derivedUpperStarLowerStarAdjunction` (and likewise for B).
- The scalar/pullback comparison is `scalarPullbackIso`, uniquely specified by its square
  with the derived counits on K-flat representatives. The ordinary square is the
  adjunction conjugate of the sectionwise direct-image/restriction identity. It is not
  an arbitrary isomorphism or an invertibility assumption on a coefficient mate.
- J in D+ is the binder `J : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat A))`.
- LZ(J) in D+ is `_hN`: an object N of the B-coefficient Plus category with
  `N.obj = (scalarExtension φ Z).obj J.obj`. Strict fullness makes this exactly boundedness.
- LW(Rf_*J) in D+ is `_hM`, expressed by the analogous equality with a Plus object M.
  Neither boundedness assertion is inferred from arbitrary scalar extension.
- The specified B-linear beta is `(scalarMate φ f).app J.obj`. `scalarMate` is the natural
  transformation obtained by `mateEquiv` from `scalarPullbackIso.hom`; its component is
  the B-geometric transpose of the scalar-extended A-counit, as in the node.
- The scalar/tensor identifications are `scalarTensorIso φ T`, uniquely fixed by the
  ordinary balancing map on K-flat representatives. Its target is tensor on the right
  with `scalarCoefficient φ T`, the restricted B-unit sheaf placed in degree zero.
  `scalarSheafTensorMap` is real data: scalar unit, restriction tensorator, then unitor.
  `scalarExtensionRepresentative` is real data: transpose of the termwise scalar unit
  under the EXISTING derived scalar adjunction. No object or map is chosen from a mere
  nonempty proposition. Only uniqueness-characterized natural isomorphisms use choice.
- The canonical direct-image restriction map is
  `scalarRestrictionDirectImageMap` in the dependency interface repair, the mate of the exact derived
  inverse-image/restriction square. On the bounded-below objects here it is precisely the
  comparison of lem-sbc-canonical-restrict-scalars-functor-comparisons, with the counit
  normalization of lem-sbc-restrict-scalars-derived-adjunction-identities.
- Equality of specified arrows is the theorem's `=`. Its left side is U(beta), followed
  by that canonical restriction comparison. Its right side is `scalarTensorIso` on the
  source, the actual `rightDerivedLowerStarProjectionMap` at `(J, B_W[0])`, and Rf_* of
  the target identification. `scalarCoefficientPullbackIso` fixes f_A^{-1}B_W[0]=B_Z[0]
  using the exact derived sheaf comparison and the ordinary inverse-image unit isomorphism.
- Naturality in J is retained by defining beta as a NATURAL TRANSFORMATION, and using the
  recorded natural projection transformation and natural scalar/tensor isomorphisms.
  The theorem gives their component equality for every object of the stated full domain;
  hence it is equality of the restricted natural transformations, including all domain
  morphisms. It does not assert a scalar extension preserves D+ on other objects.
- No properness, torsion, coefficient flatness, finiteness or isomorphism conclusion is
  added. UpperStarPreservesFlat is discharged by the published ModuleCat instance; it
  is not a binder in the statement.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: `DerivedCategoryModule`;
  Mathlib.Algebra.Homology.DerivedCategory.TStructure: `DerivedCategory.Plus`.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, publicly retained by the
  dependency module; its constant-coefficient specialization is the additional interface.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars:
  `CategoryTheory.Sheaf.restrictScalars`; the original Mathlib
  `SheafOfModules.restrictScalars` match remains in the dependency node.
- WeilConjectures.SixFunctors.ProEtale.ScalarExtension:
  `etaleSheafExtendScalars`, `etaleSheafExtendScalarsAdjunction`.
- Sheaf.Paper.WitnessCompatibility: `ProEtale.pbcRestriction_isRightAdjoint` and
  `ProEtale.pbcFixedScalarExtension`; imported through the scalar dependency module.
- WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection:
  `rightDerivedLowerStarProjectionMap`, its target bifunctor and its canonical adjunction.
- Sheaf.Paper.PbcActualScalarPullback, reexporting the general ringed-topos interface:
  `pbcActualScalarDerivedPullIso_exists` and the retained canonical tensor interfaces.
  The item's helper `scalarPullbackIso_existsUnique` specializes that same normalized
  comparison to constant coefficients in the ModuleCat presentation.
- Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons:
  `upperStarRestrictScalarsIsoSheaf`, `derivedLowerStarRestrictScalarsMap` and its iso.
- Sheaf.Paper.EtaleUnboundedRestrictionComparison:
  `scalarRestrictionPullbackIso`, `scalarRestrictionDirectImageMap`, supplying the
  ambient-category presentation of the recorded bounded-below comparisons. Their exact
  restriction square uses `Functor.mapDerivedCategorySquareIso`; their counit mate uses
  the existing geometric derived adjunctions. No new mathematical assumption is made.
- Proof imports retain ChangeOfRingsTensorComparison, KFlatResolutionIndependentCoefficients,
  EtaleRestrictScalarsAdjunctionIdentities, BaseChangeMapAbelianAndSets, and
  ExactUnboundedExchange. Their declarations and source docstrings were inspected.

Edge cases checked before finalizing the statement: f=id (the counit transpose and unit
normalizations recover scalar extension); φ=id (all scalar comparisons are the unit ones);
J=0 and B=0; empty schemes; and a nonflat map such as Z→Z/2. In the last case scalar
extension need not preserve boundedness for arbitrary J, so the two node hypotheses are
explicitly retained. No chosen cohomological lower bound or finite-Tor assumption is added.

Searches: retained msearch.py LeanFinder query "Restriction of derived extension of scalars
direct image counit mate equals projection formula map" returned module counit declarations,
not this derived equality. Loogle query `CategoryTheory.Adjunction.homEquiv` returned the
abstract adjunction API. Mathlib grep `scalar.*mate|[Pp]rojection[Ff]ormula` under CategoryTheory
returned no hits. A fresh msearch.py LeanSearch query "Restriction of derived extension of
scalars along a ring homomorphism identifies the geometric counit mate with the projection
formula morphism" returned restriction/extension of scalars and ordinary module counits,
not this theorem. Source/project rg for `scalarMate`, the item id, `scalarTensorIso`, and
`scalarExtensionRepresentative` found no exact existing item. Broader scalar-extension and
tensor searches found the published fixed scalar extension, which is reused, and equivalent
restriction helpers in FiniteCoefficientDirectImage. Its existing scalar-unit identity is weaker
than the present equality and does not replace the item. Its source was read using
scompile.py --source. Importing that large module failed with duplicate
`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv` declarations from
WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso and
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso. The smaller
recorded restriction-comparison dependency therefore gets the ambient interface below.
The finite-coefficient node is not added as a dependency.

## Dependency modules

`lem-pur-derived-change-of-rings`: `Sheaf.Paper.EtaleDerivedScalarTensor` publicly preserves the
entire recorded arbitrary-ring-sheaf interface. That interface cannot itself type an arrow
between the consumer's ModuleCat-valued sheaves, so the module supplies the constant-ring
presentation and the canonically normalized scalar/tensor comparison. It reuses both the
published ordinary extension and the published derived scalar extension. All definitions have
real data. `scalarTensorModelNormalization` records the exact model equation in a general
monoidal category before specialization; it uses
the lax tensorator of `DerivedCategory.Q` and the total-tensor/single-complex
comparison; on K-flat representatives this is the existing
`DerivedCategory.QObjTensorSingleFunctorObjIso`. The normalization on arbitrary complexes
follows from its naturality with respect to a K-flat resolution. It introduces no second
tensor construction. The four postponed theorems concern additivity, naturality of the ordinary
balancing map, equality of the general and site-specific tensor functors, and
existence/uniqueness of the normalized derived comparison; each has its
source and mathematical proof in its docstring and belongs to this dependency's statement.

`lem-sbc-canonical-restrict-scalars-functor-comparisons`:
`Sheaf.Paper.EtaleUnboundedRestrictionComparison` publicly preserves the original bounded-below
comparison module. It supplies the ambient inverse-image/restriction square and its geometric
mate, needed because the consumer's equation lives in unbounded derived categories. These are
real data, with no postponed theorem. On D+ the counit identities identify this mate with the
original `derivedLowerStarRestrictScalarsMap`. The mathematically identical helper in the larger
FiniteCoefficientDirectImage module has an unusable import closure (the duplicate above);
this repair uses only the original dependency and the geometric derived adjunction module.
No unbounded isomorphism assertion is added; only its D+ specialization is used.

`def-pc-sheaf-restrict-scalars`: lean-only repair to the exact existing
`CategoryTheory.Sheaf.restrictScalars` in the upstream constant-coefficient module. The old
Mathlib match for arbitrary ring sheaves is retained unchanged. The note explains the two
presentations and why the old declaration did not accept the consumer's objects.

## Second reading by Q158

This is the worker's final rereading; the maintainer supplies the independent delivery review.
The old arbitrary LZ/LW,c,e,d,q parameters were the principal semantic defect. The new file fixes
L to the existing scalar extension, c and e by their model normalization, d to the existing
canonical mate, and the target coefficient pullback by an actual isomorphism. Both missing
D+ hypotheses are restored. I checked the tensor order and the directions: U(beta) then d
and e_W then PF then R((1 tensor coefficient-pullback) followed by e_Z inverse) have exactly
identical source and target. Beta is B-linear and its construction uses no faithfulness of
restriction on derived morphisms. No changes to the natural statement or its proof are needed.

The derived category in the statement is the recorded `DerivedCategoryModule` from the
common upstream Coefficients module, publicly imported by the scalar dependency module.
No torsion definition is used.

Validation: scompile.py compiled each of the three delivered modules separately, both
as sandbox files and at its library path, in one dependency-ordered invocation. Exit 0;
no errors or warnings other than the permitted sorry warnings. Library-path times were
12.3 s (EtaleDerivedScalarTensor), 6.7 s (EtaleUnboundedRestrictionComparison), and
24.2 s (PurEtaleScalarMateProjection), each under the unchanged 60 s limit. The earlier
expensive tensor specialization was repaired by the explicit equality between the
site-specific and general presentations of the same tensor functor. No compiler limits
were increased. The original node statement and all dependency lists remain unchanged.
Delivery dry run: `deliver2.py Q158 lem-pur-etale-scalar-mate-projection --no-push`
returned `OK (dry run)` at 469e31604e: server preflight and all per-file compiles passed.
