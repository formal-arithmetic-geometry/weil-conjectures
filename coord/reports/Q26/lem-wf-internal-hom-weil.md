## Worker report

Module: `lean/Sheaf/Paper/WeilInternalHomWeil.lean`.
Main statement: `WeilConjectures.wf_internalHom_weil`.
This is a stage-2 statement delivery: every theorem has proof `sorry`; every
construction has explicit data or uses an existence-and-uniqueness theorem
whose normalization determines those data. There is no arbitrary choice of
an internal Hom, morphism action, Frobenius comparison, or shift comparison.

Read the whole item (six proof steps), its three statement dependencies and their
recorded declarations, and the main-20261015 blueprint statement and proof at
`sec-algebraic-groups-lie-algebras/sk-p-cyclotomic/lem-wf-internal-hom-weil`.
No repair note exists for the item. The old example Sheaf/CompactObject module
is withdrawn, so the recorded upstream CategoryTheory/CompactObject module
was also read for the actual declaration/header conventions.

Hypotheses and clauses, one by one:

- Global finite-field data: `D : FiniteFieldDatum.{u}` gives the stipulated
  characteristic, finite base field, algebraic closure and geometric fiber.
- Coefficients: `c : D.CoefficientDatum` supplies the prime ell, ell different
  from D.p, and its chosen algebraic closure. `E : Padic.FiniteCoefficientFields
  c.l c.Qbar` is precisely a finite intermediate extension. `pbcFiniteField`
  is the canonical small model Shrink E, not a smaller collection of fields.
- Geometry: `X₀ : Over (Spec (CommRingCat.of D.k₀))` and the three instances
  `IsSeparated X₀.hom`, `LocallyOfFiniteType X₀.hom`, `QuasiCompact X₀.hom`
  say separated finite type. The geometric fiber is `D.geometricFiber X₀`.
- The coefficient category is exactly `pbcStageCategory`, definitionally the
  PbcRationalCategory already used in `WeilD`, with completed integral
  coefficients. All object/morphism/derived universes follow the recorded
  interfaces (site objects u+1, arrows u, coefficients u+1, derived u+2).
- Closure: `wfHom_constructible` states closure of the full integral
  subcategory for the recorded ambient `wfOrdinaryDerivedHom`. Its explicit
  full-subcategory restriction is `wfConstructibleIntegralHom`.
  `wfConstructibleRationalHom_existsUnique` fixes the entire rational functor
  by equality after the two integral localization functors. Since objects
  are unchanged, this also fixes its object function; the fraction rule
  uniquely fixes its morphism function. It does not choose a witness merely
  to an unspecified nonempty collection.
- The main theorem's first functor equality says that this restriction is
  exactly the ambient `wfInternalHom`, through the recorded inclusion.
- The existential `W` has domain `(WeilD ...)ᵒᵖ × WeilD ...` and target
  `WeilD ...`, so it includes all bifunctor identity and composition laws.
  Its object clause identifies its carrier with the prescribed Hom object.
- The second object clause is `HEq (wfWeilStructure ... (W.obj ...))
  (wfInternalHomFrobenius ... K L)`. The latter is the actual invertible
  alpha followed by H(phi_K inverse,phi_L), defined in def-wf-internal-hom.
  Thus the theorem specifies the conjugation itself, including invertibility;
  it does not substitute an arbitrary Weil structure. HEq accommodates the
  equal carrier objects occurring in different dependent elaborated types.
- For commuting Weil morphisms `f : K' ⟶ K`, `g : L ⟶ L'`, the map equation
  identifies `(W.map (Prod.mkHom f.op g)).hom.f` with the coefficient Hom
  map on `f.hom.f.op`, `g.hom.f`. Its composite with the first equality is
  exactly the prescribed ambient H(u,v).
- Shifted pair: `wfHomShiftPair K n` has carrier K.carrier[n], and structure
  `wfHomFrobeniusShiftComponent ... ≪≫ (shiftFunctor _ n).mapIso K.str`.
  The component is constructed by localizing the exact module transport's
  shift comparison through the existing integral full inclusion. No extra
  commutation datum is assumed.
- Canonical shifts: `wfIntegralHomRightShift` and `wfIntegralHomLeftShift`
  are built from the recorded `RingedHomUniverses.hom.commShiftIso` and
  signed `sourceShift`, respectively, together with the integral inclusion's
  comparisons. `wfRationalHomRightShift`/`LeftShift` localize those exact
  components via `wfConstructibleHomModel`. `wfHomDoubleShift` composes the
  two with `shiftFunctorAdd'` to give precisely [s-r]. The main theorem
  asserts an isomorphism of Weil pairs whose underlying hom is HEq to this
  actual canonical derived comparison. It is an isomorphism in the derived
  category, not just an isomorphism of cohomology groups.
- Triangle inputs: `WfHomPreservesTriangles` quantifies over all three Weil
  objects and all three Weil morphisms `f`, `g`, `h : C ⟶ shiftedPair A 1`,
  with exactly the hypothesis that their underlying coefficient triangle
  belongs to `distTriang`. There are no extra vanishing or cone assumptions.
- Covariant output: the first two arrows are the W-maps of f and g; the
  connecting arrow is a Weil morphism `j` whose carrier is the actual
  coefficient H(id,h) followed by `wfRationalHomRightShift`. The displayed
  output coefficient triangle must be distinguished.
- Contravariant output: the first two arrows are W(g.op,id), W(f.op,id), in
  order H(C,L), H(B,L), H(A,L). The connecting arrow is a Weil morphism
  whose carrier is `wfHomLeftConnecting`, explicitly the signed source-shift
  inverse followed by H(h,id), shifted once, and cancellation of [-1][1].
  The output coefficient triangle must be distinguished. Thus even the
  connecting map is specified, not merely its existence for given objects.
- Separate additivity: the two Additive conjuncts use the fixed-source and
  fixed-target curried functors of W.
- Separate E-linearity: `wfHomCoefficientLinear` is an adapter to the EXISTING
  `pbcRationalLinear`, using its exact `pbcRationalCoefficientEquiv` field
  action. `wfHomWeilLinear_existsUnique` fixes the scalar action on the
  existing preadditive Weil category by its faithful underlying arrows.
  The main theorem states Linear for the covariant functor and the scalar
  equation on reversed arrows for the contravariant functor (Mathlib has no
  ambient Linear instance on the opposite category). It also records the
  same coefficient-functor linearity. No conjugate-linear interpretation is
  used for the contravariant slot.
- The dimension and invertibility Fact arguments are supplied explicitly
  from `weilGeometricFiber_coefficientHypotheses`, not additional hypotheses.
  Existing integral and localized triangulations then interpret distTriang
  on the exact raw rational category. The module asserts no pretriangulated
  or Verdier structure for WeilD.

Dependency declarations used:

1. `Sheaf.Paper.WeilInternalHom`: `wfOrdinaryDerivedHom`, `wfInternalHom`,
   `wfInternalHomFrobenius`, and the canonical transport construction read
   through its ordinary, complex, derived and rational normalization equations.
2. `Sheaf.Paper.PbcWeilCategory` (publicly imported by WeilInternalHom):
   `WeilD`, `weilFrobeniusPullback`, `weilGeometricFiber_coefficientHypotheses`,
   and `CategoryTheory.Endofunctor.IsoAlgebra.preadditive`.
3. `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`:
   `IsoAlgebra.mk`, `carrier`, `str`, and its underlying commuting morphisms.
4. `Sheaf.Paper.WeilTensorProduct`: existing `wfConstructibleInclusion`,
   `wfWeilCarrier`, `wfWeilStructure`, `wfUniformizer_generates`, ambient
   category and Frobenius; no new tensor construction or tensor theorem is used.
5. `Sheaf.Paper.FiniteStagePairCategory`: `pbcIntegralStage`, `pbcStageCategory`,
   `pbcStageInclusion`, `pbcStageLocalization`, the exact recorded categories.
6. `Sheaf.Paper.LocalizedTStructure`: existing integral-induced/localized
   coefficient shifts and distinguished triangles, including exact localization.
7. `Sheaf.Paper.PbcRationalTransport`: `pbcRationalLinear`,
   `pbcRationalCoefficientEquiv`; the scalar action adapter delegates to it.
8. `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`:
   `RingedHomUniverses.hom`, `homCommShift`, `sourceShift`; their normalized
   representative equations and `hom_isTriangulated` were read.
9. Mathlib `CategoryTheory.Triangulated.Pretriangulated`, `Functor`,
   `Triangulated` and `Basic`: `Pretriangulated`, `IsTriangulated`,
   `Pretriangulated.Triangle.mk`, `distTriang`, as def-weil-triangulated-category's
   mathlib_match specifies. Only coefficient triangles are used here.
10. Proof imports: `IntegralStratifiedPerfectCharacterization`
    (`integralStratifiedPerfectCharacterization`, its detailed comparison and
    closure), `IntegralConstructibleInternalHom`
    (`integral_constructible_internalHom`), `FiniteTypeGeometryFibreBound`
    (`finiteType_noetherianCover_dimension_geometricFibres`),
    `SfRationalizationKaroubi`, `ScalarLocalizationTriangulated`
    (`exists_triangulated_scalarLocalization`), `RingedPresentationTransport`
    (`ringed_presentation_transport`). These retain the node's six-step proof
    route; actual small-site Hom/shift constructions use the already available
    independent-universe interfaces and exact module transport.

All statement dependencies' full signatures and docstrings were read; Mathlib
matching is a declaration record, so no missing `lean` record was invented.
No dependency records, node statements or proof dependencies were changed.
No new independent notions or new DAG nodes were needed: the auxiliary
constructions are the restriction, shift components and triangle clause of
this node's existing notion, recorded in lean.declarations.

Edge cases checked mathematically before stating:

- Empty geometric scheme: the zero categories, Hom and zero triangles satisfy
  every clause; the geometric dimension bound is supplied even for dimension
  bottom. No nonempty scheme or point was required.
- Zero source or target: Hom is zero and conjugation is the unique isomorphism;
  no nonzero scalar/object hypothesis occurs.
- Point case: Frobenius acts on Hom by mu/lambda, so the first structure is
  inverted and the second is not; commuting arrows satisfy the same equation.
- Shifts r=s=0, positive and negative r,s: the formula is [s-r] with integral
  signed source reindexing, target reindexing, and canonical shift composition.
  Both connecting arrows retain these same comparisons.
- Torsion integral representatives becoming zero rationally are allowed;
  no stable integral Frobenius lattice is required or assumed.
- Nonsemisimple Frobenius structures are allowed. Nothing supplies Verdier
  axioms for the pair category; the previously reviewed triangle-diagram
  interpretation of exactness is preserved exactly.
- The coefficient prime remains different from D.p via CoefficientDatum;
  E can be the base coefficient field and any finite intermediate extension.
- No site universe equalities were added; no local notation or local instance
  appears in any statement. The local letI in the construction of the
  Frobenius shift merely selects the explicitly built canonical comparison.

Searches actually run (msearch.py Q26 lem-wf-internal-hom-weil):

- LeanFinder: "Derived internal Hom is an exact linear bifunctor on Weil
  complexes fixed by geometric Frobenius": 8 hits, including Ext and
  instLinearDerivedCategoryMapDerivedCategory; no matching completed Weil
  statement.
- Loogle: "CategoryTheory.Functor.IsTriangulated,
  CategoryTheory.Endofunctor.IsoAlgebra": zero hits, unknown identifier for
  the project's IsoAlgebra; not reported as a successful exact match.
- Mathlib grep: "WeilD|wfInternalHom|internalHomFrobenius", CategoryTheory:
  zero hits.
- LeanSearch: "Derived internal Hom preserves constructible complete Weil
  complexes and distinguished triangles": 8 hits about homotopy-category
  triangulation, homology preservation and derived exact functors; no match.
- rg of the project WeilConjectures/ and Sheaf/ for wfInternalHom,
  internalHomFrobenius and the blueprint id finds the ambient dependency and
  WeilComplexInternalHom. Read the upstream latter's full variables and
  internalHom declaration: it uses DerivedCategoryFiniteTor and ordinary
  etale coefficient sheaves, not the raw rational completed integral PBC
  category. Its blueprint label alone does not make it an existing match.
- rg of dag/lean_names_upstream.json for the same names finds no exact binding.
- Additional local rg searches located coefficient rational triangulations,
  full-subcategory shift comparisons, pbcRationalCoefficientEquiv and the
  independent-universe signed Hom shifts. The already landed tensor theorem
  was read as a neighboring interface, but does not state this Hom result.

Validation: scompile.py compiles the complete file both as sandbox module and
as `Sheaf.Paper.WeilInternalHomWeil`; final run clean (49.1 s and 46.9 s), no
warnings. Every binder and universe is explicit under autoImplicit false.
The node's lean.statement is copied verbatim from the main theorem signature.
The dry run and final delivery outcomes are recorded by the prescribed tools.

No STATEMENT-DISPUTED flag and no statement correction: the delivered statement
retains the item's already reviewed interpretation of exactness. Independent
second reading is left to the maintainer as directed by the worker brief.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
