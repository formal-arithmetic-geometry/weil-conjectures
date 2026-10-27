## Worker report

Delivered module: `Sheaf.Paper.CompleteIntegralResidueFunctor`.
Primary declaration:
`AlgebraicGeometry.ProEtale.CompleteIntegralResidue.complete_integral_residue_functor`.
The only new theorem has proof `sorry`; every helper has actual construction data.
The DAG statement and dependencies are unchanged. There are no new nodes or dependency
repairs, and no STATEMENT-DISPUTED finding.

Source read: main-20261015 blueprint integral-heart triangulated proof, paragraph (1),
first two sentences; derived-Nakayama first-reduction proof, Cones paragraph and shifts
sentence. Also read the local Stacks sources: derived.tex, lemma-third-isomorphism-triangle
(014A); sites-cohomology.tex, lemma-derived-base-change (06YY); sites-modules.tex,
section-constant (093I). Read the pro-etale framework coordination document and the full
signatures/docstrings of the recorded interfaces used below. The example CompactObject
module is now withdrawn; its node's record remains the example for the JSON shape.

Hypotheses and clauses, in node order:

1. An arbitrary scheme on its fixed small pro-etale site is `(X : Scheme.{u})` and
   `Scheme.ProEt.topology X`. The site has object universe u+1 and morphism universe u;
   abelian sheaves and coefficients use u+1. Internal module objects, their unbounded
   derived categories and the ordinary sheaf-module category retain those universes.
   No equality of object/morphism universes or site replacement is imposed.
2. The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is
   `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
   `Padic.coefficientExtensionRing l E 1` is precisely O_E/(pi_E), for the recorded
   valuation ring and chosen uniformizer. `Scalar` is only its `ULift.{u+1}` to the
   existing scalar universe, with its usual transported ring structure.
3. The actual continuous integral ring is `AdicCompletion.ring l E X`, used through
   `AdicCompletion.Modules l E X`. The actual residue ring object S_X is
   `AdicCompletion.finiteRing l E X 0`: the index 0 denotes exponent 1, not exponent 0.
   Its actual quotient map is `AdicCompletion.quotient l E X 0`.
4. C is exactly `IsDerivedComplete l E X`. Its recorded definition requires invertibility
   of the specified augmented Roos comparison on a K-flat representative, and its recorded
   `isDerivedComplete_iff` identifies this with the actual canonical completion map on
   any K-flat representative. No arbitrary isomorphism with a completion object is used.
5. C(0) is the first conjunct, with the ambient derived zero object. The next conjunct
   explicitly asserts C(K[r]) iff C(K) for every K and every integer r. The existential
   `_hclosed : ObjectProperty.IsClosedUnderIsomorphisms C` gives invariance under all
   ambient isomorphisms. `_htri : ObjectProperty.IsTriangulated C`, together with that
   closure, gives all three two-out-of-three implications in every ambient distinguished
   triangle. Mathlib's `IsTriangulatedClosed₁`, `IsTriangulatedClosed₂` and
   `IsTriangulatedClosed₃` instances and their `ext_of_isTriangulatedClosed*` theorems
   give exactly these three cases. The predicate's `FullSubcategory` has all ambient Homs.
6. `constantRing` is the existing `constantSheaf` of the lifted residue ring in RingCat.
   `continuousRing` specializes `finiteCoefficientRingSheaf` to that residue ring with
   discrete topology. The latter is the sheafification of `finiteCoefficientPresheaf`,
   whose values are continuous functions on `ConnectedComponents U.left`, with its
   quotient topology. It is not a locally constant replacement defined on qc objects.
   The finiteness instance is supplied by `Padic.finite_coefficientExtensionRing`;
   discreteness of the topology ⊥ is its defining equality, not a new postponed lemma.
7. `constantToContinuous` is the adjoint extension of the existing
   `finiteCoefficientScalarMap`, which is constant functions followed by sheafification.
   `IsIso (constantToContinuous ...)` asserts invertibility of this specified morphism.
8. `sectionRing` is the underlying ordinary ring sheaf of the recorded commutative
   section-ring construction on S_X. The isomorphism b from `constantRing` to `sectionRing`
   is required, for every site object U and every scalar a, to take the sheafification
   unit's constant scalar to `pulledBackConstants` applied to that same scalar.
   `pulledBackConstants` is the existing `canonicalAbelianMap` for the actual quotient
   topology induced by the spectral absolute value on E. Thus it refers to the actual
   pulled-back continuous residue ring, not a different discrete coefficient object.
   The isomorphism e to `continuousRing` satisfies
   `b.hom ≫ e.hom = constantToContinuous`. Therefore e agrees with the required
   constant-function identification on every scalar. The section-ring construction
   and its equivalence express an internal ring object in ordinary ring-sheaf notation.
9. The equivalence A is between actual internal S_X-modules and ordinary modules over
   `continuousRing`. Its forward functor is fixed by
   `A.functor = relabel l E X e`, where relabel is exactly the recorded section-action
   equivalence followed by restriction along e.inv. It therefore specifies the residue
   action and every map, not just an unrelated equivalent category. The existential
   additive witness records a property of this functor; it is a conclusion, not an
   assumption on the input. Equivalences preserve kernels/cokernels, giving exactness.
10. `AdicCompletion.derivedReduction l E X 0` is by definition the actual left derived
    extension of scalars along the quotient to S_X. Its codomain is D(Mod S_X), so the
    action has not been discarded. The natural-isomorphism conjunct identifies its
    composite with `AdicCompletion.restrict` with
    `DerivedNakayama.reductionFunctor l E X 1`, which is precisely relative derived
    tensor with the degree-zero residue coefficient module. Thus actual relative tensor
    reduction is asserted naturally on all unbounded objects. This is the comparison
    explained by the item's K-flat proof step, not an extra flatness hypothesis.
11. T₁ has source D(AdicCompletion.Modules) and target the unbounded ordinary derived
    category of `SheafOfModules continuousRing`. Its equality with the composite of
    actual derivedReduction and `A.functor.mapDerivedCategory` fixes its objects/maps.
    `_sT₁ : T₁.CommShift ℤ` supplies coherent comparisons for every integer shift;
    `T₁.IsTriangulated` supplies preservation of distinguished triangles. `IsZero
    (T₁.obj 0)` explicitly asserts preservation of zero. Every functor preserves
    isomorphisms, so no extra theorem or hypothesis for that clause is necessary.
12. `((ObjectProperty.ι C) ⋙ T₁).IsTriangulated` is the restriction along the strictly
    full complete subcategory's inherited exact inclusion. Its shift and triangulated
    structures come from the witnesses of isomorphism closure and triangulation above.
13. There are no boundedness, Noetherian, quasi-compactness, dimension, finite-type,
    characteristic or invertibility assumptions on X in any binder or helper.

Dependency interfaces used (all original statement dependencies were read):

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
  The size-convention node has no declaration by design; explicit universes render it.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the original coefficient constructions
  publicly retained from `CoefficientExtension`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint` (used through the recorded
  integral and finite coefficient specializations).
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and Mathlib's
  `DerivedCategory`: the recorded unbounded derived-category convention; no new
  derived category is introduced.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`: `IsDerivedComplete`, `ring`, `Modules`,
  `finiteRing`, `quotient`, `derivedReduction`, `restrict`, `isDerivedComplete_iff`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `finiteCoefficientPresheaf`, `finiteCoefficientScalarMap`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and its Tensor import:
  `CondensedRing.derivedTensor`, `derivedHom`; `DerivedNakayama.reductionFunctor` uses
  this exact relative tensor, not tensor over Z with an informal quotient.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly retains
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem for ringed
  sites with independent universes. The item uses the already specialized internal
  scalar-extension interface `Mod.extendScalars.leftDerivedFunctor` through derivedReduction;
  the generic ringed-site interface and its actual section-tensor computations are usable,
  so no dependency repair or stronger hypothesis is needed.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `constantSheaf`, `toSheafify`,
  `sheafificationAdjunction`; all sheafifications above are these constructions.
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`:
  `FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence`; its publicly
  retained `FiniteDiscreteOrdinaryEncoding` supplies `canonicalAbelianMap`, `Encoding`,
  `encoding_exists` and the scalar-normalization interface used by the statement.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, publicly available from
  the coefficient encoding: `sectionRingSheaf`, `sectionModuleEquivalence`.
- Proof imports retain `CompletionTriangleComparison.completion_triangle_comparison`,
  `continuousSet_descent_components`, `internal_section_tensor_comparison`, and the
  independent-coefficient K-flat resolution interface. Mathlib's triangulated-subcategory,
  triangle-isomorphism, sheafification-underlying-sets and exact-derived-functor APIs are
  imported through the corresponding modules. The six proof steps are in the theorem
  docstring in full.

Edge cases checked: X empty (empty-cover constant sheafification remains the correct
object, not the raw constant presheaf); X non-quasi-compact/non-Noetherian; disconnected
and infinite-component site objects (continuous functions on the full quotient, with
sheafification); K=0; all integer shifts including negative shifts and r=0; triangles
with any one of the three vertices missing from the two hypotheses; unbounded integral
complexes; every prime l with no assumption that l is invertible on X. The coefficient
level 0 is deliberately exponent 1, so it is the residue field rather than O_E/(1).
The scalar normalization and commuting ring square also exclude an unintended residue
field automorphism. No vacuous existence of an arbitrary equivalence or functor is used:
b and e are pinned by scalars and the square, A by its functor equality, T₁ by its equality
with the actual derived-extension composite.

Searches actually run:

- msearch leanfinder: `Derived complete integral proetale complexes form a triangulated
  subcategory with exact residue reduction`. Eight hits: generic derived-category
  triangulation, t-structures and homological kernels; no complete integral residue functor.
- msearch loogle: `"IsTriangulated", "ObjectProperty"`. Twelve hits, including
  `ObjectProperty.IsTriangulated` and its closure instances; reused this exact API.
- msearch grep: `derivedComplete|complete_integral_residue|residueReduction`. Zero hits.
- msearch leansearch: `Derived complete integral sheaf complexes form a triangulated
  subcategory and derived residue scalar extension is exact`. Eight hits including
  generic `Triangulated.Subcategory`, `DerivedCategory.instIsTriangulated`,
  `Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory`, `HasDerivedCategory.standard`;
  these are component APIs, not the item.
- rg on `lean/WeilConjectures` and `lean/Sheaf`: `IsDerivedComplete`, `residueReduction`,
  `residueFunctor`, `complete_integral`, `completion_triangle`, followed by exact-name
  checks for the new namespace and theorem. Existing completion and relative scalar-extension
  components were reused; no declaration states the complete item. The prescribed grep
  for this item's blueprint id in `lean/WeilConjectures` had zero hits. The broader
  constantToContinuous search finds other private and differently scoped constant maps;
  the helper here is only the adjoint extension of the recorded finiteCoefficientScalarMap.

Validation: scompile.py compiled both the sandbox module and its intended library name
cleanly (24.6 s and 24.8 s), under the default per-file limit. The initial elaboration
failures were fixed by supplying the discrete-topology instance, opening the existing
`CategoryTheory.Obj` and `ZeroObject` scopes, fixing the section-ring universes explicitly,
and using the full ObjectProperty class names. No theorem was proved during this stage.

## Second reading by Q92

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
