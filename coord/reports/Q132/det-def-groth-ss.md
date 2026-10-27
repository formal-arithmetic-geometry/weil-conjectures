## Worker report

This is an `existing: true` attachment of the entire definition/construction node
`det-def-groth-ss`. No Lean module, definition, theorem, or proof is added. The
node's statement, dependencies, proof, and other fields are unchanged; only its
`lean` record is supplied. The source read is the current blueprint,
`literature/blueprint/latest/blueprint/sec-picard-framework/sk-thm-picard-perfect/det-def-groth-ss.md`.
There is no repair note for this item.

The existing declarations are spread across upstream modules. The main record
binds `CategoryTheory.Functor.IsAcyclicComposablePair` in
`WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`; its `declarations`
list also contains the two spectral-sequence definitions exposed by that module.
The record's note explicitly gives the modules and names for the other clauses,
which must be imported when using those clauses. This does not treat the first
paragraph alone as the whole item. In particular, the double-complex constructions
below, including the exact couples and BOTH filtration formulas, are part of the
attachment. The separate server probe imports both main modules and checks every
one of these declarations together.

Clause-by-clause comparison with the node:

1. The categories and additive functors are those of the variables immediately
   before `Functor.IsAcyclicComposablePair`: `A : Type u₁`, `Category.{v₁} A`,
   `Abelian A`, `IsGrothendieckAbelian.{v₁} A`, and similarly for B; C has only
   `Category.{v₃} C` and `Abelian C`. Object and morphism universes are independent.
   The signature has `(F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]`.
   No finite-limit-preservation or left-exactness assumption occurs in this
   definition. Later Grothendieck spectral sequence theorems in the same file
   do impose left exactness; those later theorems are NOT the attachment.
2. G-acyclicity is expressed directly by
   `∀ q : ℕ, 0 < q → IsZero ((G.rightDerived q).obj B)`.
   The pair predicate is exactly
   `∀ (I : A) [Injective I] (q : ℕ), 0 < q →
     IsZero ((G.rightDerived q).obj (F.obj I))`.
   Thus it quantifies over every injective object and every positive derived
   degree, without requiring G itself to be exact. Mathlib's
   `InjectiveResolution.isoRightDerivedObj` computes `rightDerived` using any
   injective resolution, for arbitrary additive functors. Grothendieck categories
   have enough injectives by the standard imported Mathlib instance. Degree zero
   is not constrained, and `R⁰v = v` is not asserted.
3. The first-quadrant E₂ input is
   `E : CategoryTheory.E₂CohomologicalSpectralSequenceNat C`.
   Mathlib's abbreviation uses `SpectralSequence C` with page shapes
   `ComplexShape.spectralSequenceNat ⟨r, 1-r⟩` and starting page 2.
   In `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic`,
   `SpectralSequence.pageInfinity (E : E₂CohomologicalSpectralSequenceNat C)
     (pq : ℕ × ℕ) : C := (E.page (pq.1 + pq.2 + 2 : ℕ)).X pq`.
   This is precisely the node's chosen stable page, including `(p,q)=(0,0)`.
   For r ≥ p+q+2, the outgoing target has negative second coordinate and the
   incoming source has negative first coordinate. No degeneration assumption
   is added.
4. In that same module,
   `structure SpectralSequence.Abutment (E : E₂CohomologicalSpectralSequenceNat C)
     (H : ℕ → C)` has `filtration (n p : ℕ) : Subobject (H n)`.
   `filtration_succ_le` is the decreasing condition,
   `filtration_zero n : filtration n 0 = ⊤` renders `F⁰Hⁿ=Hⁿ`, and
   `filtration_succ_self n : filtration n (n+1) = ⊥` renders `Fⁿ⁺¹Hⁿ=0`.
   For every `n p q : ℕ` and `hpq : p+q=n`, `nonempty_gradedIso` supplies
   `Nonempty (cokernel (Subobject.ofLE _ _ (filtration_succ_le n p)) ≅
     E.pageInfinity (p,q))`.
   A quotient of subobjects in an abelian category is this cokernel, so the
   direction and all indices of the displayed graded-piece isomorphism agree.
   The node asks that such isomorphisms exist, rather than choosing bases or
   preferred identifications; `Nonempty` is exactly that clause.
5. For the final paragraph, the existing first-quadrant input is
   `K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)`.
   This represents all first-quadrant double complexes: restriction to the
   nonnegative quadrant loses only zero objects. `K.extendNat` explicitly extends
   by zero to integer indices. `K.isZero_extendNat_X_X` verifies the zero region,
   and `K.totalExtendNatHomologyIso n` identifies the total cohomologies. Thus
   using natural-number indices does not assume extra boundedness or discard
   negative-degree data that the node allows to be nonzero.
6. `HomologicalComplex₂.columnFiltration`, in
   `WeilConjectures.Algebra.Homology.ExactCouple.TotalComplexFiltration`, is a
   `DecreasingFiltration (K.total (ComplexShape.up ℤ))` with
   `F p := Subobject.mk (K.totalιColumnsGE p)`. Here `columnsGE` is the actual
   column truncation and `totalιColumnsGE` is its total inclusion. It therefore
   implements the sum of columns of index ≥ p as a subcomplex of the total.
   The differential is `d_I + (-1)^p d_II`, as in the recorded total-complex
   dependency. No arbitrary replacement filtration is introduced.
7. `CategoryTheory.DecreasingFiltration.exactCouple`, in
   `WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex`, constructs
   the actual exact couple of this filtration. Its fields are
   `D i := (F.piece i.1).homology i.2`,
   `E i := (F.gr i.1).homology i.2`, and inclusion, boundary, quotient maps
   `coupleα`, `couplef`, `coupleg`. All three zero-composite and exactness fields
   come from the cohomology long exact sequence of `F.ses p`.
   In these (filtration,total-degree) coordinates the degrees are (-1,0),
   (1,1), and (0,0). In the node's cohomological coordinates n=p+q they are
   (-1,1), (1,0), (0,0). Reindexing further by (P,Q)=(p+n,-p)=(2p+q,-p)
   gives (-1,1), (2,-1), (0,0), precisely the recorded
   `BigradedExactCouple` convention. This invertible change has inverse
   p=-Q, n=P+Q, q=P+2Q; it changes no objects or exactness requirements.
   The general `ExactCouple` API and the recorded `BigradedExactCouple` API
   are two existing presentations, not a new private definition.
8. `CategoryTheory.ExactCouple.derivedIter` and `.spectralSequence`, in
   `WeilConjectures.Algebra.Homology.ExactCouple.Basic`, explicitly iterate the
   derived couples. In `WeilConjectures.Algebra.Homology.ExactCouple.FirstQuadrant`,
   `.firstQuadrantSpectralSequence` starts at E₂ and reindexes the (r-1)-st
   derived couple by (p,q) ↦ (p,p+q). In
   `WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex`,
   `K.firstSpectralSequence` is DEFINED as
   `K.extendNat.columnFiltration.exactCouple.firstQuadrantSpectralSequence
     K.extendNat_columnFiltration_isFirstQuadrant`.
   Thus this is the node's exact-couple construction, not merely an existential
   spectral sequence with a matching E₂-page. Applying the same construction
   to `K.flip` gives the second sequence.
9. In the same DoubleComplex module,
   `K.firstSpectralSequenceAbutment :
     K.firstSpectralSequence.Abutment (fun n ↦ (K.total (up ℕ)).homology n)`
   is real data built from the canonical filtered-couple abutment.
   `K.firstSpectralSequenceAbutment_filtration (n p : ℕ)` states exactly
   `K.firstSpectralSequenceAbutment.filtration n p =
     imageSubobject (HomologicalComplex.homologyMap
       (K.extendNat.columnFiltration.F p).arrow n ≫
         (K.totalExtendNatHomologyIso n).hom)`.
   The comparison just changes from the extended total to the original total.
   This is precisely the requested cohomological image filtration.
10. Also in DoubleComplex,
    `K.flipFirstSpectralSequenceAbutment :
      K.flip.firstSpectralSequence.Abutment (fun n ↦ (K.total (up ℕ)).homology n)`
    transports the second sequence's abutment along `K.totalFlipIso`.
    `K.flipFirstSpectralSequenceAbutment_filtration (n p : ℕ)` states its
    filtration is
    `imageSubobject (HomologicalComplex.homologyMap
      (K.flip.extendNat.columnFiltration.F p).arrow n ≫
        (K.flip.totalExtendNatHomologyIso n).hom ≫
          HomologicalComplex.homologyMap (K.totalFlipIso (up ℕ)).hom n)`.
    Thus it is the filtration by the second degree on the same total cohomology.
    The signed total-flip isomorphism has diagonal sign (-1)^(pq), preserves
    the row summands, and implements the necessary total-differential convention.
    Nothing identifies the two filtrations with each other.
11. The finite-endpoint and convergence clauses are included in these abutment
    objects. Specifically `columnFiltration_convergesTo`,
    `columnFiltration_homologyFiltration_F_zero`, and
    `columnFiltration_homologyFiltration_F_succ` in TotalComplexFiltration give
    convergence and the two stated endpoints for any integer-indexed
    first-quadrant bicomplex. Only finite diagonal coproducts are required;
    C is not assumed Grothendieck and has no countable-coproduct assumption.

Dependency declarations read:

- `def-sp-grothendieck-abelian`: Mathlib module
  `CategoryTheory.Abelian.GrothendieckCategory.Basic`, declaration
  `CategoryTheory.IsGrothendieckAbelian`, including its colimit and injective
  consequences in the corresponding Mathlib files.
- `def-sp-injective-resolutions`: Mathlib modules
  `CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`, declarations
  `CategoryTheory.Injective` and `CategoryTheory.InjectiveResolution`; the
  comparison `InjectiveResolution.isoRightDerivedObj` is in
  `Mathlib.CategoryTheory.Abelian.RightDerived`.
- `lem-weil-pbc-right-derived-plus-injective`: Mathlib
  `Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`, declarations
  `CategoryTheory.Functor.rightDerivedFunctorPlus` and
  `rightDerivedFunctorPlusUnit`, with its right-derived-functor instance;
  the invertibility on injective complexes is in
  `Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`.
  The existing acyclicity definition uses Mathlib's ordinary `rightDerived`,
  whose resolution comparison supplies exactly the individual R^q objects.
- `def-weil-abstract-derived-category`: Mathlib
  `Algebra.Homology.DerivedCategory.Basic`, `HasDerivedCategory` and
  `DerivedCategory`, with `DerivedCategory.Q` the localization. No custom
  localization is used in this attachment.
- `def-sp-spectral-sequence`: Mathlib
  `Algebra.Homology.SpectralSequence.Basic`, `CategoryTheory.SpectralSequence`,
  its `page`, `iso`, and `Hom` fields, and the E₂ first-quadrant abbreviation.
- `def-sp-filtration`: upstream
  `WeilConjectures.CategoryTheory.Abelian.Filtration`,
  `CategoryTheory.DecreasingFiltration` and `.gr`. Both the filtered-complex
  and cohomological constructions use these canonical subobjects/cokernels.
- `def-sp-double-complex-total`: the recorded upstream
  `WeilConjectures.CategoryTheory.DoubleComplexTotal` supplies the total and
  the first and second degree filtrations and their bounds. Its step objects
  are packaged as `PBCDecreasingFiltration`. The existing column-truncation
  construction above implements the same subcomplexes, using the canonical
  `DecreasingFiltration` API; this attachment does not copy either definition.
- `def-sp-exact-couple`: recorded upstream
  `WeilConjectures.CategoryTheory.ExactCouple`,
  `CategoryTheory.BigradedExactCouple` and its derived/page API. The coordinate
  conversion in clause 7 explains precisely its relation to the already
  constructed filtered exact couple. No missing hypothesis or interface
  repair is needed to use the existing construction.

Edge cases checked by reading the formulas and types:

- At (p,q)=(0,0), the selected stable page is E₂, and an abutment has the
  single nonzero quotient H⁰/0. There is no positive-degree restriction on H.
- The zero bicomplex has zero total and both filtrations zero, hence top=bottom;
  this satisfies both endpoints, with no nontriviality assumption.
- A bicomplex supported at (1,0) shows why the two filtrations must be distinct:
  the first filtration's degree-one H¹ step is all H¹, whereas the second's
  degree-one step is zero. The two separate formulas above retain this case.
- A complex supported at (0,1) gives the exchanged check. A term at (0,0)
  tests the degree-zero endpoints and no off-by-one in pageInfinity.
- Unbounded first-quadrant bicomplexes are allowed: each total diagonal is
  finite but no common bound on all diagonals is imposed.
- General abelian C is permitted even without infinite coproducts; only the
  first two categories of the acyclicity paragraph must be Grothendieck.
- The pair predicate allows arbitrary additive F and G, including ones that
  are not left exact; its definition does not invoke the later existence
  theorem for the Grothendieck spectral sequence.

Searches performed (2026-10-24):

- `msearch.py ... leansearch` with "The spectral sequence of a first quadrant
  double complex converges to the cohomology of its total complex": eight
  Mathlib results, headed by `HomologicalComplex₂.total` and its differential
  lemmas; none alone contains the full compound item.
- `msearch.py ... leanfinder` with "A pair of additive functors sends injectives
  to acyclic objects and both spectral sequences of a first quadrant double
  complex abut by the image filtration": eight results, including
  `Functor.isZero_rightDerived_obj_injective_succ` and injective-resolution
  lemmas; these support the ingredients, not the whole compound item.
- `msearch.py ... loogle` with "CategoryTheory.SpectralSequence,
  HomologicalComplex₂.total": zero hits; retry with
  "CategoryTheory.SpectralSequence": twelve hits, including the spectral
  sequence structure, pages, Hom, and successor-page isomorphisms.
- `msearch.py ... grep` with
  `IsAcyclicComposablePair|pageInfinity|Abutment|columnFiltration`: no Mathlib
  hits for the upstream additions. Direct `rg` of Mathlib finds the spectral
  sequence, injective resolutions and arbitrary-additive derived functors.
- `rg` of `lean/WeilConjectures` finds IsAcyclicComposablePair in
  CategoryTheory/SpectralSequence/Grothendieck.lean, the stable-page/abutment
  definitions in Mathlib/Algebra/Homology/SpectralSequence/Basic.lean, and all
  five double-complex definitions/formulas in
  Algebra/Homology/ExactCouple/DoubleComplex.lean and TotalComplexFiltration.lean.
  Full source signatures, docstrings, and construction bodies were read.
- `grep -rn det-def-groth-ss lean/WeilConjectures` has no literal-id hit.
  The identical blueprint copy `sk-def-groth-ss` DOES occur on these exact
  declarations. The node already records that copy in `blueprint.same_as`.
  `dag/lean_names_upstream.json` also records its upstream names.
- `rg` of `lean/Sheaf` finds consumers of the existing pair predicate in
  GrothendieckSpectralSequence, GrothendieckCanonicalImageFiltration and
  CartanEilenbergSecondImageTruncation, rather than another definition of the
  whole item. No second definition was written.

No statement correction, new node, dependency module, or disputed statement.
The inherited ATTACH finding was completed by verifying the final paragraph,
not used as a reason to stop without delivery. The example
`Sheaf.CategoryTheory.CompactObject` is currently withdrawn and contains no
active declaration; its old node record was read, and the current upstream
module conventions were used for the scratch compilation probe.

Validation: a separate module-mode probe imports both
`WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck` and
`WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex` and checks all
sixteen named construction/filtration declarations. It is scratch only, not
part of the delivery. The delivery wrapper also checks the three declarations
listed in the main record. The prescribed dry run and final delivery run the
server preflight and compilation against the live published library.

## Second reading by Q132

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
