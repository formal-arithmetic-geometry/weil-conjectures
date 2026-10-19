## Worker report

The delivery defines the four coefficient cohomology functors, and supplies seven existing
DAG prerequisites that had no usable Lean declaration. The item's statement text is unchanged.
The primary declaration is `DerivedCategory.coefficientCohomologyModules` in
`Sheaf.Paper.CoefficientCohomologyModules`; it returns the four actual functors for the
blueprint's specified global datum, finite subextension and positive finite level.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Global finite-field datum p,a,q,k0,k | `D : WeilConjectures.FiniteFieldDatum.{u}`, using its existing structure unchanged. |
| Prime ell different from p, and fixed algebraic closure Qbar of Q_ell | `c : D.CoefficientDatum`; `c.prime`, `c.different`, `c.field`, `c.algebra`, `c.isAlgClosure` are the recorded datum's fields/instances. |
| A finite extension E inside Qbar | `E : Padic.FiniteCoefficientFields c.l c.Qbar`; its underlying field is `E.val`, and finite dimensionality over `Padic c.l` is the recorded instance. |
| Valuation ring and chosen uniformizer | The existing `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer` constructions; the uniformizer ideal is `Padic.coefficientExtensionIdeal c.l E.val 1`. No new choices of these data. |
| Positive finite coefficient level n and A_{E,n} | `(n : ℕ) (_hn : 1 ≤ n)` and the actual `Padic.coefficientExtensionRing c.l E.val n`. |
| Arbitrary ring R, complex in D(R), integer degree i | Mathlib's `DerivedCategory (ModuleCat R)` and `DerivedCategory.homologyFunctor (ModuleCat R) i`; every degree argument is `i : ℤ`. The generic functor is reused, not defined again. |
| H^i = kernel / image of a representing complex; canonical independence | The existing `DerivedCategory.homologyFunctorFactors` and `ShortComplex.moduleCatHomologyIso`; the latter identifies the abstract homology with the kernel modulo the differential's image. Localization at quasi-isomorphisms is the existing `DerivedCategory.Q`. |
| D^b_fin(A), with bounded finite cohomology | `(pointFiniteCohomology A).FullSubcategory`: a finite support `Finset ℤ`, `IsZero` outside it, and `Finite` of every cohomology module. |
| D^b_fg(O_E), including the source's derived completeness | `(pointFgComplete R I).FullSubcategory`: the same boundedness, `Module.Finite` of every cohomology, and the existing `DerivedCategory.IsDerivedComplete I K`. Specialize R and I as above. Completeness is retained. |
| D^b_fd(E), realized inside D(E) | `(pointFiniteDimensional E.val).FullSubcategory`: bounded cohomology and `FiniteDimensional E.val` in every degree. This does not substitute the category `DerivedCategory (FGModuleCat E)`. |
| H^i on each of these three categories | `coefficientFiniteCohomology`, `coefficientFgCohomology`, `coefficientFdCohomology` are composition of the exact full-subcategory inclusion with Mathlib's ordinary homology functor. Their three `_finite` statements express the stated finiteness clauses. |
| Stagewise objects (E',C') | `PointFdQbar` has exactly the sigma type of a finite coefficient field and an object of its D^b_fd. |
| Common-stage Hom colimits and their composition | The induced-category implementation realizes these Hom sets in D(Qbar). `pointFdQbarCocone_isFilteredTwoColimit` states the canonical common-stage surjectivity and eventual-equality criterion using upstream `CategoryCocone.IsFilteredTwoColimit`; these identify the realized Homs with the prescribed filtered colimits. Composition is composition in D(Qbar), which the canonical transition functors preserve. This is an identity-on-objects realization of the source's common-stage category, not a hypothesis on a supplied arbitrary category. |
| Stagewise H^i(C) = H^i(C') tensor_{E'} Qbar | `coefficientQbarCohomology` uses `Functor.copyObj` with actual object `(ModuleCat.extendScalars E'.val.subtype).obj ((homologyFunctor _ i).obj C'.obj)`. Mathlib orders the tensor factors Qbar tensor H; the tensor commutor gives the displayed ordering. |
| Qbar cohomology is finite-dimensional | `coefficientQbarCohomology_finite`. The finite-dimensionality at the stage is in the object's membership proof; base change preserves it. |
| Change of stage E' subset L | Actual `fieldDerivedScalarExtension` and its restriction `pointFdScalarExtension` are Mathlib's exact `Functor.mapDerivedCategory` of `ModuleCat.extendScalars`. Their defining factorization on representing complexes is the existing `mapDerivedCategoryFactors`. |
| Canonical identification after change of stage | `coefficientCohomologyChangeStage`: first the uniquely normalized `fieldDerivedHomologyIso`, then `ModuleCat.extendScalarsComp` in its tower direction. `coefficientQbarCohomology_changeStage` states that this is precisely the functor's action on the canonical stage-identification isomorphism. |
| A common-stage morphism induces its Qbar-linear map; functoriality | `coefficientQbarCohomology` is a real functor; `coefficientQbarCohomology_map_stage` states its value on any common-stage representative, exactly scalar extension of the ordinary cohomology map. Maps live in `ModuleCat Ω`, hence are Ω-linear. |

The tuple `coefficientCohomologyModules` specializes all generic constructions to the exact
four coefficient categories in the node. No extra cohomological boundedness, projectivity,
perfectness, Tor-amplitude, chosen comparison map, or flatness hypothesis is supplied by the
caller. Exactness follows from the existing field scalar-extension APIs. Only proofs are
postponed. In particular, the derived tower and cohomology natural isomorphisms are chosen
from **unique** existence statements whose value on every `Q C` is explicitly prescribed
by the ordinary termwise tensor maps. These are not arbitrary `Nonempty` isomorphisms.

The original `def-weil-finite-coefficient-point` also introduces geometric-point fibre
functors. Those functors are not needed to define cohomology of coefficient complexes.
Their target categories are supplied here by their already existing genuine DAG child
nodes, added to `stmt_deps` under the 2026-10-16 missing-prerequisite authorization. The
original dependency is retained. No fibre functor or sheaf-coefficient category is copied.

### Dependencies reused

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  `CoefficientDatum`, including all field and prime conditions.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its construction import):
  the existing coefficient rings, integer rings, uniformizer and ideals.
* `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`
  and `finiteCoefficientField_finiteDimensional`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
* `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`.
* `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` and `.Descent`:
  `ModuleCat.extendScalars`, `extendRestrictScalarsAdj`, `extendScalarsComp`,
  `extendScalarsId`, `preservesFiniteLimits_extendScalars_of_flat`.
* `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, and their existing
  shift/triangulated instances.
* `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:
  `ShortComplex.homologyFunctorIso`, providing the genuine cycle-class comparison.
* `Sheaf.RingTheory.DerivedCompleteModuleComplex`: `DerivedCategory.IsDerivedComplete`.
* `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`;
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional`.
* `WeilConjectures.CategoryTheory.FilteredTwoColimit`: `CategoryCocone` and
  `CategoryCocone.IsFilteredTwoColimit`, read from the side framework's exact source.
* `Mathlib.CategoryTheory.InducedCategory`, `.NatIso`, `.Shift.Basic` and
  `.Shift.CommShift`: the induced faithful category, `Functor.copyObj`, and the actual
  coherent shift transported through the faithful realization.

### Edge cases

All degrees are integers, including negative and zero degrees. Finite support is allowed
to be empty, so zero/acyclic complexes are included. There is no chosen lower or upper
bound, so arbitrary bounded amplitude is included. There is no nonzero-cohomology
condition. The integral ideal can be zero in the generic interface, and its actual
coefficient specialization is the uniformizer ideal. Positive finite level includes
n=1; no n=0 exception is silently used. E may be the least finite subextension, and
stage change may be the identity or an arbitrary inclusion. Empty finite-dimensional
spaces and zero morphisms are allowed. Both algebraic closures and the finite-field
datum are the existing arbitrary choices, not replaced by standard representatives.
The stagewise category has all stage pairs; it does not select a preferred finite stage.
All universe variables and declaration variables are explicitly bound; no auto implicits.

### Searches

All searches used the prescribed msearch wrapper or read-only source/DAG searches.

* LeanFinder: “cohomology modules of bounded finite dimensional derived complexes and
  scalar extension to algebraic closure through finite subextension stages”; eight
  unrelated group-cohomology/Ext hits, no exact statement.
* LeanFinder: “bounded derived category of vector spaces with finite dimensional
  cohomology and cohomology scalar extension to an algebraic closure”; eight Ext/group
  cohomology hits (`groupCohomologyIsoExt`, projective/injective resolution comparisons,
  bar/standard resolutions), no coefficient-category or stagewise construction.
* Loogle: `DerivedCategory.homologyFunctor, ModuleCat.extendScalars`; zero hits for
  the combined query. Direct source inspection supplies both exact generic APIs.
* LeanSearch: “cohomology of scalar extension of a complex of vector spaces”; service
  unavailable (Internal Server Error), recorded as unavailable, not as a negative result.
* Mathlib grep via msearch: `homologyFunctor|cancelBaseChange` in
  `Algebra/Homology/DerivedCategory`; twenty generic homology-functor hits, including
  the exact existing ordinary functor and its localization factorization.
* Mathlib grep via msearch: `pointFiniteDimensional|PointFdQbar|bounded.*finite.*cohomology|finite.*dimensional.*cohomology`
  in `Algebra/Homology`; zero matches for the required categories/stagewise functor.
* Read-only rg of Mathlib, WeilConjectures and lean/Sheaf for the new declaration names,
  and the required search for the item id in WeilConjectures: no duplicate names or item
  implementation. Upstream `DerivedCategory.Perfect` characterizes perfect objects over
  a field by bounded finite-dimensional cohomology, but does not supply this stagewise
  coefficient category or this collection of functors. Its generic perfect-object
  predicate is not substituted for the node's explicit cohomology subcategory.
* The DAG already has the seven prerequisite nodes, so they are stated under their
  existing ids, not created as new definition nodes. The server DAG and all delivery
  branch names were checked before writing: no current declaration or delivery for
  the missing point categories, field-complex scalar extension, or cohomology comparison.

No statement correction or STATEMENT-DISPUTED issue was necessary.

## Dependency modules

`def-weil-point-finite-cohomology-complexes`: no Lean record or Mathlib match was available.
`Sheaf.Paper.PointFiniteCohomologyComplexes` defines its exact full-subcategory predicate,
using finite support of cohomology and finiteness of its underlying sets.

`def-weil-point-fg-complete-complexes`: no Lean record or Mathlib match was available.
`Sheaf.Paper.PointFgCompleteComplexes` defines bounded finitely generated cohomology
**and** the already recorded derived-completeness predicate. The general ideal is kept.

`def-weil-point-fd-complexes`: no Lean record or Mathlib match was available.
`Sheaf.Paper.PointFdComplexes` gives the specified realization inside D(F), with finite
support and finite-dimensional cohomology, rather than a category of complexes with
finite-dimensional terms or a separately chosen equivalent category.

`def-weil-finite-dimensional-complex-scalar-extension`: no Lean record or Mathlib match
was available. `Sheaf.Paper.FieldComplexScalarExtension` constructs ordinary scalar
extension descended using the existing exact-functor localization API, then restricts
it to the node's full subcategories. The preservation statement is the corresponding
clause of this existing node. Unit/tower data are supplied by its existing prerequisite
`lem-weil-derived-field-scalar-extension-tower` in the next module.

`lem-weil-derived-field-scalar-extension-tower`: no Lean record or Mathlib match was
available. `Sheaf.Paper.FieldDerivedScalarTower` specifies unique unit and tower natural
isomorphisms, normalized on every representing complex by the exact ordinary tensor
maps. It records associativity, unit coherence and shift compatibility. Its theorem
placeholders are exactly existence, uniqueness and coherence clauses of this node.

`lem-weil-cohomology-commutes-scalar-extension`: no Lean record or Mathlib match was
available. `Sheaf.Paper.FieldCohomologyScalarExtension` reuses the existing short-complex
exact-functor comparison as actual data, uniquely descends it to D(K), and states its
tower compatibility, finite-dimensionality and quasi-isomorphism consequences.

`def-weil-point-fd-qlbar-category`: no Lean record or Mathlib match was available.
`Sheaf.Paper.PointFdQbarCategory` constructs actual stage pairs and uses the canonical
Hom realization in D(Qbar). The common-stage Hom colimit identification is stated as
`pointFdQbarCocone_isFilteredTwoColimit`, with its finite-matrix descent proof plan.
It retains the exact same-stage shifts, their canonical scalar-extension comparison,
a genuine coherent `HasShift`, and the source's finite-stage distinguished-triangle
predicate on triangles of this category. No arbitrary category, morphism or isomorphism
is an input. The identity-on-objects realization is canonically isomorphic to the
literal filtered-colimit-Hom construction, precisely by the stated (Hom) clauses.

### Imports that would form cycles

The scalar-extension definition node cites the cohomology comparison and the derived
tower theorem for its preservation/coherence explanations. Their supplied modules use
`FieldComplexScalarExtension` to name the actual derived scalar-extension functor.
Consequently `FieldComplexScalarExtension` does not import
`Sheaf.Paper.FieldCohomologyScalarExtension` or `Sheaf.Paper.FieldDerivedScalarTower`:
either import would close a cycle. The scalar-extension data itself uses only Mathlib's
exact-functor localization and its ordinary scalar extension. Its preservation proof
can use Mathlib's generic exact-functor homology comparison directly. The main item
imports all three interfaces together. This is the permitted cyclic-proof-import
omission of stages/2-statements.md §3(7); no mathematical dependency is dropped.

### Postponed proofs

Every theorem below has `sorry` as its entire proof and a complete source/proof docstring.
Each belongs to the listed owning DAG node, whose statement contains that assertion:

* `CoefficientCohomologyModules`: `DerivedCategory.coefficientFiniteCohomology_finite`, `DerivedCategory.coefficientFgCohomology_finite`, `DerivedCategory.coefficientFdCohomology_finite`, `DerivedCategory.coefficientQbarCohomology_finite`, `DerivedCategory.coefficientQbarCohomology_map_stage`, `DerivedCategory.coefficientQbarCohomology_changeStage`.
* `FieldCohomologyScalarExtension`: `DerivedCategory.existsUnique_fieldDerivedHomologyIso`, `DerivedCategory.fieldDerivedHomologyIso_tower`, `DerivedCategory.fieldComplexScalarExtension_properties`.
* `FieldComplexScalarExtension`: `DerivedCategory.fieldDerivedScalarExtension_preserves`.
* `FieldDerivedScalarTower`: `DerivedCategory.existsUnique_fieldScalarTower`, `DerivedCategory.existsUnique_fieldScalarUnit`, `DerivedCategory.fieldScalarTower_assoc`, `DerivedCategory.fieldScalarTower_units`, `DerivedCategory.fieldScalarTower_commShift`.
* `PointFdQbarCategory`: `DerivedCategory.pointFdQbarCocone_isFilteredTwoColimit`, `DerivedCategory.pointFd_shift_mem`.

### Validation

All eight delivered modules passed the prescribed scompile.py wrapper, including current
server confirmation, without errors or warnings (maximum observed server file time 4.5 s).
The required deliver2.py --no-push validation printed OK (commit 2583e7e0f0), with
only the intentionally absent independent second-reading section exempted by the tool.
After adding the module-docstring declaration lists, the final dry run is repeated.
The independent second reading and delivery are intentionally left to the next worker.

## Second reading by N7

I reread the node statement (source place: `def-weil-ordinary-compact-cohomology`,
order 1510, with the coefficient-category definitions at `def-weil-finite-coefficient-point`,
order 1509) against `CoefficientCohomologyModules.lean` and each supplied dependency.
The source/node list and verdicts are:

1. The global datum `(p,a,q,k₀,k)` is `D : WeilConjectures.FiniteFieldDatum.{u}`;
   `D` supplies exactly the prime, cardinality, base field, closure field, and algebraic-closure
   structure. Verdict: exact.
2. The coefficient prime `ℓ ≠ p` and fixed algebraic closure `Q̄_ℓ` are the fields of
   `c : D.CoefficientDatum`; `c.different` is the required inequality and its instance
   fields provide `Fact ℓ.Prime`, `Field c.Qbar`, `Algebra (Padic ℓ) c.Qbar`, and
   `IsAlgClosure`. Verdict: exact, with no extra hypothesis.
3. The finite stage `E/ℚ_ℓ` is `E : Padic.FiniteCoefficientFields c.l c.Qbar`;
   its subtype value and recorded finite-dimensionality are used. Verdict: exact.
4. The valuation ring, chosen uniformizer, and uniformizer ideal are
   `Padic.coefficientExtensionIntegers c.l E.val`,
   `Padic.coefficientExtensionUniformizer c.l E.val`, and
   `Padic.coefficientExtensionIdeal c.l E.val 1`. Verdict: exact canonical constructions.
5. The positive level is `(n : ℕ) (_hn : 1 ≤ n)` and
   `Padic.coefficientExtensionRing c.l E.val n` is `A_{E,n}`. Verdict: exact; `n = 1`
   is included and `n = 0` is excluded.
6. The generic ring-level object and degree are represented by
   `DerivedCategory (ModuleCat R)`, `i : ℤ`, and Mathlib's
   `DerivedCategory.homologyFunctor (ModuleCat R) i`. Verdict: exact, including all
   negative and zero degrees.
7. The representing-complex formula `ker(d^i)/im(d^(i-1))` and independence under
   quasi-isomorphism are supplied by `homologyFunctorFactors` and
   `ShortComplex.moduleCatHomologyIso`; no arbitrary representative is chosen. Verdict: exact.
8. `D^b_fin(A_{E,n})` is `pointFiniteCohomology` (finite support and `Finite` cohomology),
   and its cohomology functor is `coefficientFiniteCohomology`. Verdict: exact.
9. `D^b_fg(𝒪_E)` is `pointFgComplete` with
   `Ideal.span {coefficientExtensionUniformizer}` (the `n=1` ideal), including boundedness,
   `Module.Finite`, and `IsDerivedComplete`; `coefficientFgCohomology` is its H^i functor.
   Verdict: exact; completeness is retained.
10. `D^b_fd(E)` is `pointFiniteDimensional E.val`, realized inside the derived category of
    `ModuleCat E.val`, and `coefficientFdCohomology` is the restricted H^i functor.
    Verdict: exact; no replacement by `FGModuleCat` occurs.
11. The stagewise category is `PointFdQbar c.l c.Qbar`; its objects are finite-stage pairs,
    and `pointFdQbarCocone_isFilteredTwoColimit` supplies the canonical common-stage Hom
    colimit realization. Verdict: exact canonical realization of the stated 2-colimit.
12. For a stage object, `coefficientQbarCohomology` has object data
    `ModuleCat.extendScalars ... ((homologyFunctor ... i).obj C')`, i.e.
    `H^i(C') ⊗_{E'} Q̄_ℓ` up to the canonical tensor-factor commutor. Verdict: exact.
13. Its finite-dimensionality is the postponed theorem
    `coefficientQbarCohomology_finite`, using the stage membership and scalar extension.
    Verdict: exact.
14. For `E' ⊂ L`, `coefficientCohomologyChangeStage` composes the normalized
    `fieldDerivedHomologyIso` with `ModuleCat.extendScalarsComp`;
    `coefficientQbarCohomology_changeStage` identifies this with the stage transition.
    Verdict: exact canonical comparison, including identity-stage cases.
15. A common-stage morphism is sent by
    `coefficientQbarCohomology_map_stage` to the scalar extension of its ordinary
    cohomology map, hence to a `Q̄_ℓ`-linear map; functoriality is the actual functor structure.
    Verdict: exact.

Edge cases checked: empty finite support and zero/acyclic objects satisfy the full-subcategory
predicates; the empty and zero cohomology modules are allowed; `i` ranges over all `ℤ`;
`n=1` is allowed and `n=0` is not admitted by the hypothesis; the least finite stage and
identity stage change are allowed; arbitrary finite stages and inclusions are allowed; no
nonzero cohomology, projectivity, flatness, perfectness, or Tor-amplitude assumption was
introduced; all declaration universes are explicitly bound and the stage and closure fields
remain in the same universe as the datum.

Searches repeated: `rg` over Mathlib, `WeilConjectures`, and repository `lean/Sheaf` for
cohomology-module, finite-derived-category, Q̄ℓ stage, and scalar-extension declarations;
`msearch.py` LeanFinder/Loogle queries for bounded finite-dimensional derived cohomology and
cohomology after scalar extension; direct Mathlib inspection of
`DerivedCategory.homologyFunctor`, `homologyFunctorFactors`, and ModuleCat scalar extension.
Only the generic Mathlib homology and scalar-extension APIs were found; no existing declaration
states this coefficient-category collection. The source checkout likewise has no duplicate
implementation.

No mismatch was found, so no Lean or node statement was changed. All seven dependency modules
and the main module compile cleanly with `scompile.py` (no errors or warnings).
