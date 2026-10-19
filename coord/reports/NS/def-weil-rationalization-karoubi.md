## Worker report

The module `Sheaf.Paper.SfRationalizationKaroubi` specializes the published raw
`CategoryTheory.ScalarLocalization` to `sfIntegralConstructibleCategory`. It keeps
exactly the integral objects, localizes each Hom by the coefficient uniformizer, uses
the recorded triangulated scalar-localization datum, and defines the canonical
localization functor and its shift and triangulated structures. The coefficient
localization is identified with `E` by `sfRationalCoefficientEquiv`; the postponed
Hom-coordinate theorem states the unique additive map sending every pure tensor
`a ⊗ₜ f` to `f ⊗ₜ φ(a)`. The postponed scalar-extension theorem states the unique
additive functor whose object map is the completed integral extension and whose pure
morphism tensors are sent through the coefficient embedding. The final abbreviation
retains the source's finite-field parameter only as an unused global datum and imposes
no relation between it and `Y`; there is no Karoubi completion.

The declaration `sfRationalConstructibleCategory` renders the source's
`D^b_c(Y,O_E)[1/varpi_E]`: its objects are `ScalarLocalization` wrappers of
`sfIntegralConstructibleCategory l E Y`, and its Hom is the tensor with
`Localization.Away (coefficientExtensionUniformizer l E)`. The triangulation datum,
zero, shift, additive shifts, localization functor, CommShift, pretriangulation,
triangulation, and exact localization are direct projections of
`ScalarLocalization.exists_triangulated_scalarLocalization`; hence every image-triangle
clause and the induced shift clause is retained. `sfRationalCoefficientEquiv` is the
recorded localization equivalence, so the `E = Q_l` case is included by the existing
Padic coefficient-ring definitions. `sfRationalScalarExtension_existsUnique` binds
finite-dimensional coefficient fields `E,L`, an algebra embedding `ι`, arbitrary
scheme `Y`, and `p` with `l ≠ p`; its three conjuncts are additivity, the specified
object map, and the specified pure-tensor morphism map. `FiniteFieldDatum.sfRationalCategory`
forwards to this intrinsic category and does not add a scheme/base-field hypothesis.

Dependency declarations used:

* `Sheaf.Paper.SfIntegralConstructibleLinear`,
  `WeilConjectures.sfIntegralConstructibleCategory` and its inherited linear action.
* `Sheaf.Paper.IntegralScalarExtension`,
  `WeilConjectures.integralScalarExtension`.
* `Sheaf.CategoryTheory.ScalarLocalization`,
  `CategoryTheory.ScalarLocalization` and `ScalarLocalization.localization`.
* `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`,
  `CategoryTheory.ScalarLocalization.exists_triangulated_scalarLocalization`.
* The already published dependency module
  `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`, providing
  `WeilConjectures.sfIntegralScalarExtension_constructible`,
  `sfConstructibleIntegralScalarExtension`, and
  `sfConstructibleIntegralScalarExtension_smul` (the owning module uses the first two
  in the scalar-extension specification).

Edge cases checked: zero and empty-scheme objects are allowed by the full-subcategory
and scalar-localization constructions; all integer shifts are available; no `n = 0`,
finite-type, algebraically closed, or finite-field condition on `Y` was introduced;
the identity coefficient embedding is allowed; and `E = Q_l` uses the existing
uniformizer/localization equivalence.

Searches for an existing owning declaration: `msearch.py leanfinder` with
“rationalization of an integral constructible derived category by tensoring Hom
modules with the fraction field, without idempotent completion” returned only generic
localization results; `msearch.py loogle` with
`CategoryTheory.ScalarLocalization, WeilConjectures.sfRationalConstructibleCategory`
returned no matching declaration; grep of Mathlib `CategoryTheory` for
`ScalarLocalization|rationalConstructibleCategory` found no match; and `rg` over
`WeilConjectures/` and shared `lean/Sheaf` found no prior owning declaration for
`sfRationalConstructibleCategory`. The source blueprint explicitly says no Karoubi
completion, so Mathlib's Karoubi envelope is not the same notion. The same searches
found the already landed intrinsic dependency module and its three declarations, which
are imported and reused.

The returned-delivery collision was repaired by deleting the side module
`Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsicRepair` and its copied
dependency node, then importing and reusing the already published
`Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`. The three colliding names
are therefore declared exactly once. The item statement and its `stmt_deps` were not
changed.

## Earlier second reading (a previous round; superseded)

I reread the source node `def-weil-rationalization-karoubi` at order 1460 in
`sk-def-sf-operations/def-weil-rationalization-karoubi.md`, then checked every clause
against the delivered declarations.

1. The source fixes the global finite-field datum, a prime `l ≠ p`, a finite extension
   `E / Q_l`, a scheme `Y`, and a chosen uniformizer. `FiniteFieldDatum.sfRationalCategory`
   binds the datum and the inequality, while `sfRationalConstructibleCategory` binds
   `l` with `Fact l.Prime`, `E` with `[Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`, and arbitrary `Y`. The canonical
   `Padic.coefficientExtensionUniformizer` is the chosen uniformizer from the coefficient
   dependency. Verdict: all source hypotheses are represented; no finite-type or relation
   between `Y` and the finite field is added.
2. The integral category `D^b_c(Y,O_E)` built from finite torsion reductions is rendered
   by `sfIntegralConstructibleCategory l E Y`, through the recorded intrinsic
   `sfIntegralConstructible` predicate. Verdict: same object and finite-level predicate.
3. The required `O_E`-linear triangulated input is supplied by
   `SfIntegralConstructibleLinear` and its inherited triangulated structure. Verdict:
   the linear action and shift assumptions are exactly those used by the localization
   theorem.
4. `sfRationalConstructibleCategory` is the raw `ScalarLocalization` with unchanged
   objects and Hom module `Localization.Away(varpi) ⊗[O_E] Hom`. The canonical
   coefficient equivalence `sfRationalCoefficientEquiv` and the postponed unique
   `sfRationalHomCoordinates_existsUnique` identify this with the source's
   `Hom ⊗[O_E] E` coordinates, sending `a ⊗ f` to `f ⊗ φ(a)`. Verdict: the tensor
   order is canonically transported and the specified pure-tensor formula is retained.
5. The induced shift, zero, pretriangulation, triangulation, image-triangle
   characterization, and exact localization are the projections of
   `ScalarLocalization.exists_triangulated_scalarLocalization` in
   `sfRationalTriangulationDatum`. Verdict: every triangulated clause and the exact
   localization functor `sfRationalConstructibleLocalization` is present.
6. The source explicitly takes no Karoubi completion. The delivered category is the raw
   scalar-localization structure and introduces no idempotent objects or retract data.
   Verdict: exact.
7. For finite coefficient extension `E ⊂ L`, the theorem
   `sfRationalScalarExtension_existsUnique` binds the common prime, `l ≠ p`, both finite
   coefficient fields, and an algebra embedding `ι : E →ₐ[Padic l] L`. Its conjuncts
   state additivity, the completed integral object map, and the required pure-tensor
   morphism map; `sfRationalScalarExtension` and its additive instance select that unique
   functor. Verdict: same scalar-extension construction and action; finite-dimensionality
   over `Padic l` together with the embedding supplies the finite extension relation.
8. The `E = Q_l` case is covered by the existing Padic coefficient extension integers
   and uniformizer; the final `FiniteFieldDatum.sfRationalCategory` keeps the source's
   global convention without imposing extra structure on `Y`. Verdict: exact.

Edge cases checked: `Y` may be empty and objects may be zero because the full-subcategory
and raw localization constructions impose no nonemptiness; the index of shifts is all
`ℤ` (including zero); no `n = 0` hypothesis or finite-type/Noetherian condition is
introduced; the characteristic restriction is only `l ≠ p` in the global wrapper and
scalar transition; and all category and scheme universes are the shared `u` required by
the recorded intrinsic category. The identity coefficient embedding is allowed.

The published dependency declaration was checked at
`lean/Sheaf/Paper/IntegralScalarExtensionConstructibleIntrinsic.lean`: its theorem,
restricted functor, and linearity theorem have the exact intrinsic signatures used by
the target. No duplicate repair declarations remain, and the target imports that module
directly. `scompile.py` compiled the target module cleanly; only the expected `sorry`
warning occurs for the postponed target theorems.

## Second reading by NS

I reread the node `def-weil-rationalization-karoubi` at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-rationalization-karoubi.md`,
order 1460, and matched every introduced object, hypothesis, and conclusion clause with
`lean/Sheaf/Paper/SfRationalizationKaroubi.lean`.

1. The global datum, prime, coefficient field, scheme, and uniformizer are rendered by
   `FiniteFieldDatum.sfRationalCategory D l [Fact l.Prime] hl E Y` and the intrinsic
   `sfRationalConstructibleCategory l E Y`. The wrapper binds `hl : l ≠ D.p`; the
   intrinsic category deliberately has no unused finite-field or finite-type hypothesis.
   `Padic.coefficientExtensionIntegers l E` and
   `Padic.coefficientExtensionUniformizer l E` are the recorded valuation ring and
   chosen uniformizer. Verdict: all source data is present, with no extra hypothesis.
2. The integral category built from the finite torsion reductions is rendered by
   `sfIntegralConstructibleCategory l E Y`, whose predicate is the recorded intrinsic
   `sfIntegralConstructible`. The dependency modules
   `SfIntegralConstructibleTriangulated` and `SfIntegralConstructibleLinear` supply the
   triangulated category, the `Padic.coefficientExtensionIntegers`-linear action, and
   linear integer shifts. Verdict: the current intrinsic predicate and its exact
   inherited structure are used; the obsolete finite-field-specialized category is not.
3. The raw rationalization is the abbreviation
   `ScalarLocalization (Padic.coefficientExtensionIntegers l E)
   (sfIntegralConstructibleCategory l E Y)
   (Padic.coefficientExtensionUniformizer l E)`. Its objects are wrappers of exactly the
   integral objects and its Hom type is
   `Localization.Away varpi ⊗[O_E] (K.obj ⟶ M.obj)`. The canonical additive equivalence
   `sfRationalHomCoordinates K M` identifies this scalar-first tensor with the node's
   Hom-first `(K.obj ⟶ M.obj) ⊗[O_E] E`, and its defining theorem sends
   `a ⊗ f` to `f ⊗ sfRationalCoefficientEquiv a`. Verdict: the displayed Hom formula is
   retained through the canonical tensor symmetry and the coefficient localization
   equivalence; no second localization category is introduced.
4. The induced shift, zero object, additive shifts, localization functor, CommShift,
   pretriangulation, triangulation, image-triangle characterization, and exactness are
   the projections in `sfRationalTriangulationDatum` from
   `ScalarLocalization.exists_triangulated_scalarLocalization`. Verdict: every
   triangulated clause and the exact functor from the node is present, including the
   characterization by triangles isomorphic to localized distinguished triangles.
5. The abbreviation `FiniteFieldDatum.sfRationalCategory` preserves the source's global
   finite-field convention and adds no relation between `D` and `Y`; there is no Karoubi
   envelope, idempotent completion, or formally adjoined retract. Verdict: the explicit
   “no Karoubi completion” clause is exact.
6. For coefficient extension, `sfRationalScalarExtension_existsUnique` binds `p`,
   `hl : l ≠ p`, finite coefficient fields `E,L`, and an algebra embedding
   `ι : E →ₐ[Padic l] L`. Its three conjuncts are additivity, the object map through
   `sfConstructibleIntegralScalarExtension`, and the pure-tensor morphism formula using
   `sfRationalCoefficientEquiv` and `ι`; `sfRationalScalarExtension` selects that unique
   functor. Verdict: this is the node's integral representative extension followed by
   rationalization, with the stated action on `f ⊗ a`, and the identity embedding remains
   allowed.

Edge cases were checked against the source. The full-subcategory and raw localization
allow the zero object and an empty scheme; no nonemptiness or finite-type condition on
`Y` is imposed. All integer shifts, including shift zero, are available. The only
characteristic restriction is the source's `l ≠ p` in the global wrapper and scalar
transition. `E = Q_l` is covered by the existing Padic coefficient-extension integers,
uniformizer, and localization equivalence. The shared scheme and coefficient universe
`u` is sufficient for the intrinsic category and does not remove any source case.

I repeated the three required searches. `msearch.py` LeanFinder for a rationalized
constructible category with localized Hom tensors returned only generic localization
declarations; the Loogle query combining `CategoryTheory.ScalarLocalization` with
`sfRationalConstructibleCategory` returned no owning declaration. `rg` over Mathlib,
`WeilConjectures/`, and the shared `lean/Sheaf` found no prior owning declaration.
Mathlib's Karoubi envelope declarations were inspected and rejected because the source
explicitly says that no idempotent completion is taken. The recorded intrinsic
dependency module `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic` was opened
and its preservation theorem, restricted functor, and scalar-linearity theorem match the
uses above; no duplicate repair module remains.

No statement mismatch was found, so the node statement and `stmt_deps` were left
verbatim unchanged. The only repair being reviewed is the maintenance invalidation repair:
the old specialized `boundedConstructibleDerivedCompleteIntegralCategory` interface was
replaced by the intrinsic `sfIntegralConstructibleCategory`, while the published generic
localization and intrinsic scalar-extension interfaces are reused. The module compiled
cleanly with `python3 /home/ubuntu/weil-launcher-nt/scompile.py NS
def-weil-rationalization-karoubi lean/Sheaf/Paper/SfRationalizationKaroubi.lean`; only
the expected `sorry` warnings for postponed statements occur.
