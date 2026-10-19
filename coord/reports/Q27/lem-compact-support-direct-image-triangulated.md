# Stage-2 statement: compactly supported direct image is triangulated

## Worker report

The delivery states `AlgebraicGeometry.ProEtale.compactSupportDirectImage_isTriangulated`
in `lean/Sheaf/Paper/CompactSupportDirectImageTriangulated.lean`. Its proof is only
`sorry`; the docstring carries all four DAG proof steps. No new definition or theorem
besides this statement is supplied. No mathematical statement correction is needed.

The return at immutable head e858c2483bff reported that the maintainer fix reader
could not accept a dependency-node JSON file in `--apply-fixes`. I opened the saved
independent review and its proposed fixes. Its underlying mathematical finding was H4:
the delivered category abbreviation duplicated the already published
`AlgebraicGeometry.ProEtale.ModuleDerivedCategory`. I applied that correction directly
in this sandbox: the theorem imports and uses the existing category, the dependency's
`lean` records that existing declaration, and the redundant module
`ProEtaleConstantModuleDerivedCategory.lean` is removed. This makes the normal delivery
carry the corrected dependency record without a reviewer-side dependency JSON fix.
The former worker and second-reader assertions that the abbreviation was missing were
incorrect and are superseded by this report. A fresh second reading is still required.

I reread the item statement, its four proof steps and all six statement-dependency
records, and opened their recorded declarations. The source unit
`dag/units/sk-def-sf-operations.json`, clause (iv), identifies the compactification
composite and restricts compactification independence to etale-origin objects. This
item concerns each fixed compactification on the ambient unbounded categories; it does
not assert independence. The archived blueprint Markdown is absent from the supplied
checkout; the imported node and unit texts were read, not an unavailable original file.

Every hypothesis and clause has the following Lean rendering:

- Field: `(K0 : Type u) [Field K0]`, with no perfection or closure hypothesis.
- Finite-type schemes over that field: `(X Y : Scheme.{u})`, the two `Over` instances
  over `Spec (CommRingCat.of K0)`, and `LocallyOfFiniteType` plus `QuasiCompact` for
  each structure map. Those two properties are Mathlib's finite-type convention.
- Separated finite-type morphism over the field: `(f : X ⟶ Y)`, `f.IsOver` for the
  same spectrum, and `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
- Prime: `(l : ℕ) [Fact l.Prime]`; invertibility of its image is
  `(_hl : IsUnit (l : K0))`.
- Finite extension of Q_l: `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]`
  and `[FiniteDimensional (Padic l) E]`.
- Positive integer level: `(n : ℕ) (_hn : 1 ≤ n)`.
- Coefficients: exactly `Padic.coefficientExtensionRing l E n`, the recorded
  quotient of the integer ring by the nth power of the uniformizer ideal.
- Every object in the compactification category: arbitrary `(c : Compactification f)`.
  This is the recorded open immersion/proper morphism factorization. The base
  structure on its ambient scheme is induced through its map to Y.
- Canonical functor: exactly `rightDerivedLowerShriekOfCompactification
  (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c`. Its body is termwise
  derived open extension by zero followed by total right-derived pushforward.
- Source and target: `ModuleDerivedCategory X (Padic.coefficientExtensionRing l E n)`
  and the corresponding category for Y, using the existing upstream abbreviation.
  These are the actual unbounded derived categories of module-valued sheaves on
  `Scheme.ProEt.topology`, equivalently modules over the constant ring sheaf.
- Preservation of shifts: the existing canonical `Functor.CommShift ℤ` of the exact
  derived and K-injective-derived factors and their composite supplies every integer
  shift and its coherence; there is no arbitrary comparison hypothesis.
- Distinguished triangles: `.IsTriangulated` is Mathlib's predicate whose
  `map_distinguished` clause quantifies over every distinguished triangle, with the
  canonical composite shift map in the third arrow of `mapTriangle`.

Dependency declarations read and used:

- `def-weil-scheme-morphism-properties` is a convention record. Its finite-type
  convention uses `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; separatedness is `IsSeparated`
  from the proper-morphism interface. `Scheme.Over` and `Scheme.Hom.IsOver` are
  from `Mathlib.AlgebraicGeometry.Over`.
- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement` and
  `Compactification.category`; its imported `Compactification.Defs` supplies the
  type `AlgebraicGeometry.Compactification`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek`:
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`. Its full
  docstring and body distinguish the composite from deriving the underived composite.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its imported `CoefficientExtension`
  supplies `Padic.coefficientExtensionRing` and all its coefficient constructions.
- `WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`:
  `AlgebraicGeometry.ProEtale.ModuleDerivedCategory`. I read its complete signature,
  body and docstring in the shared side source and confirmed with `scompile.py --source`.
- `def-weil-triangulated-category` is a Mathlib leaf: the functor predicate is
  `CategoryTheory.Functor.IsTriangulated` in `Mathlib.CategoryTheory.Triangulated.Functor`,
  including `map_distinguished`, induced additivity and the composition instance.

Proof interfaces retained include upstream
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
and the non-public import
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`. The latter supplies
`SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
The exact-derived functor and composite instances are available through the canonical
upstream factors. The previous compile exposed conflicting old/new pro-etale notation
when importing the proof-only side modules `ProEtaleIntrinsicExtensionByZeroExact`,
`ProEtaleModuleDirectImageLeftExact` and `SfDerivedDirectImage`; those omitted imports
remain documented here. The proof plan still names all their mathematical uses.

Edge cases: empty schemes, zero complexes, contractible distinguished triangles,
identity and proper compactifications, and all unbounded complexes and integer shifts
are included. Level n=1 is allowed; n=0 is excluded exactly by the positivity condition.
Characteristic zero and positive characteristic with l invertible are allowed.
No nonemptiness, dimension bound, constructibility, etale-origin, cohomological-dimension
or adjoint-existence hypothesis is added. Scheme universe u, site object universe u+1
and morphism universe u remain distinct. Coefficients and module values are in u+1,
exactly the existing upstream API; smaller finite-extension presentations have their
usual universe lifts. No equality of the site's object and morphism universes is imposed.

Search evidence from the original worker (retained in `searches.jsonl`):

- msearch LeanFinder: compactification-level derived compactly supported direct image
  on pro-etale module sheaves preserving shifts and distinguished triangles; eight
  generic sheaf/module pushforward or adjunction results, no exact specialized theorem.
- msearch Loogle: `CategoryTheory.Functor.IsTriangulated, CategoryTheory.Functor.comp`;
  twelve generic results, including the composition instance, no complete item.
- msearch Mathlib grep: `rightDerivedLowerShriek|compact.support.*triangulated`;
  zero hits.
- msearch LeanSearch: compactly supported derived direct image preserving distinguished
  triangles; unavailable with Internal Server Error, not a negative search result.
- Direct upstream item-id search: no declaration for this item. Generic exact-derived,
  right-derived and triangulated composition instances are proof tools.

Repair searches: `rg` of the shared side framework for `ModuleDerivedCategory` finds
its exact existing declaration at line 53 of its owning module. The dependency's own
`lean_audit.slopmaster2.decls` also lists it. `scompile.py --source` confirms its full
current source. Direct `rg` of `lean/Sheaf` for the category and theorem names finds
no pre-existing specialized theorem. The older slopmaster2 checkout lacks the category
source file, so its absence there is superseded by the actual published side source.
No duplicate category is delivered. There is no STATEMENT-DISPUTED flag.

## Dependency modules

`def-weil-pbc-proetale-site`: a lean-only interface repair under §1(B), using an
existing declaration and no delivered dependency module. The old
`Scheme.proEtaleDerivedCategory` uses `SheafOfModules` over a constant ring sheaf and
fixes the coefficient ring in the smaller universe. The recorded compact-support
functor instead uses module-valued sheaves in the larger working universe. The existing
`ProEtale.ModuleDerivedCategory` supplies exactly that presentation, with body
`DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))`.
Module-valued sheaves are the same mathematical constant-ring module sheaves: constant
scalars act sectionwise and extend uniquely locally over the constant ring sheaf.
The dependency record has `existing: true`, branch `slopmaster2`, the verbatim signature
and explanatory `lean.note`; it has no `file` field. Every other dependency-node field
is preserved. Its former declaration remains available to existing users.

Validation is by the prescribed `scompile.py` and `deliver2.py --no-push`, with default
60-second per-file limits. No proof, global build or delivery push is authorized here.


## Second reading by Q27

I independently opened the item JSON and Lean module, the six statement-dependency
nodes and their source declarations, and the source unit `sk-def-sf-operations`,
clause (iv). This reading is of the current delivery after the duplicate-category
repair, not the superseded return. The blueprint Markdown and local Stacks TeX
are absent from this checkout. The imported node and unit give the statement;
I additionally read the official Stacks pages [015F](https://stacks.math.columbia.edu/tag/015F),
[079P](https://stacks.math.columbia.edu/tag/079P),
[070K](https://stacks.math.columbia.edu/tag/070K), and
[014Y](https://stacks.math.columbia.edu/tag/014Y) supporting its four proof steps.
Their hypotheses are exactness between abelian categories, Grothendieck
abelianness, existence of K-injective resolutions, and exactness of the two
composed functors, respectively; none imposes boundedness or etale origin here.

Object/hypothesis/conclusion checklist, in the order of the node:

1. A field K0: `(K0 : Type u) [Field K0]`. Exact; no algebraic closure,
   perfection, finite-field or characteristic hypothesis is introduced.
2. Schemes X and Y over K0: `(X Y : Scheme.{u})` and the two
   `Over (Spec (CommRingCat.of K0))` instances. Exact; these are structure
   morphisms, not a restriction to affine schemes.
3. Both schemes finite type over K0: `LocallyOfFiniteType` and `QuasiCompact`
   on each of those structure morphisms. Exact by Mathlib's finite-type
   convention, read in `Morphisms/FiniteType.lean`.
4. A K0-morphism f: `(f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of K0))]`.
   Exact: the same base spectrum occurs for X, Y, and f.
5. f separated and finite type: `[IsSeparated f] [LocallyOfFiniteType f]
   [QuasiCompact f]`. Exact; neither properness nor smoothness of f is assumed.
6. A prime ell: `(l : ℕ) [Fact l.Prime]`. Exact; includes l = 2.
7. ell invertible in K0: `(_hl : IsUnit (l : K0))`. Exact; this is a hypothesis
   on the field element, not the tautological invertibility of an identity map.
8. Finite extension E/Q_l: `(E : Type (u + 1)) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Exact field
   extension and finite vector-space dimension, with no chosen valuation added.
9. Positive level n: `(n : ℕ) (_hn : 1 ≤ n)`. Exact encoding of the
   positive integers. No specific level or ramification condition is imposed.
10. A = A_(E,n): `Padic.coefficientExtensionRing l E n`. I opened its actual
    construction through `CoefficientExtensionFinite` and `CoefficientExtension`:
    it is the quotient of the recorded integer ring by the nth power of the
    ideal generated by the recorded uniformizer, not a residue field substitute.
11. Every compactification c: arbitrary `(c : Compactification f)`. I read
    `Compactification.Defs` and `Refinement`: c has an ambient scheme, proper
    `c.g`, open `c.i`, and `f = c.i ≫ c.g`; refinements are over Y, and their
    properness is derived. The ambient base morphism is `c.g` followed by the
    structure morphism of Y. Exact; no chosen Nagata compactification is fixed.
12. The specified functor: `rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c`. I opened
    the definition in the shared upstream source: its body is
    `D((c.i)_!open[A]) ⋙ R((c.g)_*[A])`. It is the prescribed termwise
    exact extension followed by K-injective right-derived pushforward. Exact.
13. Source and target D(X_proet,A), D(Y_proet,A): `ModuleDerivedCategory X ...`
    and `ModuleDerivedCategory Y ...`. I read its entire upstream declaration
    and confirmed it using `scompile.py --source`. Its body is
    `DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))`.
    These are unbounded derived categories of the correct constant-coefficient
    module sheaves on the small pro-etale sites. Exact.
14. Preservation of shifts: the functor already carries canonical `CommShift ℤ`
    from its two factors and Mathlib's composite structure. I opened the
    right-derived triangulated instances and the exact-derived interface.
    Every integer shift is included, and no arbitrary shift comparison is an
    extra input. Exact.
15. Distinguished triangles: `.IsTriangulated`. I opened Mathlib's definition:
    `map_distinguished` quantifies over every distinguished triangle, and
    `mapTriangle` uses the canonical shift isomorphism in its third arrow.
    The composition instance uses exactly the iterated image triangle.
    Exact; no cohomological-dimension or constructibility restriction is present.

The dependency repair also passes H4/H13. The previous
`Scheme.proEtaleDerivedCategory` uses `SheafOfModules` with A in the smaller
universe; it is not the definitionally matching presentation for the recorded
functor. The replacement is the already published
`AlgebraicGeometry.ProEtale.ModuleDerivedCategory`, not a new abbreviation.
Its signature is copied verbatim, `existing: true` has no `file`, and its
`lean.note` explains the presentation and universe issue. Only `lean` changes
in that dependency JSON. No new node or dependency module is delivered.
The item JSON also changes only `lean`, and I checked its `lean.statement`
is verbatim the complete theorem signature in the module.

Edge cases checked: the empty schemes and zero complexes are allowed, including
contractible distinguished triangles. The statement quantifies over every
available compactification, including identity/proper ones, without requiring a
selected object of Comp(f). There is no separate index family to exclude the
empty set. n = 1 is allowed and n = 0 is excluded exactly as in the node.
Characteristic zero and positive characteristic different from l are covered.
All unbounded complexes and all integer shifts remain included. The scheme
universe is u, the site's object universe u+1 and morphism universe u, and the
coefficient/module universe u+1; no equality between the two site universes
is imposed. Smaller presentations of a finite extension can be lifted into
this working universe. No geometric case is lost by this size convention.

Fresh independent searches, recorded by msearch in `searches.jsonl`:

- LeanFinder: "The derived direct image with compact support for a fixed
  open-proper factorization is an exact functor of unbounded derived categories
  of pro-etale module sheaves": eight generic exact/derived-functor results,
  no exact specialized statement.
- Loogle: `CategoryTheory.Functor.IsTriangulated,
  CategoryTheory.Functor.mapDerivedCategory`: found the generic exact-derived
  triangulated instance, a proof ingredient rather than this statement.
- Mathlib grep: `compactSupportDirectImage_isTriangulated|lowerShriek.*IsTriangulated|
  IsTriangulated.*lowerShriek`: zero hits.
- Direct rg on Mathlib, upstream WeilConjectures, shared WeilConjectures, and
  lean/Sheaf with `lowerShriek`, `compactSupport`, and `Triangulated`:
  no existing pro-etale compactification-level theorem. The ordinary etale
  `isTriangulated_rightDerivedLowerShriek` is for a different site/functor.
  Direct search found the existing `ModuleDerivedCategory` that this delivery uses.
- LeanSearch: the independent query about exact open extension followed by
  derived pushforward returned Internal Server Error; recorded unavailable,
  not counted as a negative search result.

The module has one theorem, whose proof is `sorry`, and no new data definitions,
local notation, private copies, or file-local instances. The module and theorem
source/blueprint docstrings are present. The theorem docstring contains all four
node proof steps, including the explicit composite shift map and last triangle
arrow. No unbound variable or universe appears. The earlier worker report lists
the intrinsic proof modules omitted because their imports clash with the older
upstream pro-etale notation; the exact-derived, right-derived, and composition
interfaces for the actual functor are already available through its imports.

I found no remaining mathematical mismatch and changed no correct Lean or node
text. This second reading adds the independent checklist, source checks, edge
case audit, search evidence, and validation record. The earlier duplicate-category
repair is confirmed. No statement correction or citer audit is needed.


Validation: the required standalone `scompile.py Q27
lem-compact-support-direct-image-triangulated` compile of
`lean/Sheaf/Paper/CompactSupportDirectImageTriangulated.lean` passed without
errors or warnings, using the wrapper's unchanged per-invocation limits.
The delivery dry run also checks the existing category declaration and performs
server preflight before the authorized final push.

The required `deliver2.py --no-push` completed successfully: `OK (dry run)`,
commit `aef5063158`, preflight and compilation passed, nothing pushed.
