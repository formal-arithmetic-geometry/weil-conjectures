## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact`
defines `CategoryTheory.Functor.leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory`
and states its counit compatibility as
`leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory_hom_fac` with `sorry`.
The isomorphism itself has real data: it is Mathlib's `leftDerivedUnique` applied to
these two specified functors and their canonical counits. No arbitrary isomorphism
or existence choice is substituted for the canonical comparison.

Source read: the complete node and its proof, and
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/` +
`sk-def-sfb-derived-categories/def-sfb-left-derived-exact.md`. The latter states the
same comparison. The full recorded statement dependency and its Lean source were read.
There is no repair note for this item.

Hypotheses and clauses, individually:

- The categories are `{C : Type uC} {D : Type uD}`, with independent hom universes
  `[Category.{vC} C] [Category.{vD} D]` and `[Abelian C] [Abelian D]`.
- The source's monoidal structure and tensor additivity in both variables are
  `[MonoidalCategory C] [MonoidalPreadditive C]`.
- Countable coproducts are `[HasCountableCoproducts C]`.
- Integer-indexed colimits and their exactness are `[HasColimitsOfShape ℤ C]` and
  `[HasExactColimitsOfShape ℤ C]`.
- Preservation of those colimits by tensoring with each fixed object on both sides
  is the two families `[∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]`
  and `[∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]`.
- Functorial flat resolutions are `[Abelian.HasFunctorialFlatResolution C]`.
- The chosen derived categories are supplied by `[HasDerivedCategory.{wC} C]` and
  `[HasDerivedCategory.{wD} D]`, matching the dependency interface. All six universe
  variables are explicitly declared and are independent; no universe equality is imposed.
- The functor is `(F : C ⥤ D)`. Exactness is `[F.Additive]`,
  `[PreservesFiniteLimits F]`, and `[PreservesFiniteColimits F]`, exactly as the
  K-flat preservation dependency defines exactness.
- The parenthetical preservation of K-flat quasi-isomorphisms is supplied by
  `F.preservesTotalTensorKFlatQuasiIso_of_exact`. It is passed explicitly as the
  `hF` instance argument in the signature, so it is a consequence of exactness,
  not an additional hypothesis on `F`.
- `LF` is precisely the dependency's `F.leftDerivedFunctorFromTotalTensor` with
  that preservation proof; `D(F)` is Mathlib's `F.mapDerivedCategory`, the localization
  of the termwise action on integer-indexed cochain complexes.
- The conclusion is a natural isomorphism `LF ≅ F.mapDerivedCategory`. Its definition
  uses the dependency's universal-property theorem and
  `isLeftDerivedFunctor_of_inverts` applied to `F.mapDerivedCategoryFactorsh`.
  These are the two canonical counits used in `leftDerivedUnique`.
- Canonicity is made usable by the accompanying equation
  `whiskerLeft DerivedCategory.Qh comparison.hom ≫ F.mapDerivedCategoryFactorsh.hom =
  F.leftDerivedFunctorFromTotalTensorCounit` (with the same explicit preservation proof).
  This is the uniqueness comparison's counit factorization, not extra chosen data.

Dependency declarations used:

- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor`:
  `CategoryTheory.Functor.leftDerivedFunctorFromTotalTensor`,
  `leftDerivedFunctorFromTotalTensorCounit`, and
  `isLeftDerivedFunctor_leftDerivedFunctorFromTotalTensor`. Read the complete module,
  including its explicit ambient assumptions and universal-property docstrings.
- The proof dependency `def-sfb-preserves-kflat-quasi-iso` is already imported publicly
  through that statement dependency. Its module
  `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso` supplies
  `CategoryTheory.Functor.preservesTotalTensorKFlatQuasiIso_of_exact`.
  Its definition and theorem signatures/docstrings were read in full.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactorsh`.
  Read their signatures and docstrings, including the independent derived-category universes.
- `Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived` supplies
  `CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts`;
  the re-exported `Mathlib.CategoryTheory.Functor.Derived.LeftDerived` supplies
  `leftDerivedUnique`. Read the two defining signatures and bodies.

Edge cases checked by inspection: the zero exact functor needs no faithfulness or
nonzero assumption; the identity exact functor is allowed; the zero category is allowed;
all unbounded integer-indexed complexes are included, with no degree restriction or
nonempty family introduced. `D` needs no tensor structure or flat resolutions. No
preservation of countable coproducts by `F` is imposed. The independent object, morphism,
and derived-category universes exclude no size case supported by the recorded dependency.

Searches actually run via `msearch.py NU def-sfb-left-derived-exact`:

- `leanfinder`: "The total left derived functor of an exact additive functor is
  canonically isomorphic to its termwise functor on derived categories". Eight hits,
  including `mapDerivedCategoryFactorsh`, `mapDerivedCategoryFactors`, and the
  degree-zero `leftDerivedZeroIsoSelf`; no complete match for the recorded `LF`.
- `loogle`: `CategoryTheory.Functor.leftDerivedUnique, CategoryTheory.Functor.mapDerivedCategory`.
  Zero hits for that combined query.
- `grep`: `leftDerivedUnique|leftDerivedFunctorIsoMapDerivedCategory|mapDerivedCategoryFactorsh`.
  Seven Mathlib hits: the termwise factorization and general left-derived uniqueness API.
- `leansearch`: "The total left derived functor of an exact functor agrees with the
  induced functor on derived categories". Eight hits, including `totalLeftDerived`,
  `mapDerivedCategory`, and `isLeftDerivedFunctor_iff_isIso_leftDerivedLift`; no exact match.
- Direct `rg` on the project's Lean and upstream derived-category sources found the
  upstream `leftDerivedFunctorIsoMapDerivedCategory`. Its full source was read: it
  requires three extra graded-tensor assumption families and uses the old
  `leftDerivedFunctor`/`PreservesKFlatQuasiIso` rather than the dependency's recorded
  total-tensor interface. It therefore cannot be rebound as this node's exact statement.
  The new module compares the existing recorded functors and does not redefine either notion.
- Direct `rg` for `def-sfb-left-derived-exact` in upstream `WeilConjectures` had no hits.
  Search of `dag/lean_names_upstream.json` by the item id had no hits.
- Direct `rg` for the new full declaration's final component in Mathlib,
  upstream `WeilConjectures`, side `lean/Sheaf`, and `dag/lean_names_upstream.json`
  had no hits, confirming that the new names are available.

No statement correction, new node, or dependency module is needed. The node copy
changes only `lean`; its prior incomplete upstream attachment is replaced by a complete
record for this exact interface. No STATEMENT-DISPUTED issue remains.

Validation: `scompile.py NU def-sfb-left-derived-exact` compiled the module cleanly,
including its side dependency overlay, with no errors or warnings. The canonical
comparison definition contains no `sorry`; the only postponed theorem is the named
counit-factorization theorem, whose docstring gives the source and natural-language proof.

Dry-run repair: the first preflight found a truncated `lean.statement`, because extraction
stopped at the named instance argument `hF := ...`. The record now includes the complete
verbatim signature through the outer definition delimiter. Lean source was unchanged.
The remaining second-reading section belongs to the independent next worker.

## Second reading by NU

I reread the source node `def-sfb-left-derived-exact`, its blueprint statement and separate proof source places, the
Lean file, and the dependency declaration `def-sfb-left-derived-functor`.

The node's objects and hypotheses match the Lean as follows:

- The source category is a monoidal abelian category `C`, rendered by `{C : Type uC}`,
  `[Category.{vC} C]`, `[Abelian C]`, `[MonoidalCategory C]`, and
  `[MonoidalPreadditive C]`.
- Countable coproducts, exact integer-indexed colimits, and preservation of those colimits
  by tensoring on either side are rendered by `[HasCountableCoproducts C]`,
  `[HasColimitsOfShape ℤ C]`, `[HasExactColimitsOfShape ℤ C]`, and the two displayed
  families of `PreservesColimitsOfShape ℤ` instances.
- Functorial flat resolutions are rendered by
  `[Abelian.HasFunctorialFlatResolution C]`.
- The target is an abelian category `D`, rendered by `{D : Type uD}`,
  `[Category.{vD} D]`, `[Abelian D]`; the independent derived-category choices are
  `[HasDerivedCategory.{wC} C]` and `[HasDerivedCategory.{wD} D]`.
- The exact functor is `(F : C ⥤ D)` with `[F.Additive]`,
  `[PreservesFiniteLimits F]`, and `[PreservesFiniteColimits F]`. These are precisely
  the exactness assumptions used by `mapDerivedCategory` and by the recorded
  `preservesTotalTensorKFlatQuasiIso_of_exact` interface.
- The conclusion's `LF` is rendered by
  `F.leftDerivedFunctorFromTotalTensor (hF := F.preservesTotalTensorKFlatQuasiIso_of_exact)`;
  `D(F)` is rendered by `F.mapDerivedCategory`; and the canonical isomorphism is the
  definition `leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory`.
- The source proof's counit characterization is rendered by the accompanying theorem
  `leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory_hom_fac`, whose equation uses
  `whiskerLeft DerivedCategory.Qh`, the comparison's `hom`,
  `F.mapDerivedCategoryFactorsh.hom`, and the canonical left-derived counit.

No hypothesis is added or omitted, and the quantifier/universe structure remains
independent. There is no variable index set in this statement: `ℤ` is the fixed grading and colimit
shape. Empty coproducts are included in the countable-coproduct assumption. Zero and
identity functors and zero categories are allowed; an empty category cannot be abelian
since it has no zero object. Every integer degree, including zero, is covered. No scheme,
coefficient ring, characteristic, nonzero, faithfulness, or boundedness assumption is
introduced. `D` needs no monoidal or flat-resolution structure, as in the node.

I searched Mathlib, the upstream `WeilConjectures` sources, and `lean/Sheaf` with `rg`, and
independently ran `msearch.py` LeanFinder and LeanSearch with the queries below; I also
read the first worker's Loogle and grep search record. The upstream
`leftDerivedFunctorIsoMapDerivedCategory` is a different declaration: it uses the older
left-derived interface and adds three graded-tensor assumption families. It therefore does
not state this node's exact interface. No matching declaration for the new total-tensor
comparison exists elsewhere, so retaining this module is correct and does not duplicate a
usable definition.

I found no mismatch between the node and Lean, no hollow definition, and no unbound
variables. The canonical comparison has real data via `leftDerivedUnique`; only the named
counit-factorization theorem remains `sorry`, as required for a stage-2 statement. No
statement correction, new definition node, or dependency-module repair is needed.

Independent searches in this second reading:

- LeanFinder: "An exact functor induces a functor on unbounded derived categories which
  is its total left derived functor". Eight hits, including `mapDerivedCategory`,
  `mapDerivedCategoryFactorsh`, and `isLeftDerivedFunctor_of_inverts`; no comparison
  involving the dependency's `leftDerivedFunctorFromTotalTensor`.
- LeanSearch: "Uniqueness comparison of two total left derived functors with their
  counits". Eight hits, led by `leftDerivedUnique`; this is the general comparison
  constructor reused in the definition, not a duplicate of the specific comparison.
- Direct `rg` across Mathlib, upstream `WeilConjectures`, and the project's `lean/Sheaf`:
  declaration patterns for left-derived comparisons, `leftDerivedUnique`,
  `isLeftDerivedFunctor_of_inverts`, and `PreservesTotalTensorKFlatQuasiIso`.
  I opened the actual Mathlib uniqueness and invertible-counit signatures and the
  upstream comparison's full ambient variable block. The latter's three additional
  graded-tensor families prevent an exact existing attachment. The preservation
  dependency's theorem assumes precisely additive finite-limit/finite-colimit
  preservation and concludes the recorded K-flat preservation property.

The only changes made in this second reading are this independent review section and
its search/edge-case record; the correct Lean module and node signature are unchanged.
`scompile.py` completed successfully for the sole delivered file. The subsequent dry run
printed `OK (dry run)` after compiling and passing server preflight; the earlier wrapper
bookkeeping failure disappeared on the prescribed retry.
