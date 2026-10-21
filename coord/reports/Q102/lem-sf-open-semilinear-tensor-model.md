## Worker report

The delivery states `WeilConjectures.OpenSemilinearTensor.openSemilinearTensorModel`
in `Sheaf.SixFunctors.OpenSemilinearTensorModel`. It has one postponed theorem,
with all seven node proof steps in its docstring. The other declarations are
aliases, concrete operations on the existing interfaces, and records/predicates
specifying this comparison. There is no statement correction, new independent
notion, new DAG node, or dependency-record repair.

Hypotheses and clauses, read against the unchanged node:

- The prime is `(l : ℕ) [Fact l.Prime]`. The extension is `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The existing coefficient
  constructors use its integer ring and chosen uniformizer. Index `n : ℕ` in
  `integralCoefficientCommRingSheaf` denotes the node's positive exponent `n+1`.
- `U X : Scheme.{t}`, `j : U ⟶ X`, and `[IsOpenImmersion j]` give the schemes and
  open immersion. `_hlX : IsUnit (l : Γ(X, ⊤))` and its U analogue express
  invertibility of l. There is no quasi-compactness, separatedness, boundedness,
  or completeness assumption.
- The sites are literally `ProEt.topology T` on `T.ProEt`. Their object and
  morphism universes are `t+1` and `t`; coefficients and modules have universe
  `max u (t+1)`. No equality between the site and coefficient universes is imposed.
- `Operations` reuses `IntegralOpenReduction.Operations`. Its inherited
  `finiteConstants`, `projections`, `integralFunctor`, `finiteFunctor`,
  `systemComponents`, and `systemsFunctor` fix the finite and completed ring
  identifications with the actual open slice, including quotient compatibility.
  It provides exact localized extension/restriction and termwise system functors.
  Their actual adjunctions are `ordinaryAdjunction`, `openAdjunction`,
  `ordinarySystemAdjunction`, and `systemAdjunction` in the same namespace.
- `SX`, `SU`, `_cX`, `_cU` fix the specified reduction/limit calculi with their
  actual units and counits. The supplied `sections` is the actual
  `SemilinearDerivedSectionsData` on X. The conclusion requires the equality
  `o.openSystems = sections.localization (openObject j)`, so the simultaneous
  construction uses this section construction itself.
- `Comparison.preservesFlatTerms` uses the existing `SemilinearSections.flatTerms`,
  whose definition is termwise `SheafOfModules.IsFlatOnSite`.
  `Comparison.kflat` uses the recorded `IsKFlatIndependentCoefficients` predicate.
  Together these say that the extension of a flat-term K-flat representative is
  again such a representative. The existing exact extension functor and its
  `mapDerivedCategoryFactors` identify its localization with j_! of the original
  derived object, so arbitrary isomorphisms Q → K give the claimed representation
  of j_!K. There is no special choice of K or restriction to degree zero.
- `TotalComparison.chain` is the displayed total tensor chain isomorphism for
  Q and any complex F. `total` is an alias of the existing
  `SemilinearSections.totalTensor` / `coefficientTotalTensor`, hence of Mathlib's
  direct-sum total cochain tensor: its second differential has coefficient
  (-1)^a. `TotalSummands` fixes each (a,b) summand to the ordinary sheaf comparison;
  the target is extension of Tot(Q tensor restriction F). The isomorphism is a
  chain isomorphism, so it includes compatibility with that actual differential.
  `OrdinaryNaturality` and `TotalNaturality` specify naturality in both inputs.
- `OrdinaryGenerators` gives [x] tensor y → [x tensor restriction(y)] after
  sheafification. `restrictedSection` uses the actual slice-equivalence counit
  to express restriction, rather than assuming an unprescribed section map.
  `extensionSection` and `tensorSection` are the already constructed
  extension-presheaf and tensor-sheafification generators.
- `AX` and `AU : OrdinaryReduction` are ordinary functors to the strict system
  categories, with natural evaluation isomorphisms to actual scalar extension.
  Their `quotient` equations use `coefficientSequenceTransition` and
  `coefficientOrdinaryQuotient` for EVERY m ≥ n, including equality. Thus the
  models retain the strict semilinear transition maps before localization.
- `Comparison.ordinary` is a natural ISOMORPHISM OF STRICT SYSTEM FUNCTORS.
  Applying `ordinaryChain` termwise gives the node's r_Q as a chain isomorphism
  of strict semilinear systems. Its components are exactly the natural
  transformation's components; its chain law is the existing naturality equation.
  This construction never chooses lifts of evaluated derived maps.
- `Comparison.components` is the pre-localization equality identifying every
  finite component with `TensorComparison.ordinary n`. The latter is normalized
  by its `generators` equation on the actual scalar-adjunction unit. The map is
  B_n-linear, so the equation on [x] tensor 1 determines the formula on
  [x] tensor a for EVERY local coefficient a, by multiplication by a on both
  sides. On U the multiplication uses `finiteMap n`, i.e. exactly a restricted
  to U. This renders the entire coefficient formula, not just constant scalars.
- `Computation.presentation` uses the already recorded
  `CoefficientReductionPresentation`, including its derived-evaluation equation
  and all strict quotient squares. `Computation.augmentation` uses the existing
  `AugmentedPresentation`, which requires a SINGLE strict chain augmentation
  whose every component is x ↦ x tensor 1 and whose adjoint is the actual
  reduction/limit adjunction arrow. In `RepresentativeSquare` both cU and cX
  satisfy this condition. The component formula above at a=1 is the ordinary
  augmentation square on both sides, before localization. Equality of these
  ordinary strict maps is componentwise; no claim of faithfulness of derived
  evaluations is made.
- `Comparison.r` is a natural isomorphism on the entire unbounded derived
  category, with source j_! followed by reduction and target reduction followed
  by J_j. `RepresentativeSquare` identifies it with localization of that one
  ordinary strict chain isomorphism using the specified augmented computations,
  for EVERY flat-term K-flat Q. This is representative independence through
  canonical computation comparisons. Evaluating the square and using
  `Computation.presentation` and `Comparison.components` gives the canonical
  derived open tensor comparison at each n. Its generator normalization is the
  inverse open-unit tensor adjunct of Stacks 0E8I and
  `lem-sf-open-tensor-normalization`; the proof docstring records this
  characterization explicitly.
- Completeness and normalization in the opening paragraph fix conventions, not
  additional hypotheses: the quotient-Roos predicate remains
  `IntegralOnSlice.IsComplete`, and the normalization predicate is the recorded
  one in the supplied calculus. Neither is imposed on K here.

Dependency declarations read and reused:

| Node | Module and declaration |
| --- | --- |
| def-weil-l-adic-coefficient-extension | Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing, with the imported coefficientExtensionIntegers, coefficientExtensionUniformizer, coefficientExtensionRing and coefficientExtensionTransition constructions |
| def-weil-pbc-proetale-site | Mathlib.AlgebraicGeometry.Sites.Proetale: AlgebraicGeometry.Scheme.ProEt and ProEt.topology |
| lem-coef-derived-system-evaluation-calculus | Sheaf.Paper.CoefDerivedSystemEvaluationCalculus: CoefficientDerivedSystemCalculus, CoefficientDerivedSystemCoherence, CoefficientReductionPresentation, coefficientOrdinaryQuotient, coefficientIntegralScalarUnitSection and coefficientDerivedSystemEvaluationCalculus |
| def-weil-derived-complete | Sheaf.Paper.DerivedCompleteOnSlices: WeilConjectures.IntegralOnSlice.IsComplete; retained as the convention, not an extra hypothesis |
| def-weil-scheme-morphism-properties | A convention node; the open immersion is Mathlib AlgebraicGeometry.IsOpenImmersion |
| lem-sf-open-tensor-normalization | Sheaf.SixFunctors.OpenTensorNormalization: SheafOfModules.openTensorNormalization; actual exact derived adjunction construction reused through the open-operation interface |
| lem-coef-semilinear-derived-sections | Sheaf.Paper.SemilinearDerivedSections: SemilinearDerivedSectionsData, OpenSystems and semilinearDerivedSections; its SemilinearSystemModels supplies ordinaryTensor, totalTensor, tensorSummand, tensorSection, ordinaryTensorHom and flatTerms |
| def-pc-kflat-complex | Sheaf.Algebra.Homology.KFlatIndependentCoefficients: CochainComplex.IsKFlatIndependentCoefficients |
| def-pc-flat-sheaf-modules | Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: SheafOfModules.IsFlatOnSite |
| lem-pc-kflat-resolution | Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients: CochainComplex.exists_isKFlatResolutionIndependentCoefficients |
| def-pc-tensor-complex-sheaves | Mathlib.Algebra.Homology.BifunctorShift: CochainComplex.mapBifunctor; this is the total tensor in the reused model |

The existing `IntegralOpenReductionComparison` module also owns the exact
`Operations`, `TensorComparison`, `AugmentedPresentation`, extension/restriction,
finite/system extension, and extension-generator interfaces used here. These
are reused rather than copied. Its completeness/quasi-compactness-restricted
`integralOpenReductionComparison` theorem is not used. This item is a proof
dependency of that theorem; while the interfaces share that module, adding a
reverse proof import would form an import cycle and must be omitted under
stages/2-statements.md §3.7. A later proof-module separation can remove that
packaging limitation without changing any statement here.

All available recorded proof-dependency modules are imported, directly or through
these public interfaces. The missing bilinear sheafification and localized tensor
restriction imports were added explicitly. No upstream file was modified.

Edge cases checked before and after writing: U empty (no extension summands),
j identity (the summand/unit maps become identity identifications), zero complexes,
unbounded Q and F, positive exponent 1 (index 0), m=n and longer quotient composites,
negative/odd first total degrees (the existing signed total differential), arbitrary
local coefficients rather than constant sections, and distinct site/coefficient
universes. No counterexample or disputed statement was found.

Searches for an existing statement:

- `msearch.py` LeanFinder, query “Extension by zero tensor comparison for strict
  semilinear coefficient systems on flat K-flat complexes”: eight ordinary module
  flatness hits (equational criteria and exactness of tensor); none states this
  ringed-site strict-system comparison.
- `msearch.py` Loogle, query `"SheafOfModules", "tensor"`: ten hits for presheaf
  monoidal tensors and their component formulas; none gives this simultaneous
  comparison or derived normalization.
- `msearch.py` grep, query `extensionByZero|semilinear.*[Tt]ensor` in
  Mathlib/CategoryTheory: zero hits.
- `msearch.py` LeanSearch, query “extension by zero tensor comparison on unbounded
  complexes of strict coefficient systems”: eight homological-complex zero-object,
  embedding and extension hits; none matches.
- `rg` over both project source roots for
  `semilinear.*[Tt]ensor|[Oo]pen.*[Ss]emilinear|lem-sf-open-semilinear-tensor-model`
  found the ordinary input-semilinearity lemmas and the integral-open parent
  interfaces. The parent comparison is restricted to complete objects and
  quasi-compact opens, so does not state this node. The scalar-restricted
  RingedOpenStrictReduction module uses a tower in one scalar category, so does
  not state this node either.
- A final `rg` for the new namespace, main declaration and OrdinaryReduction in
  both project roots found no declaration-name collision. Searching the exact
  node id in WeilConjectures found no existing attachment.

Validation: the final scompile.py run passed without errors or warnings, both
in the sandbox check (41.5 seconds) and at its real module path (44.5 seconds).
The declaration has exactly one sorry, the stage-2 theorem proof. Diagnostic
compiles used scompile.py only. The initial delivery dry run passed preflight and compilation. The generic
K-flat-preservation import was then marked as a proof-only import, as required
by stages/2-statements.md §3.7; the final clean scompile.py rerun verified that
version too. Large dependent record equations were factored
into named predicates in the same file, retaining their contents and the fixed
per-file limit.

## Second reading by Q102

This is a second pass by the same worker, not an independent agent review.
The dispatcher instructs the worker to deliver directly; the maintainer performs
the independent review. I reread the node, the Stacks source passages, and the
Lean fields together. The clause mapping above records that reading. In
particular I checked that r is natural on ambient derived objects, the model
square is in the strict-system derived category before evaluation, both augmented
presentations use the actual adjunction, the coefficient maps are B_n-linear,
and the ordinary comparison exists before scalar restriction. No mathematical
node change was needed.
