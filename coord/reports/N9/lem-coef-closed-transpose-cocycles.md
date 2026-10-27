## Worker report

The module `Sheaf.Paper.ClosedCoefficientTransposeCocycles` states the four clauses
of `lem-coef-closed-transpose-cocycles`. All four theorem proofs are `sorry`.
The other declarations construct the specified maps and their full-subcategory
restrictions, including their naturality proofs as necessary definition data.
There is no changed informal statement, new DAG node, or dependency-node repair.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Fixed algebraic closure of a finite field | `D : WeilConjectures.FiniteFieldDatum` retains its prime, cardinality and algebraic-closure fields. |
| Prime ell different from characteristic | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` in every theorem. |
| Finite extensions E,L (and F) of Q_l | Recorded `ConstructibleExceptionalCoefficients.FieldStage l`, with its `Field`, `Algebra (Padic l)` and `FiniteDimensional` fields. |
| Positive finite quotient stages | `ring l E m` is literally `Padic.coefficientExtensionRing l E.carrier (m + 1)`; every positive exponent occurs, including 1. Likewise n and s. |
| Any unital coefficient maps | `φ : ULift A →+* ULift B` and `ψ : ULift B →+* ULift C`; conjugation by ULift identifies these with all original ring maps, with no algebraic-extension or flatness restriction. |
| Constant module sheaves on the small pro-etale site | `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u+1} A)` in the ambient derived category. This is the published fixed-module presentation of the constant coefficient sheaf. |
| Bounded constructible finite-Tor inputs of etale origin | `C A T` abbreviates the full subcategory of the recorded `ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat A) T`; its bounded-constructible clause includes etale origin (`constructibleFiniteTor.plusEtaleOrigin`). It is not a new predicate. |
| Separated finite-type k-schemes and k-maps | `X Z W : Over (Spec (.of D.k))`, with explicit `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` instances on each structure morphism. Maps `i`, `t` are morphisms in `Over`. These binders are written explicitly on each theorem rather than relying on unused section parameters being retained. |
| Closed immersions | `[IsClosedImmersion i.left]`, and `[IsClosedImmersion t.left]` in the geometric clause. Their composite has the induced instance. |
| The stipulated domain closure | `ScalarClosed` is closure under the fixed derived scalar functor; `RightClosed` is closure under the recorded exceptional functor. `ClosedAdjunction.pushClosed` expresses that the closed direct image has the indicated restricted codomain; `rightClosed` and `adjunction` specify exactly the assumed exceptional closure and adjunction. There is no abstract replacement functor. |
| Ordinary uncompleted scalar extension S | `scalar` restricts `pbcFixedScalarExtension`, the left adjoint to actual derived restriction of scalars; this is ordinary, not completed, extension. |
| Ordinary derived direct image | `push` restricts `(lowerStar (ModuleCat A) i).rightDerivedFunctor`, the published ordinary pro-etale direct image. |
| Constructible exceptional functor Ri! | `right` restricts `sfFiniteExceptionalFixed A (Compactification.ofIsProper i)`, literally Rnu_* followed by the etale exceptional functor followed by nu*. This is the finite exceptional realization retained by the recorded dependency. |
| The specified invertible ordinary comparison c_i | `comparison` has exactly `finiteCoefficientChangeDirectImageMap φ i K.obj` as component. Its `IsIso` binder records the node's given comparison isomorphism from `lem-coef-finite-direct-image`, not an exceptional invertibility assumption or a new arbitrary comparison. |
| Definition b_i = right mate of c_i inverse | `closedTranspose` specializes `transpose`, whose entire term is `mateEquiv a b (TwoSquare.mk ... (asIso comparison).inv)`. |
| Displayed exceptional counit equation | First conjunct of `closedTranspose_counit_naturality`, with Lean composition written left-to-right. |
| Naturality in M | Second conjunct, for arbitrary `f : M ⟶ N`; `closedTranspose` is also constructed as a natural transformation. |
| Canonical ordinary composition identification | `pushComp` restricts the exact `finiteDirectImageComposition` components. |
| Chained Hom adjunction, counit epsilon_i after i_*epsilon_t | `rightComp` uses `Adjunction.rightAdjointUniq` between the composite-left transported adjunction and `b.adjunction.comp a.adjunction`; Mathlib `comp_counit_app` is precisely this counit. |
| Geometric cocycle | `closedTranspose_geometric` displays both rightComp factors. After their identification it reads `b_it = Rt_B!(b_i) after b_t`. |
| Canonical tensor balancing identifications | `scalarComp` restricts `pbcFixedScalarExtensionComp`, obtained by conjugating the actual composition of restriction functors through their normalized derived adjunctions. On K-flat representatives this is `((x tensor b) tensor c) ↦ x tensor ψ(b)c`; its inverse inserts 1. No arbitrary isomorphism is chosen here. |
| Coefficient cocycle | `closedTranspose_coefficient` inserts inverse scalarComp at the source and scalarComp at the target, and between them has `scalar ψ` applied to b_AB followed by b_BC. |
| Identity coefficient change | `closedTranspose_identity` compares b_id to the identity under `scalarUnit` on X and Z. `restrictionUnit` is the sectionwise module identity; `scalarUnit` is its adjunction mate, normalized on tensor representatives by multiplication. |
| No invertibility of b | No `IsIso closedTranspose` premise or conclusion occurs; every assertion is an equality of specified morphisms. |

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, and its imported `Padic.coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: the recorded native `ProEtale.DerivedCategory.constructibleFiniteTor` (defined upstream in `FiniteCoefficient.Derived.TorAmplitude`).
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: `ConstructibleExceptionalCoefficients.FieldStage` and the retained exceptional realization; `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`: `sfFiniteExceptionalFixed`, the same finite-level realization used in `RingSystem.finiteRight`.
- `Sheaf.Paper.SfDerivedDirectImage`: finite ordinary direct-image convention, using its underlying actual `lowerStar.rightDerivedFunctor` in fixed-module coordinates.
- `Sheaf.Paper.FiniteCoefficientDirectImage`: `ProEtale.finiteCoefficientChangeDirectImageMap`, `finiteCoefficientDirectImageMap_naturality`, and the geometric/scalar cocycles available for the proof.
- `Sheaf.Paper.FiniteDirectImageComposition`: `ProEtale.finiteDirectImageComposition`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`; `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`; `Mathlib.CategoryTheory.Adjunction.CompositionIso`: the normalized adjoint identifications.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: publicly retained generic `SheafOfModules.DerivedChangeOfRingsCochainModel` and universal K-flat computation interface.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: the K-flat convention; proof imports retain `KFlatResolutionIndependentCoefficients`, `ChangeOfRingsKFlat`, `SiteDerivedTensorDescentIndependentCoefficients` for the node's proof steps.
- Canonical scalar functors and compositors are `ProEtale.pbcFixedScalarExtension` and `pbcFixedScalarExtensionComp`, publicly supplied by the finite-comparison dependency from `Sheaf.Paper.WitnessCompatibility`.
- `def-weil-scheme-morphism-properties` is a convention node; its named Mathlib morphism properties are used directly.

Edge cases checked: level 1 is m=0, and all positive levels are covered; the zero
scheme and zero complexes are not excluded. Identity coefficient maps, identity
closed immersions, and nonflat quotient maps are allowed. The coefficient and
geometric formulas retain the explicit canonical identifications rather than
asserting ill-typed strict equalities. The site has object universe u+1 and hom
universe u, while coefficient modules use u+1; no equality of those site universes
is imposed. Different coefficient field carriers may always be placed in a common
universe, as in the recorded finite-stage interface. No `let` appears in a theorem
statement. Definitions contain no sorry and no arbitrary Nonempty comparison.

Searches: msearch LeanFinder query "Closed exceptional scalar extension comparisons
are right mates of inverse direct image comparisons and respect geometric and
coefficient composition" returned 8 generic results, including module scalar
extension composition and scheme pullback conjugation, but no exact statement.
The earlier interrupted-session LeanFinder query recorded in searches.jsonl
likewise returned only closed-immersion and scheme-map facts. msearch Loogle
"CategoryTheory.mateEquiv, CategoryTheory.Adjunction.comp" returned 6 hits,
including `mateEquiv_hcomp` and `mateEquiv_square`; these are the generic tool,
not this specified sheaf statement. msearch grep
"mateEquiv_hcomp|mateEquiv_counit" in `CategoryTheory/Adjunction` returned the
five relevant lines of Mathlib Mates. Searches with rg for the node id and
`closedTranspose|closedCoefficientTranspose|ClosedCoefficient` in both
`lean/WeilConjectures` and `lean/Sheaf` found no existing exact declaration.
The broader earlier search for ClosedCoefficient also found unrelated
AlgebraicallyClosedCoefficients declarations, which are not matches.
No new node is introduced, so no new-node search record is required.

No STATEMENT-DISPUTED flag or statement correction is needed.

## Second reading by N9

This is a fresh clause-by-clause rereading by the same dispatched worker, without
spawning another agent as the dispatch forbids. The maintainer performs the
independent review. Reopened the node, the source paragraph and the completed
Lean module together. The counit equation has the correct inverse comparison
and orientation; the geometric formula uses the chained right-adjoint iso and
retains all three adjunctions; the scalar formula has inverse reassociation at
the source and forward reassociation after the C-right adjoint. The identity
formula is an equality to the scalar unit, which is exactly identity after
identification. The formal category's bounded constructibility includes etale
origin, confirmed from its definition and plusEtaleOrigin lemma. Ordinary c is
fixed by its recorded components, and b is defined by mateEquiv, with no
invertibility claim for b. During this reading the finite-type/separated
hypotheses were made explicit on each theorem, preventing Lean section-variable
pruning from dropping them. An unused coefficient alias was removed. The syntax
binder `at` was renamed `aT`. No informal node fields were changed.
