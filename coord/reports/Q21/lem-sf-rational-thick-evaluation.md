## Worker report

This delivery states `WeilConjectures.IntegralOnSlice.rationalThickEvaluation` in
`Sheaf.Paper.RationalThickEvaluation`. Every theorem proof is `sorry`; definitions
contain actual data. The item's natural-language statement and dependency lists
are unchanged. Two lean-only dependency repairs expose the missing slice interface.

The theorem states existence of the canonical natural completed-evaluation comparison,
its unique extension equation, compatible exact shift structures, and rational descent.
It asserts all closure properties of the isomorphism locus in the actual scalar
localization. It does not assume an arbitrary comparison, exactness of either functor,
completeness of RHom, or any of the closure properties.

Hypotheses and objects, with their exact Lean renderings:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `l : ℕ`, `[Fact l.Prime]`. |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. |
| Valuation ring and uniformizer | The recorded `Padic.coefficientExtensionIntegers l E` and `Padic.coefficientExtensionUniformizer l E`. The finite quotients retain the dependency's positive-exponent indexing n = exponent n+1. |
| Scheme X on which ell is invertible | `X : Scheme.{t}`, `_hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x)`. |
| Completed coefficient sheaf | `ring l E X none` uses `completedIntegralCommRingSheafUnrestricted l E X`, retaining the underlying ring data of the recorded completion. |
| Either the global site or its slice over an object U | `U : Option X.ProEt`; `Site X none = X.ProEt`; `Site X (some V) = Over V`; `topology` is respectively the actual topology and its `J.over V`. |
| Restricted coefficients and quotient maps | `restrict` is the identity or the actual `Over.forget` sheaf restriction; `ring`, `finite`, `projection`, `rho` apply it to the already recorded sheaves and maps. No replacement ring is chosen. |
| Derived category of all R-module sheaves | `D l E X U = DerivedCategory (Mod l E X U)` with `HasDerivedCategory.standard`. `Mod` is Mathlib's `SheafOfModules` on the recorded ring. |
| O_E-linearity of T | The instance `linear` is uniquely characterized by precomposition with `scalarDerived`; that action is the localization of actual constant-section multiplication. `linearOpposite` transfers the same action to reversed Hom modules. |
| Derived internal Hom | `hom` is `derivedInternalHomOfUniverses.{t+1,t,u}` on the actual site and ring; `psi M` fixes its second variable. |
| Completed derived tensor | `completedTensor` is normalized quotient completion of the existing representative-normalized ordinary tensor model. The balanced finite-level tensor identity proves `completedTensor_global_comparison` with the original global finite-tensor Roos construction. On a slice all reductions, transitions and the Roos functor are built on that slice, rather than by restricting a global result about M. |
| Scalar localization Q | `Rational` is the recorded `ScalarLocalization O_E (D ...) varpi_E`; `q` is its recorded tensor-with-one localization functor. |
| Its induced triangulation | The structure binders, `_hshift`, `_hQshift`, and `_htriangles` unpack exactly `exists_triangulated_scalarLocalization`: the shift by one is the induced scalar extension, the Q comparison is the identity, and distinguished triangles are precisely localized integral triangles up to isomorphism. These specify the triangulation named in the node; they are not extra mathematical restrictions on X or M. |
| Fixed derived-complete M | `M : D l E X U`, `hM : IsComplete l E X U M`. The global case is definitionally `IsDerivedCompleteUnrestricted`; the slice case is the canonical augmented reduction-tower Roos triangle, including its specified first map. |

Each asserted clause is represented as follows:

| Node clause | Lean rendering |
| --- | --- |
| Phi(L) = RHom(L,R) completed-tensor M | `phi M` is `psi coefficient` followed by the section functor `(A,M)` and `completedTensor`. |
| Psi(L) = RHom(L,M) | `psi M = (Functor.curry.obj (hom ...)).flip.obj M`. |
| Both functors exact | Existential `CommShift ℤ` structures and both `.IsTriangulated` conclusions, using Mathlib's opposite triangulation, whose shift n is the original shift -n. |
| Both O_E-linear | `.Additive` and `.Linear (Padic.coefficientExtensionIntegers l E)` for each functor, with the canonical scalar actions just described. |
| Psi(L) derived complete | `∀ L, IsComplete ... ((psi ... M).obj (op L))`. |
| Canonical evaluation comparison | `α : phi ... M ⟶ psi ... M`, with `completionUnit.app (ordinaryPhi.obj (op L)) ≫ α.app (op L) = ordinaryEvaluation L M`. `ordinaryEvaluation` is exactly the recorded `ringedSiteDualEvaluationLeft`, transposed from evaluation with Koszul symmetry. |
| Canonical extension into the complete target | The immediately following universal equation forces every natural transformation with that same extension equation to equal α. Neither an arbitrary map nor a Nonempty choice of an unspecified comparison occurs. |
| Natural in L | α is a Mathlib natural transformation on the opposite derived category. |
| Compatible with shifts | `NatTrans.CommShift α ℤ`, under the exact shift structures just asserted. |
| Induced exact rational functors | `F G : Rationalᵒᵖ ⥤ Rational`, natural isomorphisms `q.op ⋙ F ≅ phi ⋙ q` and `q.op ⋙ G ≅ psi ⋙ q`, their shift structures, and `.IsTriangulated` for each. Fraction maps are forced by the integral normalization and functoriality: inverse powers of the scalar identity must map to their inverses. |
| Rationalized comparison | `αQ : F ⟶ G` and `whiskerLeft q.op αQ ≫ eG.hom = eF.hom ≫ whiskerRight α q` identify it with Q(α) through the descent normalizations. |
| Rational shift compatibility | `NatTrans.CommShift αQ ℤ`. |
| S_M tests Q(theta_L,M) invertibility | `evaluationLocus M α L = IsIso (q.map (α.app (op L.obj)))` on the unchanged objects of the recorded scalar localization. |
| Contains R[0] | Explicit membership of `q.obj coefficient`, where `coefficient` is `ringedSiteDualityUnit`, the module unit complex localized in degree zero. |
| Contains 0 | `.IsTriangulated` includes `.ContainsZero`; together with isomorphism closure this includes every chosen zero object. |
| Closed under localized isomorphisms | `.IsClosedUnderIsomorphisms` on the actual rational category. |
| Closed under finite direct sums | `.IsClosedUnderFiniteCoproducts`; finite coproducts in a preadditive triangulated category are the finite biproducts/direct sums. This includes the empty sum and transports to finite index types of any universe. |
| Closed under rational retracts | `.IsStableUnderRetracts`, where the inclusion and projection lie in the rational category and may have denominators. No integral splitting is required. |
| Closed under shifts | `.IsTriangulated` includes `.IsStableUnderShift ℤ`, including negative and zero shifts. |
| All two-out-of-three triangle cases | `.IsTriangulated` includes extension closure, while its instances `IsTriangulatedClosed₁` and `IsTriangulatedClosed₃` supply the other two cases by rotation; isomorphism closure removes the iso-closure wrappers. |

Dependency declarations read and used:

- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralCoefficientGerm`, `integralConstantToCompletion`, and its public `CompletedIntegralCoefficients` definitions of the actual completion, finite coefficient sheaves and projections. Scalar sections reuse `integralScalarConstant`, characterized by precisely those finite projections.
- `def-pur-localized-ringed-site`: the exact Mathlib match `SheafOfModules.over`, `overFunctor`, and `GrothendieckTopology.over`; ring restriction is `Sheaf.over` as implemented by `Over.forget.sheafPushforwardContinuous`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `ringedSiteModules`; its exact Mathlib definition is `SheafOfModules`, used in Mod without constructing a new category.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and `HasDerivedCategory.standard`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, `derivedInternalHomOfUniverses`.
- `def-pur-integral-derived-operations`: `Sheaf.Paper.IntegralDerivedOperations`, `integralCompletedTensor`, `integralCompletedTensorComparison`, `integralDerivedInternalHom`, retained by the dependency repair described below; its strict representative helpers are reused to compare the generalized global operation with the original one.
- `def-weil-linear-scalar-localization`: `Sheaf.CategoryTheory.ScalarLocalization`, `ScalarLocalization`, `localization`, `map`.
- `lem-weil-linear-scalar-localization-triangulated`: `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`, `exists_triangulated_scalarLocalization`; the theorem's structure binders and normalizations unpack this exact signature.
- `def-weil-derived-complete`: `Sheaf.Paper.DerivedCompleteUnrestricted`, `IsDerivedCompleteUnrestricted`, retained literally in the global branch of the dependency repair.

The recorded proof modules are imported without `public`, except where already a
statement dependency. In particular the existing `RingedSiteDualityModel` and
`ringedSiteDualEvaluationLeft` fix actual evaluation on pure tensor representatives.
The main theorem docstring carries all twelve DAG proof steps, including the Hom/tensor
shift signs, unique completion extension, fraction descent, the explicit retract inverse,
and the triangle-morphism argument. Each construction obligation has its own named
sorry theorem, source and full natural-language proof in its owning dependency module.

Edge cases checked before finalizing the statements:

- Global and genuine slice objects are separate branches; M on a slice is arbitrary,
  not required to be a restriction of an object on X. Slice object and morphism universes
  are t+1 and t; coefficient size is max u (t+1), and the localization uses its standard
  morphism size. Neither an equality t=u nor an equality of site sizes is imposed.
- Empty X, an empty slice object, L=0, and M=0 give the corresponding zero categories
  or zero evaluations. No nonempty-site or nonzero-object assumption appears.
- The empty finite sum is covered by zero membership. Arbitrary finite sums and
  negative shifts are covered by the standard ObjectProperty classes.
- M derived complete is necessary: at a point M=E has zero finite reduction tower
  and fails the Roos completeness condition. It cannot be smuggled into the coefficient
  unit calculation. For complete M, evaluation at 1 identifies theta_R with the
  inverse completion unit of M.
- Rational retracts may have denominators; the ObjectProperty retract condition uses
  maps in Rational. It does not require idempotent completeness or an integral retract.
- The first positive exponent is n=0 in the implementation, meaning varpi^1. No
  quotient by varpi^0 or missing first reduction enters the completeness tower.
- The three triangle closure cases follow from rotation with the opposite shift
  convention; no single extension orientation is omitted.

Searches for an existing full statement (msearch.py with group Q21 and this item):

- LeanFinder: “The isomorphism locus of completed derived dual tensor evaluation after
  scalar localization is closed under retracts shifts and distinguished triangles”.
  Eight results concerned derived representative bounds and localizations, including
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` and
  `Functor.isHomological_of_localization`; no matching sheaf-coefficient statement.
- Loogle: `CategoryTheory.ObjectProperty.IsTriangulated, CategoryTheory.NatTrans.CommShift`.
  Zero hits for that combined query.
- Mathlib grep: `evaluation|retract|isIso` in CategoryTheory/Triangulated. Twenty-five
  hits included general triangle isomorphism and extension/retract-closure lemmas;
  none states this completed-evaluation theorem.
- LeanSearch: “The rational isomorphism locus of completed derived dual tensor evaluation
  is a thick subcategory of the derived category of module sheaves”. Eight results
  gave the existing derived category, standard localization and its linear and
  triangulated structures; no matching evaluation theorem.
- Project rg: `completed.*evaluation|evaluation.*completed|rational.*thick|thick.*evaluation`
  in WeilConjectures and lean/Sheaf. Only unrelated completed-tower evaluation and
  affine completed-Hom section calculations appeared. The item id and proposed
  declaration names have no existing upstream or side-project match.
- Slice interface rg: `IntegralOnSlice|DerivedCompleteOnSlices|IntegralDerivedOperationsOnSlices`
  in dag/nodes and lean/Sheaf found no existing declaration. Existing global operations
  and completeness were read in full rather than restated as private assumptions.

Validation: all three delivered modules are compiled individually by scompile.py in
import order, with the prescribed independent universes and default 60-second limit.
Only named theorem proofs are postponed. No statement correction, new DAG node,
STATEMENT-DISPUTED flag, or source fault is needed.

## Dependency modules

`def-pur-integral-derived-operations` is repaired in
`Sheaf.Paper.IntegralDerivedOperationsOnSlices`. The old module takes a scheme and
forms its global site only; it cannot supply operations on the actual over-site.
The repair publicly retains that complete original interface and adds sectionwise
restricted rings, finite quotients and projections on global/slice sites. Ordinary
reduction is the already recorded normalized scalar-extension construction;
consecutive transitions are uniquely determined by s tensor x mapped to rho(s) tensor x.
The augmentation is x mapped to 1 tensor x. The Roos unit is the actual chain map
(c,0), not an arbitrary lift into a triangulated cone. Resolving-class descent with
its representative comparison determines completion up to unique compatible isomorphism.
The existing normalized tensor-Hom model is then completed. The global representative
comparison identifies it with the old two-finite-reduction tensor construction.
The node copy changes only lean, with the required note and all helper declarations.

`def-weil-derived-complete` is repaired in `Sheaf.Paper.DerivedCompleteOnSlices`.
The published unrestricted predicate still has only a global Scheme argument.
`IsComplete` reuses it verbatim when U=none. On an actual slice it supplies the same
Roos-triangle condition for the actual quotient tower of an arbitrary good representative,
with the canonical augmentation transported through its representative isomorphism.
The product is explicitly existentially bound, as in the existing definition;
no equality or arbitrary map to a derived limit replaces the first-map condition.
The node copy changes only lean and includes its required explanatory note.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
