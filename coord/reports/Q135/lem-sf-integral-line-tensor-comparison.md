## Worker report

The module `Sheaf.Paper.IntegralLineTensorComparison` states
`WeilConjectures.integralLineTensorComparison`. Its only postponed theorem is that
statement, with the six-step DAG proof in its docstring. Ten helper definitions
assemble existing single, tensor, quotient, localization and cone functors and maps.
Every helper has real data; none chooses a comparison or assumes its invertibility.
No node statement, dependency record or dependency list has changed.

The source was read directly from the local Bhatt--Scholze PDF, pp. 22--24:
Definition 3.4.10 defines completion of ordinary derived tensor, Lemma 3.4.12(4)
gives local completeness via natural quotient maps, Proposition 3.5.1 gives the
quotient-tower completion, and Definition 3.5.2 uses modules over the completed
ring. These agree with the existing global branch of the recorded slice interface.

Hypotheses and objects, clause by clause:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension of Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Its valuation ring, chosen uniformizer and finite
  quotients are the recorded coefficient-extension construction used by
  `completedIntegralCommRingSheafUnrestricted` and `integralCoefficientCommRingSheaf`.
  No independent coefficient ring, coefficient action or quotient maps are supplied.
- Scheme with ell invertible: `(X : Scheme.{t})` and
  `_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x)`; invertibility is local on X.
- Small pro-etale site: `IntegralOnSlice.topology X none` is definitionally
  `Scheme.ProEt.topology X`. Its object universe is `t+1`, Hom universe `t`.
- R is the completed coefficient sheaf, not the discrete constant valuation ring:
  `IntegralOnSlice.ring l E X none` is the recorded
  `completedIntegralCommRingSheafUnrestricted l E X`.
- C in D(R): `C : IntegralOnSlice.D l E X none`, the actual unbounded derived
  category of all R-module sheaves in universe `max u (t+1)`.
- C is derived complete: `hC : IntegralOnSlice.IsComplete l E X none C` is
  definitionally `IsDerivedCompleteUnrestricted l E X C`. It retains the augmented
  reduction-tower Roos-triangle condition and does not postulate a completion map.
- T is an R-module sheaf locally isomorphic to R:
  `T : IntegralOnSlice.Mod l E X none` with `[T.IsFiniteLocallyFreeOfRank 1]`.
  The existing upstream predicate uses covering local generators with one-element
  bases, precisely local rank one. `integralLineSingle` places T in degree zero.
- Ordinary derived tensor: `integralLineOrdinary` uses the recorded
  `(IntegralOnSlice.duality ...).closed.tensor`. Its `models.iso` computes the tensor
  by `coefficientTotalTensor`, the existing `CochainComplex.mapBifunctor` total tensor
  with direct sums and differential d_P tensor 1 + (-1)^p 1 tensor d_T.
- Completed tensor: `integralLineCompleted` uses the dependency's recorded
  `IntegralOnSlice.completedTensor` on C and Q(T[0]). This is completion of the
  ordinary tensor by the actual strict reduction-tower Roos construction.
  `completedTensor_global_comparison` in the dependency identifies it with the
  original finite-tensor construction `integralOperationsTensorOnGood`.
- C_n and T_n: `integralLineFiniteComplex` applies the canonical change of rings
  along `IntegralOnSlice.projection`, termwise to P and T[0]. Since T is locally a
  free line, T[0] and T_n[0] themselves are K-flat; the conclusion supplies this
  property as `hT` rather than adding it as a hypothesis. The finite ring at Lean
  index n is the source's exponent n+1, covering exactly all positive exponents.
  `integralLineFiniteTensor` tensors these reductions over that finite ring;
  `integralLineFiniteRestrict` restores the R-action along the actual projection.

Conclusions and canonical-map clauses:

- The displayed comparison is `integralLineComparison`, defined by whiskering the
  existing `IntegralOnSlice.completionUnit` with ordinary tensor. This fixes its
  components before the theorem is stated. The first conjunct asserts `IsIso` of
  its component at `(C,T)`. It is not existence of an arbitrary isomorphism.
- Naturality in C and line isomorphisms is the second conjunct's commutative square,
  with `f : C ⟶ C'`, complete C', rank-one T' and `eT : T ≅ T'`.
- The representative clause quantifies over EVERY flat-term K-flat P and EVERY
  `e : Q(P) ≅ C`. The predicate is exactly the dependency's `Good`. The theorem
  supplies K-flatness of T[0] and goodness of S = Tot(P tensor T[0]); these are
  conclusions needed to instantiate the dependency's representative comparison.
- `integralLineRepresentativeIso` is fixed by `duality.models.iso` and e.
  The first representative equation transports the actual comparison through this
  isomorphism and `completionComparison` and equates it to `Q.map (roosUnit S)`.
  The dependency defines `roosUnit` by `mappingCocone.lift` with product augmentation
  and zero second cochain, so this is exactly the requested canonical map into
  Cone(1-s)[-1], including the zero shifted-product component.
- The finite clause provides an isomorphism beta from the finite reduction of S to
  Tot(P_n tensor T_n). Its equation on all total-degree tensor generators is
  `a tensor (x tensor y) ↦ (a tensor x) tensor (1 tensor y)`, the source's ordinary
  balancing identification in the coefficient-first convention of changeOfRings.
  There is no unspecified finite identification. These generators locally generate,
  so their formula also determines compatibility with quotient transitions.
- The final square uses `integralLineRoosProjection`, defined as the actual
  `mappingCocone.fst` followed by `Pi.π n`, then the restriction of beta. It asserts
  that projecting the specified comparison gives the actual reduction augmentation
  followed by beta. This expresses the finite-reduction clause through the actual
  projections, rather than through arbitrary inverse isomorphisms. Under the
  normalized derived coefficient adjunction, the augmentation has identity adjunct;
  hence the square identifies the reduction of the comparison with beta. Since
  beta and the comparison are invertible, the adjunct of the target projection is
  invertible as well. The docstring records this last argument explicitly.

Dependency declarations used (full recorded source interfaces were opened):

- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`; its public imports
  expose the completed coefficient sheaf and actual finite projections.
- `Sheaf.Paper.DerivedCompleteOnSlices`:
  `WeilConjectures.IntegralOnSlice.IsComplete` (global branch = the recorded
  `IsDerivedCompleteUnrestricted`), with its complete docstring and Roos definition.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `WeilConjectures.IntegralOnSlice.completedTensor`, and its `Mod`, `D`, `Cx`,
  `ring`, `finite`, `projection`, `reduction`, `generator`, `level`, `tower`,
  `augmentation`, `Good`, `completion`, `completionComparison`, `roosUnit`,
  `completionUnit`, `duality` and `completedTensor_global_comparison`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, via
  the recorded `coefficientTotalTensor` wrapper, not a second total tensor.
- `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`, used both directly and by `Good`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank` (rank 1); its definition and docstring
  were read, including the local generators and one-element basis condition.
- `Sheaf.CategoryTheory.RingedSiteDualityMaps` (publicly imported by the recorded
  integral-operations module): `CategoryTheory.RingedSiteDualityModel`, with the
  recorded total-tensor model `WeilConjectures.CoefficientTensorModels.iso`.

Every recorded, stated proof dependency's module is imported without `public` when
it is not already a statement dependency. This includes ExtensionIntegersDvr,
CompletedConstantSheafReduction, LocalizedModuleExactIndependent,
ProEtaleCountableProductsExact, KFlatResolutionIndependentCoefficients,
ChangeOfRingsKFlat, EtaleDerivedScalarTensor (the current recorded derived-change
interface), FiniteFreeCompletedScalarComparison, IntegralOperationsWellDefined,
AcyclicKFlatTensor and SheafRingDerivedCoefficientAdjunction. The general
`derivedChangeOfRingsIndependentCoefficients` interface used by the actual reduction
construction is already in the public dependency import closure. There is no need
to rebind or repair the proof dependency's more specialized current record just to
state this item.

Edge cases checked: empty X and the resulting zero sheaf category; C = 0;
T = R (identity tensor/completion comparison); nontrivial locally trivial lines;
exponent 1 (Lean n=0); unbounded C and P; arbitrary cochain degrees p,q,k, including
negative degrees; schemes without quasi-compactness or connectedness. No global
trivialization, chosen basis, boundedness, constructibility or finiteness of X is
assumed. Scheme and coefficient universes remain independent throughout.

Searches performed with the required msearch.py wrapper:

- LeanFinder: “A derived complete sheaf complex tensored with a locally free rank
  one sheaf has ordinary derived tensor equal to completed derived tensor”. Eight
  hits, principally LightCondensed monoidal structures and classical AdicCompletion
  tensor facts; no derived sheaf comparison or normalized cone map.
- Loogle: `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. Five hits.
  Read AsTensorProduct.lean around lines 318--340: the equivalence concerns ordinary
  finite modules over a Noetherian ring; it is not this sheaf-derived statement.
- Mathlib grep: `completedTensor|derivedComplete|DerivedComplete`, subdirectory
  `Algebra/Homology`: zero hits.
- LeanSearch: “Ordinary derived tensor with a locally free rank one sheaf agrees
  with completed tensor on derived complete complexes”. Eight classical
  AdicCompletion tensor hits; none has the objects or conclusion of this node.
- Source/project rg: `integralLineTensorComparison|integralLineComparison|
  completed.*[Ll]ine|[Ll]ine.*completed` in WeilConjectures, lean/Sheaf and the
  upstream name index. No existing theorem or canonical comparison; relevant
  project hits concern twists or scalar extension with different statements.
- Source grep for `lem-sf-integral-line-tensor-comparison`: no matches.
- Project search for `IsFiniteLocallyFreeOfRank 1` located the shared upstream
  predicate used here. Project source searches located the recorded completion
  unit and representative model, so neither was duplicated.

Validation: scompile.py compiled the delivered module as a single file against the
published library and side overlay, including the module-system library check;
there were no errors or warnings. The first compile took 9.8 seconds for the
library module. No direct compiler, global build, live edit or Git mutation was
run by the worker. There is one theorem with `sorry`, as required for stage 2.
There is no STATEMENT-DISPUTED flag and no statement correction.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
