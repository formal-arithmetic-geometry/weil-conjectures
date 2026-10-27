## Worker report

The module `Sheaf.Paper.PointEvaluationCompletionNormalization` states
`WeilConjectures.PointEvaluationCompletion.point_evaluation_completion_normalization`.
Its only postponed proof is that named theorem. All helper definitions have real
terms. The accepted natural-language statement and split are unchanged.

Hypothesis correspondence:

- `D : FiniteFieldDatum` fixes the prime, finite field, and fixed algebraic closure;
  `Spec (.of D.k)` is the specified geometric point, with its original small
  pro-etale site (object universe u+1, morphism universe u).
- `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give exactly the coefficient-prime
  conditions. `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` give the finite coefficient extension.
  `R` is the recorded integer ring, lifted to the module-carrier universe only;
  `B` is the recorded inverse limit of constant positive quotient coefficients.
  The published tower index `n : ℕ` denotes exponent `n+1`, including m=1.
  The recorded chosen uniformizer is used through those quotient constructions.
- `L`, `hobj`, and `_hmap` specify exactly the constant-module sheafification
  followed by change of rings, on both objects and morphisms. `[L.Additive]`
  permits its termwise action. These binders describe the actual functor from
  the node, rather than introducing an arbitrary extension functor.
  `model D l E L P` is C=L(P).
- `_hP` is boundedness of P; `_hPproj` says every term is finitely generated
  projective over R. These are precisely the representative conditions in
  `DerivedCategory.IsPerfectRingComplex`, with P itself fixed as in the node.
- `J`, `_hJ`, `_hJflat` specify its boundedness and flat terms.
  `_hCflat` states the separately stipulated flatness of every term of C.
- `eta`, `_heta` give the actual unit x ↦ 1 tensor x on every degree, using the
  recorded `PointDerivedHom.generator`. `[QuasiIso eta]` is its assumed
  quasi-isomorphism, not an assumed chain isomorphism.
- `_hBsections` is bijectivity of the actual constant-values ring map R→ΓB.
  Thus it specifies ΓB=R through that map, rather than an unspecified equivalence.
- `_hB`, `hC`, `hJ`, `_hT` are exactly membership of B[0], C, J and the signed
  total in the bounded constructible derived-complete category. `hC` and `hJ`
  use `finiteTorConstructibleIntegral`, which includes both that membership and
  one uniform Tor interval for all positive reductions.
- `e` ranges over every chain map from the actual signed total to B[0].

Conclusion correspondence:

- The existential `goodC` and `goodJ` supply the K-flat flat-term representatives
  needed to evaluate the existing completed-tensor representative comparison;
  they impose no new hypothesis. The node's proof step 1 establishes them.
- `rho` is an isomorphism of the two strict complex towers, so it includes every
  transition and every differential. `Balanced ... rho` gives its inverse-direction
  formula (c tensor a) tensor (j tensor b) ↦ (c tensor j) tensor ab on every
  local homogeneous generator. Since rho is an isomorphism, this fixes the forward
  rule (c tensor j) tensor a ↦ (c tensor 1) tensor (j tensor a) as well.
  The formulas use the sheaf tensor's canonical local generators; they do not
  identify sheaf tensor with sectionwise tensor.
- `tensorModelIso` names the existing representative isomorphism, with explicit
  endpoints to prevent expensive unfolding. `chi` is the localized identity-extension
  unit followed by the inverse balancing cone map and that representative comparison.
  `IsIso (chi ...)` is precisely invertibility of χ_D after localization.
- `UnitCoordinates` gives the actual quotient-product coordinate, at every degree,
  level and site object, and the zero shifted-product coordinate. Both D and B[0]
  have this predicate. The shifted projection has degree i→i-1, including negative i.
- The quantified quotient equality is the strict reduction square for e at every
  positive level. `tower.map e` is the actual reduction tower map. For B[0], its
  identity scalar reduction is canonically A_(n+1)[0] by multiplication.
- The equality involving `unit` and `completion.map e` is the equality of chain
  maps H(e_m)χ_D=χ_B e before localization, with χ_D here viewed in its quotient
  Roos presentation. `completion` is the specified functorial shifted cone, whose
  map is induced on both product coordinates, never a triangle filler.
- `b` and `b.hom = Q.map ...` say that χ_B is invertible and is the SAME stipulated
  identity-extension map. Its inverse is used in the following completed-pairing formula.
- `∃! v, chi ... ≫ v = Q.map e` is the completion-reflector characterization of
  the pairing from the completed tensor/internal-Hom adjunction (node proof step 5).
  `completedPairing` is the explicit map obtained by the representative
  comparison, H(rho), H(e_m), and b.inv. The next equation uses it. Together these identify the canonical pairing
  with χ_B^(-1)H(e_m), and state its composite with χ_D is e. The pairing is thus
  characterized independently by its ordinary precomposition and identified with
  the strict-cone formula; equality is not inferred from finite derived reductions.
- `beta` is a chain map on ordinary module total tensors; its generator equation
  is x tensor h ↦ (eta x) tensor h. Bounded projectivity of P makes this source a
  representative of the stated derived tensor.
- `betaCompletionEquation` is the equality with `canonical.completion` and normalizes beta followed by completion
  against the SAME published canonical completion chain map. That witness has both
  finite quotient coordinates and zero shifted coordinate, as required.
- The final equation localizes beta using the canonical lax monoidal map for Q,
  transports sections through `pointIntegralDerivedFactors`, and applies Γ(chi).
  Its right side is the inverse of `pointIntegralTensorComparison`, precomposed
  with the actual localized eta, with the ΓJ factor transported by the recorded
  exact-sections identification. This is exactly τ^(-1)=Γ(χ_D) beta with all
  model comparisons shown. No inverse for eta before localization is demanded.

Dependency declarations read and used (including their public reexports):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its coefficient-extension
  import: `Padic.coefficientExtensionIntegers`, `coefficientExtensionRing`, the
  chosen uniformizer and finite quotient conventions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; the imported
  `completedIntegralCommRingSheafUnrestricted` and completed coefficient unit.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`; the recorded
  module version in `Sheaf.Paper.PointDerivedHomModels`: `extensionObject`,
  `extensionMorphism`, `generator`, `coefficientMap`, `total`, `totalElement`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: the existing sheaf tensor
  and `SheafOfModules.IsFlatOnSite`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` (its bounded finite-projective clauses
  are expanded because the node fixes P itself).
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, as
  used by the recorded `PointDerivedHom.total` with its signed total differential.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites` and its public `FiniteTorAmplitude`:
  `finiteTorConstructibleIntegral`, the integral clause of the dependency node.
- `Sheaf.CategoryTheory.StrictRoosModel`: the specified shifted-cone convention;
  `integralOperationsRoosFunctor` is its published strict tower-of-complexes
  presentation used throughout the completed coefficient constructions.
- `Sheaf.Paper.IntegralDerivedOperations` and the recorded
  `IntegralDerivedOperationsOnSlices`: `integralCompletedTensor`,
  `integralCompletedTensorComparison`; no new tensor is defined.
- `Sheaf.Paper.DerivedPullbackTensorHom` through the point tensor interface:
  the same constructible integral tensor; the completed adjunction is rendered
  by its unit-normalized unique extension as in proof step 5.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedScalarIdentityUnit`, `completedScalarRoosEndomorphism`, and the
  identity coefficient case of the canonical finite-free comparison.
- `Sheaf.Paper.PointFibreDerivedTensor` and its public model interfaces:
  `PointIntegralTensorData`, `PointIntegralTensorCanonical`,
  `pointIntegralTensorComparison`, `pointIntegralComplexSections`,
  `pointIntegralDerivedFactors`, `pointFibreIntegralAmbient`.

All stated proof dependencies are available through the imports; in particular,
`IntegralPointCoefficientAdjunction`, bounded-flat K-flatness, the total-tensor
model, strict reduction-tower comparison, constant/Koszul completion comparison,
completion reflector, and ringed point evaluation. The parent
`PointCompletedEvaluation` is deliberately not imported: it cites this item as
its proof dependency, so importing it would create the dependency cycle.

Edge cases checked: P=0, J=0 and zero e; degree-zero finite free P; nonzero
negative cochain degrees; the smallest quotient m=1 (n=0 in the API); arbitrary
ramification of E; eta merely a quasi-isomorphism, not a chain isomorphism;
non-sectionwise sheaf tensor; and identity coefficient extension. All formulas
retain arbitrary degrees and local sections and the zero shifted cone coordinate.
The spectrum of a field is nonempty as required, and l=p is excluded explicitly.

Searches: msearch LeanFinder, query "Strict quotient tower completion of a sheaf
tensor pairing and normalization of the inverse point sections tensor comparison",
returned sheaf component and sheafification lemmas, no match. Loogle
"CochainComplex.mappingCocone, TensorProduct.assoc" returned no hits; the separate
"CochainComplex.mappingCocone" query found the construction and its projections,
not this theorem. msearch grep "completed.*pairing|completion.*normalization"
found no Mathlib match. LeanSearch query "Strict quotient tower completion of a
tensor pairing with zero shifted cone coordinate and inverse point sections tensor
comparison" returned ordinary quotient-tensor equivalences and unrelated tensor
lemmas, no completed sheaf/point statement. Searches of `WeilConjectures` by the
node id and the completion/pairing terms found no declaration for this statement.
The corresponding `Sheaf` search found the parent `PointCompletedEvaluation`
(specialized to projective dual evaluation and depending on this item), the point
tensor models and other completion-unit results. None states the arbitrary-e,
arbitrary-bounded-flat-J normalization of this item. The search service output
is preserved in `searches.jsonl` in the worker sandbox.

No new DAG nodes, dependency replacement modules, statement correction, or
STATEMENT-DISPUTED claim is needed. The maintainer provides the independent review.

Implementation notes: `chainChi` and `unitCompletion` give explicit endpoints for
the same augmentation and canonical precomposition; `betaCompletionEquation`
only names their displayed chain-map equality. `completedPairing` composes
H(rho) and H(e_m) before applying Q, an equivalent functorial expression that
avoids unfolding separate localized endpoints. These are helpers of this node,
not new mathematical notions. No diagnostic commands or heartbeat changes remain
in the delivery module.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
