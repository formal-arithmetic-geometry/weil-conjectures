## Worker report

The module `Sheaf.Algebra.Homology.RingedSignedBidualLocalization` states
`CategoryTheory.ringed_signed_bidual_localization`, with one `sorry` and no definitions.
The natural-language statement is unchanged. The server compile of the final module
passed without errors or warnings (2026-10-21; 11.7 s library compilation).

The two already landed definition nodes `def-coef-hom-representative-evaluation` and
`def-sfb-internal-hom-strict-models` are added to stmt_deps to cite the actual
Hom-product projection/factorization and fixed resolution augmentation used in the
signature. Both were read, including their source declarations and docstrings.
No new nodes or dependency modules are delivered.

Hypotheses and clauses, in the order of the node:

- A ringed site small in the module universe is represented by `C : Type c`,
  `[Category.{v} C]`, `J : GrothendieckTopology C`, and module universe `max c v u`.
  The object, arrow and coefficient bounds are independent. Standard small-site
  infrastructure is `[HasSheafify J AddCommGrpCat.{max c v u}]` and
  `[J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]`.
- The commutative coefficient sheaf is `R : Sheaf J CommRingCat.{max c v u}`.
  `RingedTensorModules J R` transparently abbreviates the recorded
  `ringedSiteModules`, hence Mathlib's `SheafOfModules` over the underlying sheaf
  of rings. `[HasDerivedCategory.{w} ...]` independently sets the derived morphism
  universe. `DerivedCategory.Q` is the unbounded quasi-isomorphism localization.
- The fixed closed structure is `S : CoefficientClosedStructure
  (derivedInternalHomOfUniverses J R)`. The normalized K-flat tensor and uncurrying
  models are `T : CoefficientTensorModels J R S`. The Koszul symmetry is `s`, with
  `_coherence : RingedDerivedTensorCoherence J R S T s` expressing the recorded
  representative normalization, including its `symmetry_model` field. These
  binders select the structure the node says to fix; they impose no flatness or
  finiteness on E or D. No equality between universes is imposed.
- `ringedTensorUnitComplex J R` is the actual coefficient sheaf in degree zero,
  using `HomologicalComplex.single`. Its derived image is written explicitly
  as `DerivedCategory.Q.obj (ringedTensorUnitComplex J R)` throughout.
- The theorem supplies a family `β : ∀ E, E ⟶ Hom(Hom(E,O),O)` of actual chain maps
  for ALL `E : CochainComplex (RingedTensorModules J R) ℤ`. The repeated Hom terms
  are `homComplex (R := R)`, so D and its double Hom are the actual product-defined
  complexes, not chosen derived representatives.
- The first conjunct, for each E, quantifies over integers a,q with a+q=0 and
  q+a=0, every site object U, section x of E^a(U), every slice object W over U,
  and every section phi of D^q over W.left. It applies the actual outer
  `coefficientHomComponent` to beta(x), evaluates the resulting sheaf-Hom section
  at W and phi, and equates this to `(a*q).negOnePow` times the inner Hom projection
  evaluated at x restricted along W.hom. This is exactly the stated signed formula
  on all localized sections, including the restriction data needed for sheaf maps.
- The next conjunct quantifies over EVERY chain map beta' with the same source and
  target. If it satisfies that same full section formula, then `β' = β E`.
  Together with the supplied map and first conjunct this states existence and
  uniqueness for each E. The uniqueness premise does not require naturality,
  localization, flatness, or an arbitrary strengthening of the formula.
- The next conjunct states `(β E).f a ≫ homComplexπ D O a q k h = 0` for every
  q+a=k with k≠0. Thus every other Hom-product component vanishes as a sheaf map,
  not merely on sections at one object. This also follows intrinsically from
  the zero coefficient sheaf in degree k, but is included as an explicit clause.
- Naturality quantifies over every E' and f:E→E' and states
  `f ≫ β E' = β E ≫ Hom(Hom(f,O),O)`. Each Hom action is the first-variable map
  of the recorded `homComplexFunctor`, evaluated at O. The two opposites produce
  the required covariance; no separately chosen map appears.
- Only the final conjunct assumes `_hE` and `_hD`. They are exactly the two
  `QuasiIso` hypotheses for `((homComplexFunctor.obj (op E)).map eta_O)` and
  `((homComplexFunctor.obj (op D)).map eta_O)`. Here eta is the existing
  `WeilConjectures.SfbHomFilteredColimit.resolutionUnit J R`. Reading its definition
  shows that it is precisely `CochainComplex.toKInjectiveResolution` with the same
  Grothendieck-abelian instance used in `coefficientHomResolution` and
  `derivedInternalHomOfUniverses`. The leading underscores suppress unused-binder
  warnings; neither hypothesis is dropped or absorbed into a choice.
- The conclusion supplies gamma_E and gamma_D as ISOMORPHISMS, and fixes their homs
  by the two equations `gamma.hom = Q.map (Hom(id,eta_O)) ≫
  (coefficientHomResolutionIso ...).inv`. These equations uniquely determine the
  isomorphisms, including their inverse maps. This is exactly the fixed localization
  comparison of the node, rather than an assertion that some unrelated isomorphisms
  make the final equation true. Their existence expresses inversion of the two
  assumed quasi-isomorphisms.
- The final displayed expression writes b in full as `S.transpose` of
  `(s.braiding QE (H(QE,O))).hom ≫ S.evaluation QE O`. Thus no extra bidual
  definition or normalization hypothesis is introduced. It asserts exactly
  `b_QE ≫ H.map (gamma_E.hom.op,id_O) = Q.map (β E) ≫ gamma_D.hom`, which is
  `H(gamma_E,O) ∘ b_QE = gamma_D ∘ Q(beta_E)` in the node's composition convention.
- No K-flatness, boundedness, perfectness or bidual isomorphism is assumed or
  asserted for E or D. The first four clauses precede the augmentation hypotheses.

The declaration docstring gives all eight proof steps of the node, including the
integer sign calculation, two independent K-flat resolutions, both normalized
uncurrying computations and final cancellation. Nothing is proved in this delivery.

Dependency declarations read and used:

- `def-weil-size-convention` has a convention record, with no Lean declaration;
  it is implemented through the independent universe bounds above.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  used via `RingedTensorModules`; Mathlib supplies its category and abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex` and
  `homComplexFunctor`. `HomComplexComponents` supplies `homComplexπ`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the
  actual total tensor used by the recorded models.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, retained in the models' domains.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, its actual localization construction.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`,
  `CoefficientTensorModels`, transposition, evaluation and representative fields.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `RingedTensorModules`, `ringedTensorUnitComplex`, `RingedDerivedTensorCoherence`.
  Its existence theorem supplies exactly the structures quantified over here.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`: `coefficientHomComponent`,
  `coefficientHomResolution`, `coefficientHomResolutionIso` and its inverse
  augmentation presentation. The existing node already occurs in proof_deps,
  and is now also cited in stmt_deps.
- `Sheaf.Paper.DerivedInternalHomFilteredColimitData`:
  `WeilConjectures.SfbHomFilteredColimit.resolutionUnit`. This is a definition
  belonging to the existing `def-sfb-internal-hom-strict-models` node; it is now
  cited in stmt_deps. No filtered-colimit theorem is assumed or used.
- Other recorded proof dependencies are imported non-publicly:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`,
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.

Preflight repair: an initial version reused helper definitions from
`RingedSiteDualityMaps`. Preflight forbids importing that module because it is
attached to `def-per-ringed-site-bidual-transpose`, listed in
`coord/route-pivot-dropped.txt`. The delivered version imports no such module:
all signed section, naturality, transposition and fixed comparison formulas are
written directly in the theorem using the prerequisite declarations listed above.
No new definition copies those helpers, and no downstream theorem is a proof input.
There is no forward import cycle back to the consumer duality-maps node.

Edge cases checked before writing:

- E=0 and the zero coefficient ring: all formulas, uniqueness and both composites
  are zero; there is no nonzero-ring assumption.
- Degree zero: the sign is +1, giving ordinary sheaf bidual evaluation.
- A single complex in any positive or negative degree a: only q=-a contributes,
  with sign `(-1)^(-a*a)`. `Int.negOnePow` handles every integer exponent.
- Characteristic two: the displayed sign becomes trivial, without changing the type.
- Arbitrary unbounded complexes: all products are the existing Hom products;
  no sum over product factors, finite support or truncation is introduced.
- Every slice object and empty sites remain included. Naturality precedes the
  augmentation hypotheses, so chain maps without those hypotheses remain covered.

Searches actually run:

- `msearch.py leanfinder`, query “Signed bidual chain map of sheaf complexes and
  localization through the two Hom augmentation quasi-isomorphisms”: eight hits,
  including `CategoryTheory.Sheaf.H` and generic derived/localization factorization
  results; none states signed internal double-Hom evaluation with both comparisons.
- `msearch.py leansearch`, query “Evaluation to the double internal Hom of a complex
  of sheaves has the Koszul sign and commutes with derived localization under the two
  augmentation quasi-isomorphisms”: eight hits on `Functor.mapDerivedCategoryFactors`,
  generic localized Hom, and total shifts; no exact match.
- `msearch.py loogle`, `homComplex, bidual`: unknown identifier `homComplex`, no hits.
  Retried `HomologicalComplex, Module.Dual`: no hits.
- `msearch.py grep`, `bidual|doubleDual|toIhomIhom`, directory `Algebra/Homology`:
  no Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item ID, signed bidual,
  bidual/doubleDual and ordinary-bidual naturality found helper constructions in
  `RingedSiteDualityMaps` and a private naturality result in
  `CoefficientBidualEvaluationShiftOne`; no public declaration states the whole
  node. The item ID has no upstream match. The name index has no matching public
  signed sheaf-complex localization declaration. Further `rg` for augmentation
  found `coefficientHomAugmentation` and `SfbHomFilteredColimit.resolutionUnit`;
  the latter is already owned by a landed definition node and is used directly.

No new nodes, dependency repairs, statement corrections or disputed statements.
All writes are in the item sandbox; compilation uses scompile.py exclusively.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
