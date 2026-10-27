## Worker report

`Sheaf.Paper.FieldBoundedConstructibleTensor` states
`AlgebraicGeometry.Scheme.FieldConstructibleTensor.field_bounded_constructible_tensor`
with proof `sorry` and constructs the canonical derived degree-zero isomorphism
`singleComparison`. The other public declarations are explicit specializations of
existing categories and functors; none constructs replacement coefficients, tensor,
constructibility, or a derived category. No new node, dependency repair, or statement
correction is needed. The item's natural-language statement and proof are unchanged.

Source read: blueprint main-20261015,
`sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md`,
third paragraph “The stratum”. Its arbitrary-field argument uses exact field tensor,
finite constant models on common refinements, and the two bounded truncation towers.
The node makes the rank and support bounds explicit. The module's theorem docstring
carries each of the node's five proof steps and its dependency ids.

Hypothesis and clause correspondence:

- Scheme S: `(X : Scheme.{u})`. Noetherian is exactly `[CompactSpace X]`
  and `[IsLocallyNoetherian X]`; quasi-separatedness follows by the existing instance.
- Arbitrary field: `(κ : Type (max v (u + 1))) [Field κ]`. There is no `Finite κ`,
  finite-field, ring-characteristic, or scheme-characteristic condition. The coefficient
  universe is any enclosing size; `u` and `v` remain independent. The published
  `coefficientProEtaleModelTopology.{u,v} X` is an equivalent small representative
  of the actual weakly-etale pro-etale site, not a replacement topology.
- Constant ring sheaf κ_S: `ring X κ` abbreviates
  `ConstantCompletion.constant (coefficientProEtaleModelTopology X) κ`, i.e.
  `constantSheaf` applied to `CommRingCat.of κ`, the sheafification of the constant
  ring presheaf. `Modules X κ` is `ConstantCompletion.Mod` of this ring, the
  dependency's `ringedSiteModules`/Mathlib `SheafOfModules`.
- Ordinary unbounded derived category: `D X κ` is `ConstantCompletion.D` of the
  same ring. `tensor R` is the published `KFlatFixedTensor.derivedTensor R`, with
  `HasDerivedCategory.standard` made explicit. It is the ordinary uncompleted
  site-descent tensor; `ordinary X κ` is its existing ordinary module-sheaf tensor.
- Constructible sheaves F and G: the two
  `IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ` premises.
  This predicate is supplied by the added, already landed node
  `def-sfb-affine-locally-constructible-proetale-modules`. On a Noetherian X,
  `proEtale_noetherian_global_constructibility` identifies it with a single finite
  constructible locally closed stratification with finite constant local models.
  Its local values are finitely presented κ-modules, equivalently κ^r for finite r.
  The existential local value is inside the quantifier over covering members, so ranks
  may vary. This uses the discrete-coefficient specialization already in the DAG;
  the more general condensed-ring `IsConstantModelConstructible` definition is
  imported, but cannot be applied directly to intrinsic discrete coefficient sheaves.
- Ordinary tensor closure: the first output
  `IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ
  (((ordinary X κ).obj F).obj G)`.
- Canonical F[0] tensor^L G[0] ≅ (F tensor G)[0]: the public definition
  `singleComparison J κ F G` is precisely an isomorphism between these objects.
  `single R` is the existing single complex in degree zero followed by the standard Q.
  Its data is real: every term of F[0] is flat by `isFlat_constantFieldModule`;
  `isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite` supplies K-flatness.
  The unique normalized family from `ringed_kFlat_single_tensor_comparison`
  computes the derived tensor with G[0]; composing with Q of
  `HomologicalComplex.singleMapHomologicalComplex` identifies the termwise tensor
  as the single complex on F tensor G. The uniqueness and resolution normalization
  in that published theorem determine the family, so the `.choose` here does not
  choose an arbitrary isomorphism. This derived-category isomorphism is available
  for all sheaves, hence in particular for the constructible inputs of this item.
- Rank product on any common cover: the first output also quantifies over a finite
  `Stratification X`, a stratum `i`, and any weakly-etale chart `f : T ⟶ S.domain i`.
  Its two premises identify the pullbacks of F and G along `f ≫ S.immersion i`
  with `constantSheaf ... (ModuleCat.of κ (Fin r → κ))` and the analogous rank s.
  Its conclusion identifies the same pullback of the ordinary tensor with the
  rank `r*s` constant sheaf. In particular it applies to each member of every
  common trivializing cover on a common refinement. Covering is a joint condition;
  the per-chart calculation only needs the two given trivializations. No uniform
  rank across covering members is required. The inherited `Scheme.Stratification`
  already contains constructibility of the locally closed strata.
- A and B in D^b_c: the two `coefficientBoundedConstructibleProEtale X κ` premises.
  The added landed node `sk-def-sfb-bounded-constructible` defines this as
  constructibility of every integer cohomology sheaf and vanishing outside one
  finite interval, in this same standard derived category, with no completeness.
- Tensor in D^b_c: the first conclusion of the second universal clause is that
  same predicate applied to `((tensor (ring X κ)).obj A).obj B`.
- Support intervals: `∀ a b c d : ℤ` with vanishing of A for `n < a ∨ b < n`
  and B for `n < c ∨ d < n`, concluding vanishing of tensor cohomology for
  `n < a+c ∨ b+d < n`. Vanishing is `IsZero` in the intrinsic module category
  applied to the existing `coefficientModelCohomology`. No ordering assumptions
  are added: empty intervals are included exactly as in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (structure and
  locally affine field), with its category of morphisms; `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian`; `Mathlib.Topology.Defs.Filter`: `CompactSpace`;
  `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  the tensor is the published signed direct-sum total tensor, not a completed product.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`; `Sheaf.Paper.CondensedConstantConstructibility`:
  `ProEtale.IsConstantModelConstructible`, read with its finite-constant-model definitions.
  The explicit discrete specialization and its global equivalence are described above.
- `Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules`:
  `Scheme.coefficientProEtaleFixedModulePullback` and
  `Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf`;
  `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`:
  `ProEtale.coefficientBoundedConstructibleProEtale`;
  `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`:
  `CategoryTheory.coefficientModelCohomology` and size-correct sheafification.
- `Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility`:
  `Scheme.proEtale_noetherian_global_constructibility`, including its full global
  stratification, constructibility, covering sieve and finitely presented-value clauses.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`:
  `SheafOfModules.KFlatFixedTensor.ordinaryTensor` and `derivedTensor`;
  `Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison`:
  `SheafOfModules.ringed_kFlat_single_tensor_comparison`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat`:
  `SheafOfModules.isFlat_constantFieldModule`;
  `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`:
  `SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite`.

All recorded proof-dependency modules are imported. The main theorem remains `sorry`;
its proof is not attempted in stage 2. The canonical comparison definition only
specializes and composes existing constructions and theorems.

Edge cases checked: the empty scheme (zero module category, empty partition);
zero sheaves and zero ranks r=0 or s=0 (product rank zero); empty strata;
unordered support intervals (acyclic input, hence zero tensor);
ordered singleton intervals (degree-zero or shifted sheaves); arbitrary integer shifts;
infinite fields and arbitrary scheme characteristic. There is no hidden requirement
that the field be finite or that a cover have a common rank.

Searches (actual log retained in sandbox searches.jsonl):

- LeanSearch, “Tensor product of bounded constructible complexes over a field is bounded
  constructible”: eight generic total-tensor and module tensor hits, including
  `HomologicalComplex.tensorObj` and `Module.Finite.tensorProduct`; no exact match.
- Loogle, `"constructible", "tensor"`: zero hits (also repeated in this resumed turn).
- LeanFinder, “Derived tensor of bounded constructible sheaves over an arbitrary field is
  bounded constructible on the proetale site with sum of cohomological bounds”:
  eight light-condensed monoidal/flatness hits, no exact theorem.
- msearch grep, `constructible.*tensor|tensor.*constructible`: zero Mathlib hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for constructible/tensor combinations,
  and the item id in `lean/WeilConjectures`: no exact item statement. The nearby
  `BoundedConstructibleTensorPreservation` is for a scheme separated finite type over
  a field and ell-adic finiteness coefficients with an invertible prime; its full
  hypotheses were read and do not state this arbitrary-constant-field theorem or
  its support and rank clauses. Existing coefficient predicates, site-model tensor
  and normalized single comparison were found and reused instead of recreated.
- The upstream declaration-name index was checked for
  `FieldConstructibleTensor|field_bounded_constructible_tensor`: no match.

Validation: scompile.py compiled the module separately as a sandbox and under its actual
library module path, with no errors or warnings. Diagnostic probes were removed.
The final packet is also checked by deliver2.py --no-push before delivery.

No STATEMENT-DISPUTED flag or source correction.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
