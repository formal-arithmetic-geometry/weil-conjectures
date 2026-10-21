## Worker report

Delivered module: `Sheaf.Paper.RationalStratumIntegralModels`, namespace
`AlgebraicGeometry.ProEtale.RationalStratum`. The main theorem is
`exists_filtration_integral_models`; `exists_lisse_completed_lattice` states the
last, additional lisse assertion of the same DAG node. Both proofs are `sorry`.
The helpers contain real data or explicit predicates, with no postponed data.
No node statement changed, no dependency record was repaired, and no new DAG
notion was introduced: helpers only spell out this node's existing constructions
and normalization requirements.

Read source: Bhatt--Scholze PDF, printed pp. 60--62, Definitions 6.8.6/6.8.10,
Proposition 6.8.11(3), Lemma 6.8.13, Proposition 6.8.14(2). The source explicitly
allows constructible integral models that are not lisse. The module docstrings
carry all seven DAG proof steps and their dependencies.

Clause-by-clause statement match:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. `WithAbs` supplies the canonical topology.
  `latticeCoefficientIntegers l E` is the actual valuation subring, with only
  its topology-bearing type synonym changed. `uniformizer` is the recorded
  chosen uniformizer viewed in that field; no extra choice or assumption.
- Noetherian finite-dimensional base and ell invertible: `[IsNoetherian X]`,
  `_hdim : ∃ n, topologicalKrullDim X ≤ n`, and
  `_hl : ∀ x, IsUnit (l : X.presheaf.stalk x)`.
- Small pro-etale site, B and E: the published `latticeModuleRing` on `X.ProEt`
  gives the continuous presentations of B and E. `IsCompletedModel` includes
  an isomorphism from `pbcAdicCompletion X (pbcIntegralDatum l E)` to the
  integral lattice coefficient sheaf; every positive finite residue fixes
  this isomorphism. `finiteComparison` composes the existing canonical
  finite-coefficient comparisons and the normalized quotient ULift equivalence.
  Localization to E is the actual `integralLatticeCoefficientMap`.
- Module sheaves and ordinary sheaf tensor: `SheafOfModules.{u+1}` and
  `integralModelRationalize`, the existing sheafified change of rings.
  `tensorSection` is explicitly its presheaf tensor followed by sheafification.
- C_X is the full completed category: `IsCompletedModel` applies
  `PbcIsBoundedConstructibleComplete` to `DerivedCategory.singleFunctor _ 0`
  of the actual module, after restriction along the normalized ring isomorphism.
  Its three clauses retain intrinsic completeness, uniform constructible
  reductions and compatible etale-origin witnesses. This is membership of M[0],
  without replacing M by a completion. The raw Q and R_X are contextual in the
  node and impose no further conclusion; their published module is imported.
- Constructible rational F: `_hF : IsContinuousConstructible X (WithAbs ...) F`.
  Its finitely presented field models are finite free, exactly the source's
  finite locally closed stratification definition. We use the recorded predicate.
- Finite filtration: `m`, objects `H : Fin (m+1) → ...`, monomorphisms
  `a k : H k → F`, and successive monomorphisms `d k`; `IsZero (H 0)`,
  `IsIso (a (Fin.last m))`, and `d k ≫ a k.succ = a k.castSucc` identify
  these objects with nested subobjects from zero to F. A categorical filtration
  is understood as increasing, without requiring distinct consecutive terms.
- Quotients: `_q k : cokernel (d k) ≅ (piece (U k) (t k) ...).obj (L k)`.
  `piece` is literally the published `continuousModuleDirectImage t` followed
  by `continuousModuleExtensionByZero U`. These reuse the actual ringed functors
  and the canonical continuous-function coefficient inverse-image map.
- Geometry: `U k : X.ProEt`, `IsOpenImmersion`, `QuasiCompact`,
  `QuasiSeparated`; `t k : S k → (U k).left`, `IsClosedImmersion`,
  `IsReduced (S k)`. The conclusions `hS`, dimension bounds and local unit
  assertions give each S_k the required noetherian, finite-dimensional,
  ell-invertible hypotheses. The instance `hS k` is passed explicitly to the
  constructibility predicate; no extra universe equality is imposed.
- Integral N_k: the family `N` consists of actual integral modules, and its
  `IsContinuousConstructible` clause is precisely finite-stratum models
  B_S tensor_A P with P finitely presented. Torsion is permitted.
- M_k: no arbitrary M family is quantified; it is the expression
  `(piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)`.
  Both its continuous constructibility and its completed membership are asserted.
- First displayed isomorphism: `α k : integralModelRationalize ... (N k) ≅ L k`.
- Final displayed isomorphism: `β k`, with the equation
  `β k = e k ≪≫ (piece ...).mapIso (α k)`. Thus it is the scalar comparison
  followed by the actual functors applied to the chosen lattice isomorphism.
- Normalization: `IsNormalizedComparison ... (e k)` quantifies every n≥0,
  site object W, factorization W→U, and section on the actual closed base
  change. It says e sends varpi^(-n) tensor the open-extension generator of s
  to the open-extension generator of varpi^(-n) tensor s. `generator` uses
  the actual direct-sum presheaf inclusion and module-sheafification unit.
  This specifies the sequential-localization comparison on all generators,
  not merely a Nonempty isomorphism. Sheafification and colimit universality
  determine the map from those equations.
- Additional lisse clause: `exists_lisse_completed_lattice` has the same base
  hypotheses and `[L.IsFiniteLocallyFree]`, and concludes constructible N,
  its full completed degree-zero membership, and its rationalization isomorphism.

Dependency declarations read and reused (module → declarations):

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification` →
  `Topology.FiniteLocallyClosedStratification`,
  `Scheme.FiniteLocallyClosedStratification`; these govern the geometric
  stratification meaning. The continuous predicate internally uses the recorded
  scheme stratification, equivalent here because the base is noetherian.
- `Sheaf.Paper.ContinuousConstructibleModule` → `IsContinuousConstructible`,
  `continuousModulePullback`, `continuousCoefficientModule`, canonical coefficient maps.
- `Sheaf.Paper.IntegralModelOpenClosedPieces` → `openSliceModules`,
  `continuousModuleDirectImage`, `continuousModuleExtensionByZero`,
  `integralModelRationalize`, `integralModel_open_closed_pieces`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` →
  `Scheme.proEtaleRingedDirectImage`, `Scheme.proEtaleRingedExtensionByZero`,
  `Scheme.proEtale_ringed_open_closed`.
- `Sheaf.Paper.AdicCoefficientDatum` → actual coefficient-ring and reduction
  constructions. `Sheaf.Paper.IntegralUniformCoefficient` publicly retains
  `PbcIsBoundedConstructibleComplete` and its finite-extension specialization.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` →
  `Scheme.integralCoefficientULift`, `Scheme.integralStratifiedPerfectCharacterization`.
- `Sheaf.Paper.PbcRationalCategory` → `PbcRationalCategory`, `pbcRationalization`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` → coefficient
  constructions and `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale` → `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules` → `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` → the existing
  independent-universe tensor structures. No second sheaf tensor is defined.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.HomologySequence` →
  `DerivedCategory`, `singleFunctor`, `homologyFunctor`, `homologyFunctorFactors`.
- `Sheaf.Paper.FiniteModelStratumFiltration` →
  `CondensedRing.exists_finiteModelStratumFiltration` (proof import).
- `Sheaf.Paper.ContinuousCoefficientRealizations` → `chartComparison_naturality`
  and the actual realization isomorphism (proof import).
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence` →
  `InternalAbelianSheafModule.sectionModuleEquivalence` (proof import).
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction` →
  `Scheme.continuousCoefficientImmersionRestriction` and its normalized maps.
- `Sheaf.Paper.LisseEConstructibleIntegralLattice` →
  `exists_constructible_integral_lattice` (proof import).
- `Sheaf.CategoryTheory.ScalarLocalizationModuleColimit` →
  `CategoryTheory.scalarLocalization_moduleColimit` (proof import).
- Mathlib `AlgebraicGeometry.Noetherian`, `Morphisms.Immersion` and
  `Topology.NoetherianSpace` provide all recorded Mathlib-only proof leaves.

Edge cases checked: m=0 makes Fin m empty and permits exactly the zero filtration;
X empty and F=0 are allowed. Zero-rank lisse modules and torsion integral models
are allowed. No reducedness is required of X, only of S_k. No nonempty stratum or
positive filtration length is assumed. Fractions include n=0, the normalized unit.
All variable and universe binders are explicit (`autoImplicit false`); scheme
universe u and coefficient/module universe u+1 preserve the small site's sizes.

Searches, 2026-10-21 (msearch.py, group Q14 and this item):

- LeanFinder: “Constructible continuous l adic sheaves admit finite stratum
  filtrations with integral lattices”: 8 scalar Ideal.Filtration hits; no match.
- Loogle: `SheafOfModules, Localization`: 0 hits.
- LeanSearch: “Constructible l-adic sheaves have integral lattices and finite
  stratum filtrations”: 8 general sheaf, finite-type, colimit and constructible-set
  hits; no theorem with this statement.
- Mathlib grep via msearch: `[Ll]attice.*[Ss]heaf|[Ss]tratum.*[Ff]iltrat|[Cc]onstructible.*[Ff]iltrat`:
  5 ideal-sheaf lattice hits, no match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `stratum.*integral|rational.*stratum` found no exact existing declaration.
  Existing lattice, stratum-filtration and open/closed lemmas each provide only
  parts; the downstream ContinuousRationalDerivedRealization cites this proof
  in prose and does not state this standalone filtration theorem.
- rg for `rationalStratum|exists_filtration_integral_models|IsCompletedModel|IsNormalizedComparison`
  in both libraries found no declaration-name collisions.

Validation: scompile.py compiled the single file as both a sandbox module and its
library module with no errors or warnings (12.0 s and 12.2 s on the final compile).

## Second reading by Q14

A second pass by this same dispatcher worker reopened the node and the complete
Lean file; it is a self-check, not an independent agent review. The dispatcher
explicitly forbids spawning agents and assigns the maintainer the independent
review. The check matched the base hypotheses, filtration endpoints and inclusions,
quotient object, actual open/closed functors, reduced geometry, stratum hypotheses,
constructible models, completed predicate, finite residue normalization and fraction
formula against the clauses above. It found that an initial final-isomorphism clause
allowed an arbitrary isomorphism to the rational stratum piece. This was replaced
by β together with its equality to e composed with piece.mapIso α. No statement
correction was needed. The main theorem and additional lisse theorem both have
only sorry proofs, and no definition contains sorry. All helper declarations carry
the owning node's blueprint tag and source docstring. Maintainer independent
review remains the authoritative mathematical reading.
