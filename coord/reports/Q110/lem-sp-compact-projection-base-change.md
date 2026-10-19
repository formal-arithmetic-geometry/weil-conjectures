## Worker report

The delivery states `lem-sp-compact-projection-base-change` in
`Sheaf.Paper.SmoothPurityCompactProjectionBaseChange`, declaration
`AlgebraicGeometry.ProEtale.CompactProjectionBaseChange.compact_projection_base_change`.
The natural statement is unchanged. There is one postponed proof, that theorem;
its docstring reproduces all five steps of the DAG proof and names their inputs.
All helper definitions have real data. No definition chooses a functor or map
from an existence theorem proved by `sorry`.

The recorded interfaces do not already package the ordinary coefficient-tower
operations and the complete compactification diagram needed by this item.
The module exposes their canonical presentations as helper structures belonging
to this item. Their existence is a conclusion, and the compatibility is universal
for every normalized presentation. In particular the theorem does not assume a
supplied projection/exchange coherence, an arbitrary comparison isomorphism,
proper-base-change invertibility, or a projection formula. The same construction
works on the vertical ringed site itself, preserving coefficient transitions.
These helpers encode the operations and canonical maps already specified in this
node, rather than introduce an independent mathematical notion requiring a new
DAG definition node.

### Hypotheses and objects

- The global algebraic closure of the finite field, including its characteristic
  prime, is `D : WeilConjectures.FiniteFieldDatum`. The coefficient prime is
  `(l : ℕ) [Fact l.Prime]` with `_hl : l ≠ D.p`.
- `GeometricAssertion` quantifies over `X Y Y' : Scheme.{u}` with the three
  `Over (Spec (CommRingCat.of D.k))` instances. Each of their structure maps has
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`. Thus all three schemes
  are separated and of finite type over the specified field.
- The named maps `f : X ⟶ Y`, `v : Y' ⟶ Y` have the corresponding `IsOver`
  instances. Only `f` is given separatedness and finite type explicitly. There
  is no flatness, smoothness or properness assumption on `v`.
- The chosen compactification is `q : Compactification f`, with open immersion
  `q.i`, proper map `q.g`, and its recorded factorization equation. It is the
  upstream notion recorded by def-weil-compactifications-refinements, not a copy.
- The arbitrary realizations of the two pullbacks are `X' B'`, their maps
  `a f' b p'`, and `_sx : IsPullback a f' f v`,
  `sb : IsPullback b p' q.g v`. The open square is
  `sj : IsPullback a j' q.i b`, with `[IsOpenImmersion j']` and
  `_hf' : j' ≫ p' = f'`. These express exactly the base-changed compactification.
  Using arbitrary pullback realizations includes the literal Mathlib pullbacks.
- Setting (i) quantifies over every `A : Type (u+1)` with `[CommRing A] [Finite A]`
  and `_ha : ∃ r : ℕ, 1 ≤ r ∧ (l ^ r : A) = 0`. `finiteCoefficients A`
  is the actual constant commutative ring sheaf on each small pro-etale site,
  with `proEtaleConstantDirectImageMap` as structural map.
- Setting (ii) quantifies over `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
  `TowerCoefficients l E c` requires that the underlying ring presheaf is
  literally `spCoefficientPresheaf l E T`, fixes every structural map at
  `(n,U)` to the constant-ring map on `O_E/(ell)^(n+1)`, and supplies a normalized
  equivalence from the recorded `spCoefficientTowers l E T`.
  This equivalence fixes entire module presheaves and module morphisms, hence
  fixes restrictions and every semilinear transition, not merely the levels.
- Ordinary sites have object universe `u+1` and Hom universe `u`. The vertical
  sites `ℕ × T.ProEt` retain these universes. Coefficients and section modules
  have universe `u+1`. `E` and the schemes may be taken in any common ambient
  universe, and the coefficient ULift is the one already used by the tower
  declaration. No equality of the site object and Hom universes is imposed.

### Each operation and clause

`Mod` and `Der` are the existing ProjectionRestriction abbreviations for sheaves
of modules over a commutative ring sheaf and their ordinary unbounded derived
localization. There is no bounded, constructible, cartesian, derived-complete
or completed subcategory restriction. In the finite case this is the intrinsic
constant-ring presentation of the node's category; the recorded constant-ring
and fixed-scalar realization equivalences identify it with the other recorded
finite-module presentations. In the tower case `TowerCoefficients` gives the
specified equivalence with the actual tower category before deriving it.

`Presentation.operation f : Operation ...` is pinned by
`Presentation.coefficient` to `c.moduleMap f`. `Operation.pushforward` is the
existing sectionwise module pushforward, `Operation.pullback` its existing
module left adjoint. `Operation.left` is its exact termwise derived localization,
`Operation.right` the ordinary K-injective right derived direct image, and
`Operation.derivedAdjunction` their canonical derived adjunction. These are
existing constructors, not fields of unconstrained functors in this delivery.
Thus in setting (ii) direct image is the total right derived functor on the
system category, rather than a proposed identification with independently
computed derived direct images of the individual levels.

`Presentation.tensor T : TensorModel ...` retains the flat K-flat representative
isomorphism with the signed total tensor and its localization descent property.
`ordinaryTensor` retains the pure-section normalization; `tensorComparison`
retains the actual signed total-complex equation on all flat K-flat pairs.
Consequently it supplies precisely the uncompleted derived tensor and canonical
pullback/tensor isomorphism, rather than a second tensor construction.

`siteSquare` is the composite of the existing ordinary pullback-composition
isomorphisms and the commutative-square equation, with the coefficient index
unchanged in systems mode. `rightSections` fixes the corresponding ordinary
module direct-image square on every section. `ordinarySquare` is its conjugate
under the actual module adjunctions, and `square` is its exact termwise derived
localization. This retains the canonical composition comparisons.

`OpenModel` presents the exact left adjoint of the actual open inverse image,
with invertible unit. This fixes open extension by its universal property up to
the unique adjunction-preserving isomorphism. `shriek` is termwise localization,
and `openAdjunction` is localization of that same adjunction. `gammaInvNat` uses
the existing `Adjunction.projectionMap`; its transpose is open unit tensor identity
followed by the inverse tensor comparison. `betaInvNat` is the actual adjunction
mate of the inverse open square. `OpenComparisons` records only invertibility
of these two open maps, the conclusion of the recorded open-normalization lemma.
The maps `gammaIso` and `betaIso` invert these actual natural transformations.

- `Presentation.exchange` calls the recorded
  `CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData`.
  Thus beta is proper exchange at `j_!M` followed by `Rp'_*` of open base change.
- `Presentation.projection` calls the recorded
  `CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData`.
  The proper map is the existing counit-defined right-adjoint projection, then
  `Rp_*` of the actual open tensor isomorphism. The pullback in its target is
  written literally as `p^* ⋙ j^*`, implementing the node's stipulated
  `j^* p^* ≅ f^*` identification without choosing another comparison.
- `targetIso` first applies the canonical tensor comparison for `a=u`, then
  the inverse open square and the inverse proper square to its coefficient
  factor. It is precisely `u^*(M ⊗ j^*p^*K) ≅ u^*M ⊗ j'^*p'^*v^*K`.
- `pulledProjection` is inverse source tensor comparison followed by
  `v^* PF_f`. `tensorTargetExchange` is beta at the tensor input followed by
  compact-support image of `targetIso`. `tensorExchange` is beta_M tensor
  identity. The first clause of `DiagramAssertion` is consequently exactly
  the forward identity of the node, including its source and target identifications.
- The second clause quantifies over arbitrary morphisms `r : M ⟶ N`,
  `z : K ⟶ L` and gives the source/target functoriality square for that same
  common route. This is simultaneous naturality, not merely pointwise equality.
- The final clause assumes `IsIso` of beta_M, beta at the tensor input, PF_f
  and PF_f'. Its equation is inverse target identification, inverse beta,
  `v^*` of inverse PF_f, source tensor comparison, then beta_M tensor identity,
  equal to inverse PF_f'. This is the node's inverse equation with all
  implicit identifications expanded. No additional isomorphism hypothesis is used.

The main theorem asserts nonempty normalized presentations and validity of
`GeometricAssertion` for every such presentation in both settings. Therefore
existence of the canonical operations is not a hypothesis or a vacuous universal
condition, and the assertion does not depend on selecting a favorable presentation.

### Dependency declarations read and used

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its instances.
- def-weil-scheme-morphism-properties is a collection record with no declaration;
  the notions used are Mathlib `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `Scheme.Over` and `Scheme.Hom.IsOver`, whose signatures were read.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its recorded base-change
  declarations were read with `scompile.py --source`; pullbacks and their projections
  are the Mathlib `IsPullback`/`pullback` conventions it documents. This module is
  already publicly imported through FiniteFieldFiber.
- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement`,
  the underlying `Compactification`, and its open/proper factorization.
  `Compactification.BaseChange` was also read for its base-changed open square.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, and its constant-ring comparisons, read.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `AlgebraicGeometry.ProEtale.derivedTensor`, read from current server source;
  reexported. Its intrinsic counterpart here is the dependency's K-flat tensor model.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingDerivedPullback` and its ordinary adjunction;
  the underlying arbitrary-ring operations are reused through `Operation`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero` and `sfIntrinsicModuleEquivalence`, read;
  the equivalent open-adjunction presentation is necessary also for systems.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientPresheaf`,
  `spCoefficientTowers`, `spEllIdeal`, `spCoefficientRings`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `spCoefficientTowersAbelian`, `SpCoefficientTowersAbelian`, and
  `sp_coefficient_towers_abelian`; the actual category is used in TowerCoefficients.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  read, publicly imported, and used through the normalized tensor-comparison interface.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: both
  `compactificationExchangeFromData` and `compactificationProjectionFromData` are
  called literally. No second exchange/projection data structure replaces this dependency.
- Proof imports: `Sheaf.CategoryTheory.DiagramSiteRealization`,
  `Sheaf.SixFunctors.OpenTensorNormalization`, `Sheaf.Paper.RingedExchangeTensorCoherence`,
  `Sheaf.Paper.ProjectionMateExact`. Their recorded signatures and proof docstrings
  were read. The full five-step proof is retained in the theorem docstring.

### Edge cases and searches

Checked: the zero finite coefficient ring is allowed (no Nontrivial hypothesis);
`r=1` is included and `r=0` excluded exactly as stated; the first tower level is
`n=0`, exponent `n+1=1`; all transition morphisms remain present, including
nonflat reductions. Zero objects, empty schemes and arbitrary unbounded complexes
are included. Identity base change and identity/open-only/proper-only factorizations
have the canonical unit and pullback comparisons. A nonflat base change imposes no
extra typeclass constraint. The inverse expression has the order C^{-1};P^{-1};B,
which follows from P;C=B;Q and has the required endpoints.

Searches performed with the prescribed wrapper:

- `msearch.py ... leanfinder "The compact support projection formula map for unbounded
  derived sheaves commutes with base change and inverses"`: 8 irrelevant hits on
  module presentations, pullback generators, sheafification and pushforward composition;
  no compact-support derived compatibility theorem.
- `msearch.py ... loogle '"rightAdjointProjectionMap"'`: 0 hits in the search service.
  The project's declaration with this name is available and is used by the recorded
  compactification projection constructor.
- `msearch.py ... grep 'projection.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*[Pp]rojection'
  CategoryTheory`: 0 Mathlib hits.
- `rg` with the same pattern and the item id in the upstream WeilConjectures and
  side `lean/Sheaf` trees found etale compact-projection theorems and unrelated
  geometric projection maps. The etale `projectionMapOfCompactification_baseChange'`
  and `projectionMap_rightDerivedLowerShriekBaseChangeMap` signatures were opened:
  their categories are `D(X_et,A)`, not the ordinary varying-coefficient tower category,
  so they cannot bind this node. No occurrence of this item's id was found.
- Source searches of the ordinary/strict-system operation interfaces identified
  `OpenTensorNormalization`, `ProjectionRestriction` and the supplied-domain
  compactification constructors used here. No preexisting declaration has the final
  two-setting statement.

There is no STATEMENT-DISPUTED flag and no node correction. Only the item's `lean`
record changes. All validation uses scompile.py; the final dry run additionally runs
server preflight and the prescribed per-file compilation.

## Second reading by Q110

A final in-thread reading checked the source node against the actual module, especially
both coefficient settings, the absence of restrictions on v, the four inverse hypotheses,
and each tensor/composition comparison. It found and repaired a reuse issue: the final
exchange/projection definitions now call the recorded supplied-domain constructors
literally. It also checked that rightSections compares underlying section functions: the
raw linear map on the fibre-product object has a different scalar ring before
restriction of scalars, so heterogeneous equality of entire linear maps would
incorrectly identify those scalar rings. The final equation erases that scalar
parameter while the rightSquare itself remains a linear natural isomorphism.
It also made presentation independence explicit: the main assertion applies
to every normalized presentation, and asserts their existence separately. This is a
worker self-check, not a claim of an independent second worker; the dispatcher brief
prohibits starting agents and assigns the independent review to the maintainer.

## Validation

The final scompile.py check compiled both the sandbox and library module with no
errors or warnings. The node signature matches the source verbatim; only the lean
record differs from the original node, and the module has exactly one sorry, in
the main theorem. Delivery preflight and compilation are run by deliver2.py.
