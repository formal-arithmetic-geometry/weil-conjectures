## Worker report

The module `Sheaf.Paper.SystemRefinementConstructibleDomain` states the complete node
in the namespace `AlgebraicGeometry.ProEtale.SystemRefinement`. All twelve theorems
have `sorry` proofs. Definitions have actual data. The node's mathematical statement,
proof, and proof dependencies are unchanged. No new nodes or dependency replacements
are delivered. Two already landed nodes are added to statement dependencies: the
canonical positive coefficient tower and the exact constant-scalar tensor encoding.
Their dependency closures were checked not to reach this item.

### Hypotheses and objects

* `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` render the prime and finite coefficient extension.
  `F : FiniteFieldDatum` supplies the specified finite field and algebraic closure;
  `hl : l ≠ F.p` is the distinct-characteristic hypothesis. The geometric theorems
  explicitly include these section variables even where they occur only in hypotheses.
* `rings` and `transitions` are aliases of the published `scalarRings` and
  `scalarTransitions`, not another tower. Index `n : ℕ` means exponent `n+1`, so
  every and only positive finite level is covered. These use the recorded valuation
  ring, uniformizer, quotient, and quotient homomorphism. The coefficient lift is
  `ULift.{u+1}`; `finiteRings` reuses `finite_coefficientExtensionRing`.
* Schemes are `Scheme.{u}`. Their actual small pro-etale categories have object
  universe `u+1` and morphism universe `u`, and coefficients and modules have universe
  `u+1`. `VaryingRing.Derived` is the ordinary unbounded derived category of module
  sheaves on the coefficient sequence site. It is not an inverse sequence of separate
  derived categories. `B` and `tau` alias its actual constant coefficient sheaves and
  actual quotient transitions. No site universes have been equated.
* `X.Over (Spec (.of F.k))`, `Y.Over ...`, and `f.IsOver ...` are the k-scheme
  structures and the k-morphism. Each structure morphism has `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`; `f` has those three properties too.
  This renders exactly separated finite-type schemes and separated finite-type f.
* `c₁ c₂ : Compactification f` contain the opens and proper maps with their
  factorization equations. `r : c₁.Refinement c₂` contains `r.hom`, `r.i_hom`
  and `r.hom_g`, namely u, uj1=j2 and p2u=p1. Properness is the existing refinement
  instance. `compactificationOpenQuasiCompact` is the published consequence of
  quasi-compact f, not an additional hypothesis on the opens.
* `VaryingRing.G`, `.P`, `.J`, `.adj`, `.pId`, and `.pComp` supply actual simultaneous
  inverse image, derived direct image, exact open extension, adjunction and canonical
  identity/composition comparisons. Our `gamma` uses the published actual
  `VaryingRing.gamma` for `(j1,1,u,j2)` with the necessary identity-edge comparison.
  Its underlying arrow is exactly that node's open base change followed by clopen
  projection, identity on the chosen component and zero on its complement.
* `compositor` is equality transport along `r.hom_g` followed by the inverse of
  `VaryingRing.pComp`; it has orientation Rp1 to Rp2 Ru. This is the canonical
  adjoint-conjugate direct-image compositor, not an arbitrary isomorphism.

### Each assertion

* `domain X K` is literally `∀ n, intrinsicFiniteTorsionConstructible ... (ev n K)`.
  Thus boundedness and constructibility hold independently at each positive level.
  No common bound, normalization, or Tor hypothesis occurs here. The fixed-scalar
  presentation `level` is evaluation followed by the recorded exact scalar restriction.
* `gamma_isIso` asserts `IsIso (gamma r K)` for every K in that domain.
* `level_origin` separately asserts, for each `n`, an L in the etale bounded-below
  category, `Etale.DerivedCategory.isBoundedConstructible ... L.obj`, and an
  isomorphism from comparison pullback of L to `level n K`. Bounded constructibility
  is the D^b_c condition; using its canonical D-plus inclusion does not weaken it.
  There is no sequence of L's, compatibility condition, or choice of their transitions.
* `gamma_evaluation` is an equality of the evaluated actual map, transported by
  `evalP` and `evalJ`, with `VaryingRing.constantGamma` at this same coefficient ring.
  It retains the identity-edge factor explicitly and works on every K.
* `gamma_witness_evaluation` states the forward-mate normalization for every bounded
  constructible L and every isomorphism alpha, in the fixed-scalar encoding. Its
  right side is j2! alpha inverse, `properOpenProEtaleIso` at L, then Ru* j1! alpha.
  This is exactly clause (a) of the recorded refinement definition, with witness
  transport, rather than just existence of some finite isomorphism.
* `theta` is the compositor followed by Rp2 of the inverse of the actual `gamma`.
  It obtains the `IsIso` instance from `gamma_isIso`, not a separate chosen inverse.
  `theta_evaluation` states equality of its evaluated isomorphism with the existing
  `properTransportRefinement`, conjugated by alpha through the two compact-support
  candidates. `imageLevel` contains the canonical open and direct-image comparisons.
  L and alpha are arbitrary binders, and hL is its bounded-constructibility hypothesis.
  `properTransportRefinement` is the ambient-derived version of the same recorded
  definition's part (b), including its D-plus compatibility isomorphisms.
* `normalized` is an alias of `SemilinearSections.Normalized`, applied to the actual
  system and its actual reductions. `reduction` aliases `SemilinearSections.reduction`;
  its maps are the scalar-adjunction transposes of the actual horizontal transitions.
  `Calculus` is the existing representative-normalized `SemilinearSections.Data`.
  `A : ∀ W, Calculus W` supplies a model of this specified calculus, including its
  ordinary tensor, K-flat representative, evaluation, scalar adjunction and pure
  tensor normalization fields. It is not a free tensor functor or a proposition.
* `ctf W M` is literally levelwise the recorded `finiteTorConstructible` predicate.
  `tor` aliases the recorded `HasProEtaleTorAmplitude`. In particular the ordered
  intervals and tests on every module sheaf in degree zero are retained.
* `normalized_operations` has exactly the assumed normalized M,N and their ctf
  levels. Its first four conjuncts assert normalization of `G f N` and
  `A.closed.tensor (M,G f N)`, followed by their levelwise ctf conditions.
* Its fifth conjunct quantifies over n and a,b,c,d and preserves the pullback
  interval [c,d] while giving tensor interval [a+c,b+d]. Thus the bounds may depend
  on n; the theorem does not demand a common interval.
* Its sixth conjunct is the actual pullback reduction formula under `evalG`:
  scalar extension of evaluation, the inverse `scalarPull`, and pullback of N's
  actual reduction. The seventh is the tensor reduction formula under
  `tensorEvaluation`: scalar extension of that evaluation, `scalarTensor`, then
  the two actual reductions under the recorded level tensor functor.
* The assertions for M follow from hcM, and for the tensor from the ctf conclusion:
  their domain conditions allow the preceding inverse, origin, and evaluation
  theorems to be specialized to each. No assertion normalizes Rp j! M, and no
  hypothesis or argument detects equality of arbitrary system maps by evaluation.

### Canonical encoding helpers

The interfaces use two existing presentations: modules over the sheafified constant
commutative ring and fixed-ring module-valued sheaves. `ordinaryDirect_existsUnique`
fixes the comparison by identity on every section. `ordinaryPull_existsUnique` and
`ordinaryOpen_existsUnique` uniquely specify the inverse/open comparisons through
explicit unit equations. Their definitions choose the unique witness, not a map
from mere unconstrained existence. `fixedDirect` and `fixedOpen` derive those
ordinary comparisons by the published total-derived/exact localization comparisons.
`pushLevel`, `openLevel` and `imageLevel` compose these with the actual evaluations.

`restrictionDirect_existsUnique` fixes the quotient restriction/direct-image square
by its identity after forgetting to abelian sheaves. This is equality of the whole
underlying natural transformation (HEq allows the two scalar presentations), and
pins every component on every section. `restrictionPull_existsUnique` fixes its
left-adjoint mate by its displayed unit transpose. `scalarPull_existsUnique` then
fixes extension of scalars versus inverse image by its scalar-adjunction transpose.
Each uniqueness theorem has a complete proof description, and each data definition
refers only to that uniquely determined witness. These helpers state the canonical
scalar comparisons already required by this node; they introduce no independent
mathematical notion or additional hypothesis.

### Dependency declarations inspected and used

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its coefficient import:
  `Padic.finite_coefficientExtensionRing`, `.coefficientExtensionRing`,
  `.coefficientExtensionTransition`.
* `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`:
  `WeilConjectures.IntegralSystemRealization.scalarRings`, `.scalarTransitions`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `.ProEt.topology`;
  upstream `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory`
  supplies the coefficient/site size convention. The scheme-properties collection
  node introduces no independent notion: its Mathlib separatedness, finite-type
  and quasi-compactness classes are the explicit binders here.
* `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, its properness instance and equations.
* `Sheaf.Paper.SemilinearDerivedSections` and its recorded model/calculus imports:
  `WeilConjectures.SemilinearSections.Data`, `.coefficientMap`, `.res`, `.reduction`,
  `.Normalized`; their actual evaluation, scalar-adjunction, tensor and model fields.
* `Sheaf.Paper.NormalizedDVRTower`: normalization uses all actual transition-adjoints.
  Its separate coherent integral-tower encoding is not substituted for the strict
  semilinear derived category specified here; `.Normalized` is precisely the
  normalization definition supplied by this node's semilinear-sections dependency.
* `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`; through the existing exact
  encoding equivalence this is the intrinsic predicate. The signatures directly
  use `Scheme.intrinsicFiniteTorsionConstructible` and `finiteTorConstructible` from
  the recorded `Sheaf.Paper.FiniteTorAmplitudeSites` imports, so no new finiteness
  condition replaces the dependency predicates.
* `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting`: `.VaryingRing.gamma`,
  `.gamma_evaluation`, `.P`, `.G`, `.J`, `.ev`, `.evalP`, `.evalG`, `.evalJ`,
  `.pId`, `.pComp`, and `.constantGamma`.
* `Sheaf.Paper.RefinementComparisonIsomorphism`:
  `AlgebraicGeometry.ProEtale.properTransportRefinement`, `.properTransportRefinementPlus`,
  `.refinementProperOpenIso`, `.refinementComparisonAtWitness`; the first is used
  verbatim in theta_evaluation, with its canonical bounded-below/ambient transport.
* `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`:
  `CategoryTheory.ConstantScalarRestriction.restriction`, `.onDerived`, `.exact`,
  `.additive`, `.isEquivalence`; restriction is fixed by constant scalar sections.
* Proof imports include `ProEtaleConstructibleOrigin.constructible_proEtale_origin`,
  `SystemNormalizedTensorClosure.normalized_tensor_closure` and
  `.normalized_inverseImage_closure`, the recorded `sf_pullback_torAmplitude`,
  `finiteCoefficient_tensor_ctf`, the strict-tower `gamma_evaluation` and
  `normalizedProperOpenCalculus`, `properOpenInterchangeCoherence`,
  `properOpenComparison_site_normalization`, and
  `ringedToposDerivedPushforwardComposition`. The latter's small-category signature
  is not used to force pro-etale universes equal: the already published geometric
  pComp is the needed canonical conjugate construction. No repair is necessary.
* `lem-pur-system-proper-open-invertibility` is still unstated in the read DAG.
  It is a proof dependency only, not an object needed for this signature; no module
  for it is imported. Its refinement specialization is directly stated here as
  gamma_isIso; stage 3 can use its module when published. All other stated proof
  dependencies have imports (the Noetherian consequence uses Mathlib.Noetherian).

### Edge cases

Checked n=0 in the implementation means exponent 1, so the zero exponent is never
introduced; every n>=1 in the node is covered. Identity refinement and m=n retain
canonical identity/composition comparisons. Empty schemes and zero complexes are
allowed by the recorded constructibility definitions (an empty scheme can use a
positive empty stratum); there is no nonempty scheme or nonzero complex hypothesis.
Compactification refinements are not required Cartesian or surjective; extraneous
proper components are precisely the complement killed by the clopen projection.
Nonflat quotient transitions are permitted throughout. Normalization is not used
for arbitrary K, and only actual reduction maps are inverted. Integer intervals
remain ordered through the existing Tor predicate; different levels can have
arbitrarily different bounds. No uniform etale-origin witnesses, common finite
stratification across levels, or normalization after proper pushforward is imposed.

### Search and source checks

The sandbox searches.jsonl contains the original wrapper results. LeanFinder query
"Strict semilinear derived systems compactification refinement mate invertibility
constructible finite coefficient levels tensor Tor amplitude" returned unrelated
Profinite.NobelingProof, generic derived-category factorization and local-cohomology
lemmas; no exact statement. Loogle `CategoryTheory.IsIso, SheafOfModules` returned
generic sheafification/scalar-restriction isomorphism facts, no refinement-domain
assertion. Loogle `CategoryTheory.IsIso, DerivedCategory` returned the generic
cohomology criterion and fraction/factorization lemmas, no match. msearch grep
`semilinear.*refinement|refinement.*constructible` in CategoryTheory returned zero.
LeanSearch "Proper compactification refinement mate invertible for semilinear
coefficient systems with bounded constructible levels" returned unrelated analytic
semilinear-map results. Direct rg of both project roots for refinement/constructible,
SystemRefinement, and scalar comparison names found the existing generic varying-ring,
strict-tower and canonical coefficient bridges; these are reused rather than restated.
Direct search for this node id in WeilConjectures returned no declaration. The initial
unqualified Loogle query `IsIso, DerivedCategory` was unusable; the qualified query
above was run successfully. No exact existing statement was found.

Read Stacks more-etale.tex at lemma-shriek-proper-and-open (0F7B) and
lemma-shriek-composition (0F7J), the blueprint main-20261015 tensor-ctf and
pullback-tor-amplitude statements, and the full item proof. The source requires
actual comparisons and arbitrary witness transport; those are explicit equations
here. The original sandbox draft had a slow sectionwise restrictionDirect formula;
replacing that formula by the same identity as an underlying abelian natural
transformation resolved its kernel unfolding cost. Also corrected its nonexistent
compactification.left projection to the recorded compactification.Z.

### Validation

All compiles used the prescribed scompile.py wrapper against the published live
library, with the fixed per-file limit and no global build. The final full module
compiles both as sandbox and under its actual library module name, with no warnings.
The final pass after using the recorded intrinsic/ctf predicates took 11.3 seconds
and 10.4 seconds respectively. Every theorem remains sorry. No statement dispute
or source correction was found. The prescribed dry run and delivery follow.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
