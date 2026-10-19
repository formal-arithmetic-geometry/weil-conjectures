## Worker report

The delivery states `AlgebraicGeometry.Scheme.integral_cohomological_adic_criterion`,
with `sorry` and the five-step natural-language proof of the DAG node. It also supplies the new definition node `def-sfb-completed-constant-stratified`; the returned
dependency record for `sk-def-sfb-constructible` is restored unchanged.
The `integralCriterionWEquals` instance is exactly Mathlib's existing
`WEqualsLocallyBijective.ofEssentiallySmall` at the site's standard coefficient size.
It resolves a maximum-universe ambiguity in an imported generic instance; it introduces
no hypothesis, transport of K, additional axiom, or postponed proof.
No statement correction, extra hypothesis, or mathematical proof is added.

Hypotheses and ambient objects, clause by clause:

- A prime ell is `(l : ℕ) [Fact l.Prime]`.
- A finite extension E/Q_l is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Its integers, uniformizer, and ideal are the existing
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`, and
  `ProEtale.IntegralConstantCompletion.ideal l E`. The latter is literally the ideal
  spanned by `ULift.up` of the uniformizer in `IntegralConstantCompletion.integers`.
  The lift changes only the coefficient universe; it does not restrict E.
- `(X : Scheme.{u}) [IsNoetherian X]` means a finite affine cover by Noetherian rings.
  Mathlib's `isNoetherian_iff_of_finite_affine_openCover` confirms this interpretation.
- `adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E)` is the actual limit
  of constant quotient ring sheaves at exponents n+1. Quotienting the lifted scalar ring
  is canonically identical to lifting each R/pi^(n+1). Thus this is precisely B, including
  its projection to k_X at index 0. The recorded integral-limit theorem identifies this
  with O_{E,X}; no independent or arbitrary coefficient ring/map is assumed.
- `DerivedCategory (proEtaleRingModules X B)` is the ordinary unbounded localization of
  sheaves of modules over B on the original small pro-etale site. Site objects have
  universe u+1 and arrows universe u; these are not equated.

Condition (1):

- `DerivedCategory.TStructure.t.bounded K` is the existing ordinary bounded-cohomology
  condition, as used by `constantModelBoundedConstructible` and `boundedConstructible`.
  No completeness is hidden in this condition.
- `∀ q : ℤ, IsCompletedConstantStratified X I ((DerivedCategory.homologyFunctor _ q).obj K)`
  imposes the specified constructibility on every cohomology module.
- The new completed-constant definition uses `s : FiniteLocallyClosedStratification X` to give
  the finite locally closed partition, immersion maps, covering, and disjointness.
  `∀ a, Topology.IsConstructible (s.stratum a)` is explicitly the constructibility of
  each stratum. The cover `V` is a covering sieve of the final pro-etale object on each
  stratum, so its slice isomorphisms express precisely pro-etale local isomorphisms.
- `∃ P : ModuleCat A, Module.FinitePresentation A P` gives the exact scalar models in
  the statement. `completedAdicChange X (CompletedConstantReduction.base X I)` applied
  to `(adicLisseConstantModules X A).obj P` is ordinary B tensor_R P, not a derived or
  completed tensor substitute. The same genuine immersion inverse-image functor is
  applied to M and its model before `SheafOfModules.overFunctor` restricts to U. For
  immersions the canonical limit comparison identifies the inverse-image B with B on
  the stratum, as in the recorded immersion limit-preservation statement. These are
  isomorphisms of modules over that ring, not just underlying additive sheaves.

Condition (2) is the existing `IsSfbAdicConstructible X I K`, read in full:

- Its first conjunct is `IsSfbAdicComplete X I K`. This uses the recorded
  `IsLocallyDerivedRingedIdealComplete` via `ConstantCompletion.IsComplete`, after the
  actual section-preserving AsSmall transport to an equivalent small site. Its ideal
  is the kernel of the actual first quotient projection, equal to pi B by the recorded
  constant-coefficient result. It imposes local derived completeness without a bound.
- Its second conjunct quantifies over an actual etale residue-module cochain complex C.
  Passing to `DerivedCategory.Q.obj C` realizes exactly the existential derived object
  in the node; every object has such a representative. The condition on C.homology is
  boundedness, not a bound on the chosen representative's terms.
- `∀ q, IsConstructibleSheaf (C.homology q)` is the existing global etale constructibility
  predicate: finite constructible locally closed strata with locally constant finitely
  generated residue modules. Since A/I is k, finite generation is finite dimensionality.
- `Nonempty (Q.obj (sfbResidueComplex X I K) ≅ Q.obj (...comparisonUpperStar... C))`
  supplies exactly the required coefficient-linear derived isomorphism. Its orientation
  is immaterial because an isomorphism has an inverse. The residue complex is obtained
  by the existing `completedAdicDerivedChange` along `limit.π ... (op 0)` followed by
  fixed-scalar restriction. Thus its tensor is relative to B and retains the k action.
- The final existential integers a,b with a <= b test every etale degree-zero k-module
  sheaf N and every q outside [a,b]. `sfbEtaleTensorDegreeZero` computes the relative
  derived tensor: over a field, all module sheaves on the etale site are flat, as seen
  by exact conservative geometric stalks. It therefore agrees with the node's finite
  Tor-amplitude clause even for unbounded representatives. No test module is omitted.
- The outer iff gives both directions of the equivalence.

Dependency declarations read and used (directly or through the public imports):

- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`:
  `ProEtale.sfb_integral_coefficient_limit`, finite quotient tower, `sfbCondensedIntegers`.
- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`:
  `IntegralConstantCompletion.integers`, `.ideal`, `.integral_constant_completion`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `ProEtale.IsConstantModelConstructible`, `IsFiniteConstantStratified`,
  `HasFiniteConstantLocalModel`, `constantModelBoundedConstructible`; all retained.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` and its public
  `ProEtaleBoundedConstructible` import: the ordinary bounded-cohomology convention.
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`:
  `CategoryTheory.IsLocallyDerivedRingedIdealComplete`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and `CoefficientExtension`:
  the finite l-adic extension, integer ring, chosen uniformizer, and quotient definitions.
- Mathlib: `AlgebraicGeometry.Scheme`, `IsNoetherianRing`, `Scheme.ProEt`,
  `Scheme.smallEtaleTopology`, `Module.FinitePresentation`, and `DerivedCategory`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` (no implicit constructibility restriction).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  the recorded relative-tensor/internal-Hom convention, publicly importing its Tensor.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, `.proEtaleSiteComparisonModules`;
  the actual inverse-image functor is `ProEtale.comparisonUpperStar`.
- `Sheaf.Paper.AdicStratifiedPerfect`: `IsSfbAdicConstructible`, `IsSfbAdicComplete`,
  `sfbResidueComplex`, `sfbEtaleTensorDegreeZero`, `adic_stratified_perfect`.
  The predicate declarations are used by the right-hand side; the theorem remains only in
  `proof_deps`, as required by the returned repair.
- `Sheaf.Paper.CompletedConstantSheafReduction`: `CompletedConstantReduction.base`;
  `Sheaf.Paper.AdicLisseModule`: constant-module and completed-ring constructions;
  `completedAdicChange` is the published ordinary scalar extension.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`: `proEtaleRingModules`;
  `ProEtaleInverseImage`: `proEtaleModuleInverseImage`.
- Proof imports retain the DVR, truncation triangle, general ringed derived restriction,
  finite torsion-free PID freeness, and Noetherian finite-presentation lemmas. The other
  available proof modules are already imported by AdicStratifiedPerfect or
  IntegralConstantCompletion. No downstream theorem about this criterion is imported.

Edge cases checked before writing: empty X permits zero strata and all module categories
are trivial; K=0 is included; concentrated-in-one-degree complexes and arbitrary shifts
are allowed; P=0, P=R/pi^m, and P=R^r are all permitted finite-presentation witnesses;
there is no torsion-free or projective hypothesis on P. No finite dimension of X,
separatedness beyond Noetherian qcqs, ell-invertibility, or lower/upper bound on arbitrary K
is assumed. The same isomorphism uses the residue action, so it does not merely compare
underlying abelian complexes. Source read: PDF Definition 6.8.10 and Proposition 6.8.11(3),
and the current blueprint sk-prop-integral-criterion/_section.md. No statement fault found.

Searches:

- msearch.py LeanFinder: "Bounded constructible integral pro etale complexes are derived
  complete with bounded constructible residue reduction". Eight hits: BDeRham/BDeRhamPlus
  and etale-site facts; no matching constructibility/completeness equivalence.
- msearch.py Loogle: `"Constructible", "Complete"`: zero hits.
- msearch.py grep: `constructible.*complete|complete.*constructible` in CategoryTheory:
  zero hits.
- msearch.py LeanSearch: "A bounded constructible integral pro etale complex is derived
  complete with constructible residue reduction". Eight hits: IsAdicComplete constructors,
  p-adic integer completeness, bounded derived representatives and HasExt; no match.
- rg of `integral_cohomological_adic|cohomological_adic_criterion` and the blueprint id
  in the source WeilConjectures tree and shared lean/Sheaf: no existing theorem. Wider
  integral/constructible and constant-model searches found IntegralModelsStacks (a consumer
  whose proof explicitly cites this item), AdicStratifiedPerfect (the general supporting
  criterion), and CondensedConstantConstructibility (internal modules only).
- Read current server source using `scompile.py --source` for
  InternalAbelianSheafModuleEquivalence and InternalSectionTensorComparison. These change
  presentation but do not give a directly usable B-ring-sheaf constructibility predicate.
  The chosen repair therefore uses genuine ordinary module pullback and extension rather
  than introducing a second internal-module equivalence or an arbitrary comparison.

## New nodes

`def-sfb-adic-stratified-perfect-data` is the existing-definition interface node for the
unchanged declarations in `Sheaf.Paper.AdicStratifiedPerfect` used by the item's right-hand
side. It records `sfbFixedScalarRestriction`, `sfbEtaleTensorDegreeZero`,
`sfbResidueComplex`, `sfbModelRings`, `IsSfbAdicComplete`, and
`IsSfbAdicConstructible`; the theorem `adic_stratified_perfect` remains only in
`proof_deps`.

`def-sfb-completed-constant-stratified` is the new definition node for the completed-ring-sheaf
finite-stratification predicate. It records the actual inverse-image coefficient ring on each
stratum and slice, the covering sieve, constructibility of every stratum, and an ordinary
finite-presentation witness `P` with scalar extension `B tensor_A P`. Its source is Bhatt--
Scholze Definition 6.8.10 and Proposition 6.8.11(3). Searches used LeanFinder, Loogle,
Mathlib grep, the slopmaster2 source tree, and the shared `lean/Sheaf` tree; no exact existing
predicate was found. The original `sk-def-sfb-constructible` record and module are retained
unchanged, and the new definition imports and uses that general finite-constant-local-model
interface.

## Second reading by N4

Repair self-check on 2026-10-18: R1 is addressed by the new
`def-sfb-adic-stratified-perfect-data`, whose `existing: true` record lists exactly the six
plain definitions in the unchanged published module. Read their signatures and bodies:
the residue projection has exponent `0+1`, scalar restriction retains the module action,
completeness uses the actual kernel ideal, and the final predicate quantifies over every
degree-zero residue module. The item cites this definition node; the supporting theorem
occurs only in `proof_deps`. R2 is addressed by
`def-sfb-completed-constant-stratified`, citing all four requested definition nodes and
owning the existing sandbox definition. Compared the restored `sk-def-sfb-constructible`
JSON with the current shared base: the entire record is identical, including N7's seven
declarations. The item's only changed fields against that base are `lean` and `stmt_deps`;
the latter only adds the two new definition nodes. Both module signatures and the existing
predicate signature are verbatim in their records. No Lean source change was required.

Author self-check, as required for direct dispatcher delivery; independent review is by the
maintainer. Reopened the item node, the new definition node, and both Lean files and traced both conjuncts and the iff. The
finite-stratification definition explicitly checks constructibility of strata and finite
presentation of P, and compares modules over the same actual inverse-image ring. The right
side is the already published complete + etale-origin + Tor-amplitude predicate, with the
first quotient indexed by 0+1. Neither representative choices nor ULift remove any complexes
or scalar actions. In particular the left side has no completeness baked into its definition.
The source's finite projective resolution of a torsion module is used only in the proof plan,
not as a projectivity requirement on its local cohomology models. No mismatch found and no
mathematical statement changed. The helper has real definition data, and the only postponed
proof newly written is the item's named theorem with the complete node proof in its docstring.

## Validation

Both delivered modules compile cleanly through the prescribed scompile.py wrapper,
individually and in dependency order against the side-project overlay. No extra hypotheses
were introduced to resolve universes: the sole elaboration aid specializes the existing
Mathlib small-site locally-bijective theorem to coefficient universe u+1. Site objects stay
in u+1 and site morphisms in u. Scratch probes were removed before delivery.

Preflight metadata repair: lean.declarations lists declarations actually defined in each
new file. The original condensed constructibility declarations are still public imports;
none is redefined. The canonical site instance is exported with priority 3000 to make its
fixed universe available to consumers as well as to this theorem. The supporting theorem node lem-sfb-adic-stratified-perfect remains in proof_deps because its
mathematical equivalence and closure facts are used only by the postponed proof; the item
stmt_deps instead cite the new definition node for the predicate declarations.
