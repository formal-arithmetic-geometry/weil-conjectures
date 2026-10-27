## Worker report

The module `Sheaf.AlgebraicGeometry.TwistedCohomologyDevissageClosure` states
`AlgebraicGeometry.Scheme.Modules.twistedCohomology_devissage_closure` with its entire proof
postponed by `sorry`. Two real Prop definitions belonging to this same node spell out the
property introduced in the node itself:
`TwistedCohomologyVanishingBound L E b` and `HasEventualTwistedCohomologyVanishing L E`.
They introduce no independent mathematical notion or alternative tensor/cohomology construction.
No node statement, statement dependency, or proof dependency is changed.

The source read was `literature/stacks-project/coherent.tex`,
lemma-surjective-finite-morphism-ample (Tag 0B5V), lines 4548–4574, especially the definition
of P at 4563–4566 and the verification of conditions (1) and (2) at 4571–4574.
I also read lemma-property-higher-rank-cohomological (Tag 01YM), lines 3425–3458.
The locally Noetherian version of the closure assertions needs no properness, ampleness,
quasi-compactness, or finite-morphism hypothesis: those hypotheses in 0B5V belong to the later
ampleness argument and are not used in these formal closure properties. The item is a supporting
node, not the unit's statement; its accepted stage-1 split is preserved verbatim.

Hypothesis and clause correspondence:

- Scheme: `X : Scheme.{u}`; arbitrary universe `u` is explicitly declared.
- Locally Noetherian: `[IsLocallyNoetherian X]`, retained even though these closure arguments
  work without it.
- Invertible structure module: `L : X.Modules` and `[L.IsInvertible]`, using the existing
  locally-trivial rank-one definition. The coefficient category is exactly the category
  of structure-module sheaves on X; `X.Modules` is definitionally the `moduleRings` carrier
  accepted by the recorded cohomology and coherence declarations.
- Tensor and powers: ordinary monoidal `E ⊗ L.tensorPow n`; `Scheme.Modules.tensorPow` is the
  existing natural-number power, whose zero value is the structure module. No replacement
  powers or derived tensor are introduced.
- Cohomology: `RingedSpace.moduleCohomology X.toRingedSpace p`, the p-th right derived functor
  of module global sections, not the Ext cohomology of an underlying abelian sheaf.
- Coherent means `RingedSpace.IsCoherent X.toRingedSpace E`, including finite type and
  finite type of all the specified kernels. It is not merely the conjunction of
  quasi-coherence and finite type. The recorded dependency module publicly exposes this
  exact predicate, so no dependency repair is needed.
- P: `HasEventualTwistedCohomologyVanishing L E` is `∃ b : ℕ, ...Bound L E b`.
  Its bound predicate says `∀ n : ℕ, b ≤ n → ∀ p : ℕ, 1 ≤ p → Subsingleton ...`.
  Subsingleton of the underlying module means the cohomology group is zero. The bound is
  uniform over every positive p and is chosen before n and p. This formula is defined
  for all modules, and the conclusions involving coherent modules carry coherence explicitly.
- (1), every nonnegative n: the first quantified conjunction asserts invertibility of
  `L.tensorPow n`, additivity of `tensorRight (L.tensorPow n)`, and its preservation of
  finite limits and finite colimits, the exactness condition in this abelian category.
  Right tensoring sends E to exactly `E ⊗ L.tensorPow n`.
- (1), cohomology functors and long exact sequences: for every p, the stated composite
  functor is additive. There exists a `CohomologicalDeltaFunctor X.Modules ...` whose
  degree functors equal exactly those composites, including their morphisms. Its fields
  provide the connecting maps for every short exact sequence, the initial monomorphism,
  all three repeating exactness positions, and naturality. This expresses the complete
  long exact sequence, not only exactness at the middle H^p.
- (1), finite sums: `∀ r : ℕ, PreservesColimitsOfShape (Discrete (Fin r)) ...` for each
  n and p. Finite direct sums in an additive category are finite coproducts. This includes
  the empty sum and the actual functor maps, rather than arbitrary object isomorphisms.
- (2), zero: `HasEventualTwistedCohomologyVanishing L (0 : X.Modules)`.
- (2), extensions: `S : ShortComplex X.Modules`, `S.ShortExact`, and the three
  `RingedSpace.IsCoherent` hypotheses are exactly a short exact sequence of coherent
  modules. The two end-term vanishing hypotheses are expressed with their arbitrary
  witnesses `b₁ b₂`. The conclusion is `...Bound L S.X₂ (max b₁ b₂)`.
  This is the witness form of the implication between the existential P predicates and
  additionally specifies exactly the maximum of any given pair of witnesses, as required.
- (3), finite sums coherent: `∀ (r : ℕ) (E : Fin r → X.Modules), (∀ i, IsCoherent ... (E i))
  → IsCoherent ... (∐ E)`. There is no positivity requirement on r here.
- (3), retract: a coherent E, `r : ℕ`, `1 ≤ r`, and an arbitrary bound b witnessing
  `...Bound L (∐ fun _ : Fin r ↦ E) b` imply `...Bound L E b`. It is the same b,
  not a newly existentially chosen bound. The direct sum is explicitly r copies of E.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category of morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, the ordinary monoidal structures,
  and `tensorPow` (including its zero and successor clauses).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, `cochainModulesSymmetric`,
  `cochainModulesPreadditive`, and the existing tensor localization construction.
  This is the recorded tensor dependency; its data agrees with the scheme tensor.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`; its public import exposes
  `AlgebraicGeometry.RingedSpace.moduleCohomology` and the recorded delta-functor structure.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: publicly exposes
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`. The legacy
  `IsQuasiCoherentFiniteType` predicate is not used in place of coherence.
- `Mathlib.Algebra.Homology.ExactSequence`, with the public short-exact interface:
  `CategoryTheory.ShortComplex.ShortExact` (exact, mono first arrow, epi second arrow).
- Mathlib's sheaf-module limits and finite-coproduct preservation interfaces supply the
  categorical zero, actual finite sums, and `PreservesColimitsOfShape`.

The proof-only imports follow every recorded proof dependency:
`WeilConjectures.AlgebraicGeometry.Modules.Dual` (`IsInvertible.tensorObj`,
`nonempty_iso_dual_dual`),
`WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact`
(`finiteLocallyFree_tensorLeft_exact`),
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed` (`tensorClosed`),
`WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives`
(`moduleSheaves_abelian_enoughInjectives`),
`Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact`
(`globalSectionsFunctor_additive_leftExact`),
`WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`
(`Functor.exists_universal_rightDerived_deltaFunctor`), and
`WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum`
(`RingedSpace.coherent_kernel_cokernel_sum`). They remain ordinary, non-public imports.
The theorem docstring carries all six accepted proof steps, naming their inputs.

Edge cases checked before and after drafting:

- n = 0 uses the existing structure-module tensor unit and is included in exactness and
  all bound quantifiers; no assumption n > 0 was added.
- p = 0 is included in additivity and the long exact sequence, and excluded only from
  the positive-degree vanishing property by `1 ≤ p`.
- b = 0 is allowed; max b₁ b₂ works even when one or both bounds are zero.
- E = 0 is included; vanishing is Subsingleton, the correct notion for the underlying
  carrier of a module, rather than `IsZero` on a bare Type.
- r = 0 is included for coherence and preservation of sums. The retract implication
  requires r ≥ 1, because a zero-fold sum cannot detect an arbitrary summand's vanishing.
- r = 1 gives precisely a single copy, and the same b is retained.
- The empty scheme is allowed: there is no nonemptiness, point, or dimension hypothesis.
- No characteristic restriction or equality of independent universe variables is used;
  ordinary scheme modules use the recorded common universe u, not a restricted coefficient
  or test-object universe.

Searches actually run for an existing statement:

- LeanFinder through msearch: query “Eventual higher cohomology vanishing for invertible
  sheaf twists under extensions and finite sums”. Eight hits: `CategoryTheory.Sheaf.H`,
  `Sheaf.cohomologyPresheaf`, `Sheaf.instAddCommGroupH`, and five derived-category
  support/injective/projective results (`isGE_iff`, `isZero_of_isGE`,
  `to_singleFunctor_obj_eq_zero_of_injective`, `isGE_Q_obj_iff`,
  `from_singleFunctor_obj_eq_zero_of_projective`). None states the item.
- Loogle through msearch: `"Functor.Additive", "rightDerived"`: zero hits.
- LeanSearch through msearch: “Eventual higher cohomology vanishing after invertible
  twists is closed under short exact sequences and direct summands”. Eight hits:
  `ObjectProperty.IsClosedUnderExtensions.mk`, five group-cohomology long-exact-sequence
  results, `Abelian.Ext.covariantSequence_exact`, and the top object property's extension
  closure instance. These are generic extension or group/Ext results, not this statement.
- Mathlib grep through msearch: `eventual.*vanish|vanish.*twist|twist.*vanish`: only two
  unrelated hits, RegularizedHypergeometric.lean:178 and Asymptotics/Defs.lean:1505.
- Direct rg over both `lean/WeilConjectures` and `lean/Sheaf` for the same conceptual
  pattern found unrelated limit-stage vanishing, projective-space Serre vanishing,
  ideal-twist ampleness tests, and cohomology-localization results. Those assert other
  hypotheses and conclusions, not this conjunction of exactness and closure assertions.
- Searched the exact node id in the source library and in Sheaf: no declaration found.
- Searched `twistedCohomology`, `TwistedCohomology`, `twistVanishing`, `TwistVanishing`,
  and `cohomologyVanishing` in both roots; results concern other twist families or
  compact cohomology. Searched `dag/lean_names_upstream.json` for both new predicates
  and the theorem's proposed full-name components: no existing declaration.

No mathematical node fault or STATEMENT-DISPUTED issue was found. The first compile diagnosed
that categorical zero notation needs Mathlib's `ZeroObject` scope; the scope was opened,
without changing the statement. All binders and universes are explicit and autoImplicit is false.

Validation: scompile compiled both the sandbox check and the named library module cleanly
(7.1 s and 6.2 s in the successful run). The required deliver2 dry run passed server preflight
and compilation. A local packet comparison confirmed that only the node's `lean` field changed,
its recorded signature is verbatim from the module, there is exactly one `sorry`, and every Lean
line is at most 100 characters. The final delivery wrapper repeats compilation and preflight.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
