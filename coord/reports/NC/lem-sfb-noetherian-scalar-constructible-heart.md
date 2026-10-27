## Worker report

The single module `Sheaf.Paper.NoetherianScalarConstructibleHeart` states
`AlgebraicGeometry.ProEtale.noetherian_scalar_constructible_heart` with one `sorry`.
It defines no new notion and proves nothing. The live item's accepted stage-1 split,
statement, dependencies and proof are unchanged; only its `lean` field is supplied.
The prior BLOCKED ending concerned stage 1. The stage-2 handoff in
`coord/brief-stage2.md` §0 and the current queue (stage 2, state) authorize this work.
There was no preserved mathematical work in the sandbox, only dispatch marker files.

### Hypotheses and objects, clause by clause

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The coefficient is `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`
  with `[MonObj Λ] [IsCommMonObj Λ]`: a commutative condensed ring.
- `hΛ` has exactly six alternatives, in the node's order. The first quantifies a
  commutative finite discrete topological ring `A`, requires `Finite A` and
  `∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0`, and identifies its actual condensed ring
  `Profinite.continuousMapRingObj A` with `Λ` by a ring-object isomorphism
  `Nonempty (Mon.mk Λ ≅ Mon.mk ...)`. Finite rings have representatives in `Type 0`;
  the isomorphism permits any isomorphic presentation in the specified coefficient
  universe. `Nonempty` expresses existence of an isomorphism, not arbitrary
  chosen coefficient data or an assumed comparison functor.
- The second is `Profinite.continuousMapRingObj ℤ_[ℓ]`.
- The third is `∃ E : PadicAlgCl.FiniteIntermediateField ℓ, ...
  Profinite.padicIntegersRingObj ℓ E`, with its norm topology inherited from the
  fixed algebraic closure. The existing finite-intermediate-field subtype records
  finite dimension over `ℚ_[ℓ]` and containment in `PadicAlgCl ℓ`.
- The fourth is `Profinite.continuousMapRingObj ℚ_[ℓ]`.
- The fifth quantifies the same existing finite-intermediate-field type and uses
  `Profinite.continuousMapRingObj E`.
- The sixth uses `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`, so sections are
  ALL continuous maps into the norm-topological algebraic closure. It does not
  use `Profinite.padicAlgClRingObj`, which restricts to finite-subextension-valued
  sections. The recorded `IsLocalizingAdmissibleCoefficient` currently has an
  extra disjunct for that distinct ring. Using it as this theorem's hypothesis
  would assert an additional case. Accordingly `hΛ` writes the node's six cases
  directly, using the same already-defined coefficient ring objects and ring
  isomorphisms; it introduces no replacement coefficient predicate or definition.
  Quantifying the possible `E` in its two alternatives is equivalent to the
  node's convention of first fixing an arbitrary finite `E` and choosing a case.
- The scheme is `(X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]`.
  These are exactly the two cited Noetherian conditions, with no separatedness,
  dimension, characteristic, nonemptiness or invertibility assumption added.
- The ambient category is exactly
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`,
  implicit in the recorded constructibility predicate. This is ordinary internal
  modules over the point-pullback coefficient, not a completed/adically derived
  category. The scheme/site universe is `u`, sheaves take values in `Ab.{u+1}`,
  and the small indexing universe in the conclusion is exactly `u+1`.
- The subcategory is the existing `ConstantModelConstructible Λ X`, the FULL
  subcategory for `IsConstantModelConstructible Λ X`. Its recorded definition
  uses finite scalar presentations chosen on the condensed point, before pullback
  to pro-etale covers of constructible locally closed strata; on qcqs schemes it
  uses a finite stratification. No arbitrary local-matrix substitute is used.

### Conclusions, clause by clause

- Essential smallness is `EssentiallySmall.{u + 1}
  (ConstantModelConstructible Λ X)`, an equivalence with a category small in the
  specified indexing universe, not the vacuous self-size bound.
- Repleteness is `ObjectProperty.IsClosedUnderIsomorphisms
  (IsConstantModelConstructible Λ X)`.
- Contains zero is `ObjectProperty.ContainsZero (...)`; its Mathlib definition
  supplies an ambient zero object satisfying the predicate. Repleteness then
  includes every ambient zero object.
- Kernel and cokernel closure are respectively
  `ObjectProperty.IsClosedUnderKernels (...)` and
  `ObjectProperty.IsClosedUnderCokernels (...)`. Mathlib quantifies all ambient
  kernel/cokernel objects of every morphism between objects with the predicate.
- EVERY ambient extension is expressed by
  `ObjectProperty.IsClosedUnderExtensions (...)`, whose `prop_X₂_of_shortExact`
  quantifies an arbitrary ambient short complex and short-exactness proof, and
  deduces membership of its middle object from membership of both endpoints.
  There is no restriction to sequences already inside the full subcategory.
- Abelianness is `Nonempty (Abelian (ConstantModelConstructible Λ X))`.
- Exact inclusion is `PreservesFiniteLimits (ObjectProperty.ι (...))` and
  `PreservesFiniteColimits (ObjectProperty.ι (...))`, the standard equivalent
  exactness formulation for this full abelian inclusion, including preservation
  of ambient kernels and cokernels. No arbitrary inclusion functor is supplied.
- Integral torsion scalar models are included because the existing predicate
  requires finite presentation, not finite free/projective modules or finite
  Tor amplitude. The theorem has no Tor-amplitude hypothesis.

### Recorded dependencies and proof imports

Statement dependencies were read with their complete recorded signatures and
module docstrings:

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`; its expanded
  coefficient list explains why the exact six alternatives are written in `hΛ`.
  Its imported existing continuous-map and padic coefficient constructions are used.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (every affine open has Noetherian ring).
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt`, with `Scheme.ProEt.topology`.
- `def-weil-size-convention`: metatheoretic convention; explicit `universe u`,
  `Scheme.{u}`, `Profinite.{u}`, `Ab.{u+1}` and `EssentiallySmall.{u+1}` implement it.
- `sk-def-sfb-module-derived-pushpull`:
  `Sheaf.Paper.CondensedModuleDerivedPushpull`, the recorded ordinary
  `CondensedRing.moduleObjectDerivedPushforward` and
  `CondensedRing.moduleObjectDerivedPullback` are publicly imported, together
  with their underlying ordinary module category and point-pullback coefficient.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `IsConstantModelConstructible`, `HasFiniteConstantLocalModel`,
  `IsFiniteConstantStratified`, `ConstantModelConstructible`, all in
  `AlgebraicGeometry.ProEtale`.

Every proof dependency with a recorded module is imported, except the size
convention which has no module. Plain proof imports are:
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
(`CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`),
`Sheaf.CategoryTheory.RingedSiteModules` (`CategoryTheory.ringedSiteModules`),
`Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`
(`AlgebraicGeometry.ProEtale.finiteConstantLocalModel_iff_exists_cover`),
`Sheaf.AlgebraicGeometry.ConstructibleModuleObjectsEssentiallySmall`
(`AlgebraicGeometry.ProEtale.constructibleModuleObjects_essentiallySmall`),
`WeilConjectures.ConstructibleSheaf.Refinement` (`Scheme.Stratification.inter`),
`Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
(`CondensedRing.module_pullback_additive_exact`),
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr` (`Padic.extension_integers_dvr`),
`Sheaf.Paper.TAdmissibleDualizableTruncations`
(`CondensedRing.tAdmissible_dualizable_truncations`),
`Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels`
(`AlgebraicGeometry.ProEtale.condensed_dualizable_iff_local_perfect`),
`Sheaf.CategoryTheory.DerivedCategory.DegreeZeroAbelianCriterion`
(`DerivedCategory.degreeZero_abelian_criterion`),
`Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`
(`FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence`),
`Sheaf.Paper.FiniteCoefficientModelComparison`
(`FiniteDiscreteOrdinary.finiteCoefficientModelComparison`),
`Sheaf.Paper.ProEtaleFixedModuleConstructible`
(`Scheme.IsConstructibleProEtaleFixedModuleSheaf`), and
`Sheaf.Paper.ProEtaleConstructibleExactClosure`
(`Scheme.constructibleProEtale_exactClosure`).
The statement imports already include the Noetherian topological consequences,
p-adic number constructors, the ordinary pullback and the Mathlib abelian full
subcategory criterion. The sole proof node
`lem-sfb-semihereditary-topological-coefficients-admissible` has no recorded Lean
module yet, so there is no module to import for it. It is retained verbatim in the
DAG/proof docstring for stage 3; it is not a missing notion needed to type this statement.

### Sources and edge cases

Read the local HRS PDF, Theorem 6.2(2)-(3) (heart = finite scalar models),
Lemma 6.10 and Corollary 6.11(1) (topological semihereditary coefficient rings),
and the current blueprint unit's refinement/coherence route. HRS's regular
coherence argument is only used for the five topological cases. The finite
possibly nonregular discrete case follows the separate 09B5/03RZ route recorded
in the accepted node proof, including its finite-model comparison.

Checked before writing: the empty scheme has the same zero/full-subcategory
formulation and is not excluded; zero finite coefficients satisfy the first
alternative; `n=0` in the annihilation condition permits exactly the zero ring;
rank-zero presentations give zero; modules such as `Z/ell^2` are permitted by
finite presentation and use the finite-discrete proof branch; integral torsion
models require no finite Tor amplitude; all characteristics and all dimensions
remain available; the algebraic closure case is not restricted to finite
subextensions and does not acquire a completeness hypothesis. No statement
correction or disputed statement is needed.

### Searches and validation

All prescribed search wrappers used group NC and the exact item id:

- `msearch.py ... leanfinder`: “Finite scalar model constructible sheaves over
  continuous l adic rings on a Noetherian scheme form an essentially small abelian
  subcategory closed under kernels cokernels and all ambient extensions”. Eight
  generic condensed/sheaf Grothendieck/abelian results, no exact match.
- `msearch.py ... leansearch`: “Constructible finite scalar model sheaves with
  continuous l adic coefficients on Noetherian schemes form an essentially small
  abelian category closed under extensions”. Eight generic sheaf-abelian,
  Grothendieck and Ext results, no finite scalar-model theorem.
- `msearch.py ... loogle`: `"constructible", CategoryTheory.Sheaf`, zero hits.
- `msearch.py ... grep`:
  `IsConstantModelConstructible|constructible.*[Ss]erre|constructible.*[Kk]ernel`,
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: constructible-heart,
  scalar-heart, `IsConstantModelConstructible`, and the exact item id. Upstream
  `essentiallySmall_isConstructibleModuleObject_of_noetherianSpace` concerns the
  broader arbitrary local-finite-presentation predicate, not this theorem.
  `coefficientHeart_essentiallySmall` and `coefficientHeart_closure` cover only
  particular field cases (including a different algebraic-closure ring), while
  `isConstantModelConstructible_serre_padicIntegers` covers integral closure only.
  None states all clauses of this node for its six coefficient cases, so an
  `existing: true` record is not appropriate. The exact item id had no upstream hit.
- The full module compiled through `scompile.py` both as a sandbox file and at
  its intended library module path. Both checks succeeded with no errors or
  unexpected warnings (9.8 s and 9.1 s respectively). The first compile's only
  issue was using dot notation on a predicate typed as a function rather than
  `ObjectProperty`; explicit `ObjectProperty` predicate names fixed it.

## Second reading by NC

Worker rereading of the completed signature against the node, not an independent
agent review. The dispatch expressly forbids starting another agent; independent
review belongs to the maintainer. Rechecked each of the six disjuncts, the norm
versus discrete convention, all-continuous algebraic-closure sections, both
Noetherian assumptions, the ordinary internal module category, finite constant
scalar-model subcategory, indexing universe, and every conclusion above. The
extra finite-subextension coefficient in the recorded broad predicate is avoided
by the six explicit alternatives; no dependency definition was replaced. Ambient
extension closure was checked directly against the Mathlib class definition.
No further mismatch or statement correction was found. Only the theorem proof is
`sorry`; there is no data definition, auxiliary axiom, private notation, local
instance, hidden `let` binder, additional hypothesis, new node or dependency repair.
