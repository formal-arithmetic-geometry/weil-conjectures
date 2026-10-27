## Worker report

This is a stage-2 statement delivery on top of Q104's accepted stage-1 split. The
inherited BLOCKED ending confused the stages: the live node has reviewed stage-1
proof steps but no Lean record. The maintenance handoff in brief-stage2 explicitly
confirms that this is the input to stage 2. The accepted statement, dependencies,
proof and stage-1 review are preserved. Only lean is added to the node copy.

The module Sheaf.Paper.TameInertiaScalarMate states
Profinite.TameInertiaScalarMate.scalar_mate_isomorphism. This is the only postponed
theorem. Its proof is exactly sorry, and its docstring gives all five proof steps.
All helper definitions have real data. No helper chooses an object from a mere
existence theorem: the main theorem concludes the existence of normalized models
and a universal derived scalar pair. These are fixed up to the unit-preserving
isomorphisms used in the conclusion. No new DAG nodes or dependency repairs are needed.

Hypothesis-by-hypothesis reading:

- Distinct primes p and ell: `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
  (_distinct : p ≠ ℓ)`.
- Omega is an algebraic closure of Q_ell with its extended norm topology:
  `(Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω]
  [IsAlgClosure ℚ_[ℓ] Ω]`. The normed algebra structure requires compatibility
  with the Q_ell norm. There is no completeness hypothesis on Omega.
- The finite intermediate extension is `(E : IntermediateField ℚ_[ℓ] Ω)
  [FiniteDimensional ℚ_[ℓ] E]`. Its actual inclusion is `algebraMap E Ω`, with
  `continuous_subtype_val`. The coefficient map is the dependency's
  `TameInertiaKoszul.coefficientMap`, which uses the recorded continuous-map ring map.
- The nonnegative rank is `(r : ℕ)`, with no positivity assumption.
- G is the dependency's `TameInertiaKoszul.Group p r`, namely the finite product
  of the products of the lifted PadicInt factors for primes q different from p.
  H is its `complement p ℓ r`, the subgroup with zero ell-coordinates; its
  generators are `generator p ℓ r i`. The lifts only implement the size convention.
- Every M is quantified by `Computes` as `M : Inputs E p ℓ r`. This is the
  existing full subcategory of representations satisfying `admissible`: finite
  E-dimension, joint continuity for the finite-dimensional module topology,
  finite actual H-image, and `Nat.Coprime (Nat.card image) ℓ`. Thus none of the
  representation hypotheses is replaced by a condition on an arbitrary complex.

Clause-by-clause reading:

- All continuous coefficient rings are the existing `ring F`, whose underlying
  sheaf is `continuousMapRingObjOfUniverse F`. The representation modules and
  extended actions are `d.modelE.action` and `d.modelΩ.action`, normalized by
  their `module`, `action_sections`, `map_sections`, and restriction fields.
  Their sections are precisely C(S,F tensor_E M), with the finite-dimensional
  module/product norm topology. No discrete or solid module category is used.
- `CondensedAction.Modules` is the recorded internal `CategoryTheory.Mod` category.
  `DerivedCategory` is the ordinary unbounded localization. The existing
  `TameInertiaKoszul.Context` is the normalized invariants functor with its
  total-right-derived universal property in the dependency's standard universe
  u+2. Its `derivedInvariants` applies it to the actual M_F in degree zero.
  It is the specialization already supplied by the recorded Koszul dependency,
  not another definition of invariants. The generic recorded derived-invariants
  module is also imported. No equality between site universes is imposed.
- The exact scalar restriction is exactly `coefficientRestriction E Ω h`, i.e.
  `Mod.comap` along the actual continuous internal ring map. Ordinary extension
  is the alias `tensor = Mod.extendScalars ...`, the existing balanced-coequalizer
  construction, not an arbitrary left functor. `DerivedTensor.functor`,
  `comparison`, and `universal` specify its total left derived pair. Its
  `adjunction` is to the exact restriction's `mapDerivedCategory`. Its `unit`
  equation uses the actual `Mod.extendRestrictAdjunction` unit on every homotopy
  complex, with the exact-functor factorization displayed. This is the transported
  unit-normalized coefficient adjunction of the recorded sheaf-ring theorem.
- The map u is the dependency's `representationCoefficient ... d.maps M`,
  constructed from the actual coefficient action map x to 1 tensor x and the
  normalized invariant/scalar-restriction comparison. `mate` is literally its
  image under `(s.adjunction.homEquiv _ _).symm`. There is no arbitrary arrow
  substituted for the unit or its adjunct.
- N=M^H is the dependency's `fixed`; `Result.average_range` identifies it with
  the range of `average`, whose sum is over the actual finite H-image. The
  generator operators are the existing `operator` on this fixed submodule.
- The two signed Koszul complexes are `d.modelE.koszul` and `d.modelΩ.koszul`.
  `Realization.coordinates` uses `Indices r a`, finite subsets of Fin r of
  integer cardinality a. `Realization.differential` is the stated deletion sum,
  with sign given by the cardinality of the smaller members of J. This also
  makes all degrees outside [0,r] empty without excluding any integer degree.
- The normalized derived isomorphisms are `d.comparisonE.kappa` and
  `d.comparisonΩ.kappa`, supplied by the same recorded `Result`. Their invariant
  inclusion and rank-zero normalizations and the actual coefficient square are
  retained as fields of d.
- The first conjunct of `Computes` is `IsIso (mate ... s M)`, in the actual
  derived category of internal C_Omega-modules, not just on cohomology.
- `tensorMap` is the actual ordinary chain-level scalar-adjunction adjunct of
  `d.maps.koszul.app M`, using `Mod.extendRestrictAdjunction.mapHomologicalComplex`.
  The next two conjuncts state that this chain map and the canonical derived
  tensor comparison on the Koszul complex are isomorphisms. This exposes the
  bounded flat/K-flat computation rather than assuming it as input.
- The following equality is T(kappa_E) followed by sigma equal to the canonical
  derived-tensor computation followed by Q(t) and kappa_Omega. The quotient/Qh
  and mapHomotopyCategory transports are all explicit and in the correct direction.
- The final conjunct quantifies every integer degree a, profinite test S, local
  scalar z, section x, subset I, and point t. `tensorGenerator` is z times the
  literal ordinary scalar unit at x, i.e. the class z tensor x in the existing
  balanced tensor. The output coordinate is
  `z.down t • extension E Ω (fixed ... M) ((dE.coordinates ... x I).down t)`.
  This says exactly z tensor (x_I) maps to (z x_I). At z=1 it retains the scalar
  unit, and for arbitrary z it gives the whole balanced tensor representative.
- The theorem concludes the existence of d and s; neither analytic Koszul
  comparison nor derived scalar context is an additional assumption on M.
  Quantification over M occurs inside the conclusion and covers every admissible M.

Dependencies used and inspected (module, declarations):

- Sheaf.Topology.ContinuousMapCondensedRing:
  Profinite.continuousMapRingSheafOfUniverse and its underlying ring-object construction.
- Sheaf.Topology.ContinuousMapCondensedRingMap:
  Profinite.continuousMapRingSheafMapOfUniverse and continuousMapRingObjMapOfUniverse.
- Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod, ModObj, Mod.Hom, Mod.comap.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions:
  CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions and its universal
  derived-functor convention; the specialization supplied by Koszul.Context is used.
- Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction:
  SheafOfModules.sheafRingDerivedCoefficientAdjunction, the unit/transpose normalization
  transported through the existing internal-module equivalence. This theorem is
  imported for the postponed proof, and its actual ordinary internal tensor is used.
- Sheaf.CategoryTheory.CondensedActionModule: Profinite.CondensedAction.Modules,
  sectionModule, ActionModule and Invariants.
- Sheaf.CategoryTheory.CondensedDerivedInvariants:
  CategoryTheory.CondensedDerivedRestriction.derived, scalarBase, scalarComparison,
  coefficientMap; their already recorded normalized ordinary-derived specification
  is instantiated by TameInertiaKoszul.Context and representationCoefficient.
- Sheaf.Paper.TameInertiaContinuousKoszul: all of Group, generator, complement,
  Inputs/admissible, fixed/average, ring, Realization, Context, ScalarRestriction,
  RestrictionUniversal, CoefficientMaps, representationCoefficient, Comparison,
  Result and continuous_koszul. These supply the actual objects and normalized maps;
  none is copied or replaced. The unused characteristic-p field in continuous_koszul
  can be F_p, so it is not an extra hypothesis of this node.
- WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars: Mod.extendScalars,
  extendUnit, extendRestrictAdjunction. I read their coequalizer construction,
  unit formula and Hom equivalence; the tensor already exists and is reused.
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction:
  CategoryTheory.Adjunction.mapHomologicalComplex and mapHomotopyCategory.
- For the proof plan the module imports the recorded CochainTensorUniverses,
  FlatOnSite and BoundedAboveFlatSheafKFlat modules. The existing
  InternalAbelianSheafModule.sectionModuleEquivalence is transitively imported.
  The proof follows the accepted finite-free argument through that equivalence.

Source reading: the node and all its statement dependency statements and recorded
signatures/docstrings were read. The current blueprint direct-image proof paragraph
(3) locates this extracted tame-boundary calculation, and the accepted stage-1 proof
supplies its finite-coordinate argument. No claim is made that the blueprint proves
the analytic Koszul input; this delivery uses that existing theorem as a dependency.

Edge cases checked before stating: r=0 gives the trivial product group and a single
empty-subset degree-zero term; the source unit is ordinary multiplication. N=0
allows the empty basis and zero sections in every degree. Degrees a<0 and a>r
have empty Indices. Empty test profinite S makes the pointwise formula vacuous,
without dropping the sheaf-level map or isomorphism assertion. A trivial action
at positive r has zero differentials, and a one-dimensional nontrivial commuting
action keeps the same scalar differential and signs. No Nonempty or positive-rank
binder excludes these cases. The primes remain distinct, including ell=2.

Searches made:

- msearch.py leanfinder, query "The canonical derived extension of scalars adjunct
  on condensed tame inertia invariants is an isomorphism computed by finite Koszul
  complexes": 8 hits, involving profiniteSolidCounit, locally constant condensed
  adjunctions and solidification. None concerns this all-continuous internal-ring
  derived-invariant comparison.
- msearch.py loogle, query "Mod.comap, Adjunction": 0 hits; it reports the indexed
  identifier Mod.comap unknown. Source inspection subsequently found and reused
  CategoryTheory.Mod.comap and the upstream concrete extension adjunction.
- msearch.py grep, query "Koszul.*(scalar|tensor)|(scalar|tensor).*Koszul": 0 hits.
- msearch.py leansearch, query "The extension of scalars adjunct on derived invariants
  of a continuous finite dimensional tame inertia representation is an isomorphism
  with Koszul multiplication representative": 8 hits. ModuleCat's ordinary scalar
  adjunction and Rep.invariantsAdjunction are general ingredients, not this theorem.
- rg over both lean/WeilConjectures and lean/Sheaf for
  "scalar_mate_isomorphism|TameInertiaScalarMate|tame.*inertia.*scalar|Koszul.*scalar"
  found generic Koszul scalar-base-change and other unrelated uses, not this statement.
  The upstream KoszulBaseChangeIso is for algebraic Koszul complexes, not the actual
  adjunct on condensed continuous-action derived invariants.
- grep for the exact node id under lean/WeilConjectures returned no match. Searches
  for tame inertia found the Frobenius/monodromy module, not this theorem. The existing
  TameInertiaContinuousKoszul supplies only the model and coefficient square and is
  used as a dependency, not registered as an existing match for the stronger scalar mate.

No statement dispute, correction or new source fault was found. The stale 06YS source
reference mentioned by the accepted stage-1 review is avoided: the proof docstring
uses 06YQ and the recorded bounded-above-flat module already cites 06YQ correctly.

Validation: scompile.py compiled the full module in sandbox and library modes with
no errors or warnings. All variables/universes are explicit (autoImplicit false).
Only the main theorem uses sorry. The required delivery dry run follows.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
