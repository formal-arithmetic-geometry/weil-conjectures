## Worker report

The module `Sheaf.CategoryTheory.OpenNormalActionInjectiveModels` states the node in
seven named theorems, all with `sorry`. No definition, dependency record, natural-language
statement, or proof plan was changed. The main declaration is
`Profinite.CondensedAction.openNormalActionInjectiveModels`, the resolution-normalization
equation for the existing canonical natural isomorphism `normalBeta`.

Hypotheses and clauses, matched to Lean:

- A commutative condensed ring on the coherent profinite site is `A : CondensedBar.Ring.{u}`.
  Its underlying ring object is `A.toMon : Profinite.CondensedRing`, with the existing
  `ringComm` instance. It ranges over arbitrary internal commutative rings, including rings
  with no topological-ring presentation. The site is `Profinite.{u}` and its coherent topology;
  internal module and action categories have objects in `u+2`, morphisms in `u+1`, and the
  existing `NormalComparisonCategories` chooses derived localizations in `u+2`.
- Internal action modules and fixedness are the recorded `ActionModule`, `Fixed`, and
  `FixedAll`: actions are by every continuous-map section after every profinite base change,
  not merely by points of the abstract group. `Modules A.toMon` is the recorded internal
  module-object category. No alternate action or invariants notion is introduced.
- The structural Grothendieck abelian hypotheses are `[C : NormalComparisonCategories]`.
  `[V : NormalInvariantFamily]` supplies normalized full-invariant adjunctions and additive
  exact forgetting, arbitrary continuous group restrictions, and trivial inflation.
  The imported `CondensedDerivedRestrictionCalculus` publicly supplies its structural
  `CondensedDerivedInvariants` interfaces: `forgetExact`, `restrictionAdditive`,
  `restrictionLimits`, `restrictionColimits`, `trivialAdditive`, `trivialLimits`,
  `trivialColimits`, and `scalarExact`. These are the node's stated structural background;
  no K-injective preservation or quotient-invariant existence is assumed by the family.
  Scalar restriction uses the same underlying sheaf and its kernels/cokernels; no flatness
  hypothesis is introduced. The scalar clauses play no additional role in this kernel lemma.
- Profinite G and L are `G L : ProfiniteGrp.{u}`; open normal K is
  `K : OpenNormalSubgroup G`. `normalKernel`, `normalQuotient`, `normalProduct`,
  `normalProjection`, and `normalKernelInclusion` are the dependency's actual subgroups,
  quotients, product, quotient projection and map k ↦ (k,1).
- Finite discrete Q and a continuous set section are exactly
  `openNormalQuotientSection`: `Finite`, `DiscreteTopology`, and a continuous map `s`
  with `Function.RightInverse s QuotientGroup.mk`.
- `openNormalQuotientExists` concludes `Nonempty (NormalQuotient A G L K)`.
  This existing specification includes an additive quotient-invariant functor T, its
  injective natural inclusion, image exactly `Fixed`, residual action compatible with
  every lift, both normalized transposes, and K-injective preservation. Its `image`
  and `residual` fields encode the internal submodule and independence of lifts.
  This theorem does not choose an undetermined object as a definition.
- `openNormalComparisonExists` concludes `Nonempty (NormalDerivedComparison A G L K)`
  for any such T. Its `kernel` and `ordinary` natural isomorphisms render the ordinary
  identities UT = Γ_K r and Γ_(G×L) = Γ_(Q×L) T; `kernel_inclusion` and
  `ordinary_inclusion` normalize them by the same invariant inclusions. The normalized
  left-inflation identity is also retained by the dependency specification. The use of
  isomorphisms transports between invariant-submodule realizations and does not replace
  these inclusion-normalized identifications by arbitrary comparisons.
- `openNormalKernelPreserves` concludes the existing `NormalKernelPreserves` certificate,
  so r preserves K-injectives. `openNormalFullInvariantsPreserves` concludes preservation
  by every Γ_P. T's preservation is part of the quotient datum whose existence is proved.
  The kernel-preservation theorem is an instance so `normalBeta` can be stated without
  adding preservation as an assumption to its normalization theorem.
- `openNormalActionResolution` quantifies over every integer-indexed complex N and concludes
  existence of a complex I, chain map i, `I.IsKInjective`, and `QuasiIso i`. No boundedness
  or termwise-injective assumption is made.
- The existing `normalBeta A G L K d` has type
  `T.functor.rightDerivedFunctor ⋙ U.mapDerivedCategory ≅
  r.mapDerivedCategory ⋙ Γ_K.rightDerivedFunctor`; thus it is a natural derived
  isomorphism on the entire unbounded categories. The main theorem quantifies over
  arbitrary N,I and any `i : N ⟶ I` with `[I.IsKInjective] [QuasiIso i]`.
  Its left side is beta_N followed by the canonical resolution computation of
  RΓ_K D(r)(QN). Its right side is the canonical resolution computation of
  D(U) RT(QN) followed by the localized chain isomorphism induced by `d.kernel.hom`.
  The two `mapHomologicalComplexCompIso` factors only reassociate the two degreewise
  functors; `d.kernel.hom` is the invariant-inclusion identification of the identical
  fixed-section complex. The equation says beta is its identity under these
  identifications, including differentials. It is asserted for EVERY resolution i;
  hence its normalization is independent of a resolution. Naturality for arbitrary
  derived morphisms is supplied by the natural isomorphism, not just chain maps.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `Modules`, `sectionModule`,
  `inflate`, `trivial`, `forgetAction`, `Fixed`, `FixedAll`, `Invariants` in
  `Profinite.CondensedAction`.
- `Sheaf.CategoryTheory.CondensedNormalInvariantData`: `NormalComparisonCategories`,
  `NormalInvariantFamily`, `NormalQuotient`, `NormalDerivedComparison`,
  `NormalKernelPreserves`, `normalBeta`, and the normal group/map constructions.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded universal
  unbounded right-derived functor and resolution-computation interface. On the structural
  Grothendieck categories the existing `Functor.rightDerivedFunctor` and
  `Functor.rightDerivedFunctorObjQIso` from the imported upstream KInjective module are
  the canonical computation used by `normalBeta`; no second derived functor is defined.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: its recorded coefficient
  square and structural exactness background, publicly imported as a statement dependency.
- Proof imports: `Sheaf.CategoryTheory.CondensedSplitCosetInduction`, declaration
  `Profinite.CondensedAction.SplitCosetInduction.exists_datum`;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, declaration
  `CategoryTheory.Adjunction.preservesKInjectiveComplexes`;
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`, declaration
  `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`;
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`, declaration
  `CochainComplex.IsKInjective.Qh_map_bijective`.
- `def-weil-size-convention` is a convention record without a declaration; explicit
  universe u and the dependency's site/module/localization universes implement it.

Edge cases checked before writing: K=G, finite G with K=1, trivial G or L, infinite L
(so K×1 need not be open or finite-index), zero ring, zero modules and complexes,
and complexes unbounded in both directions. None requires averaging, division by
|Q|, finite L, discrete modules, or a flat ring map. The section is a set section,
not a homomorphism; no splitting of the group extension is asserted.

Searches: `msearch.py leanfinder` queried “Condensed internal module actions open normal
subgroup quotient invariants preserve K-injective unbounded derived comparison”. Eight
hits concerned ordinary condensed-module categories (IsSolid, LightCondensed Grothendieck,
AB4/AB5, CondensedMod and related equivalences); none states this normalized action theorem.
`msearch.py loogle` queried `"IsKInjective", "invariants"`, with zero hits.
`msearch.py grep` queried `KInjective|quotientToInvariants|normalBeta` in Mathlib/Condensed,
with zero hits. `rg` in WeilConjectures and Sheaf for normalBeta, NormalKernelPreserves,
NormalBetaUnit and open-normal patterns found the usable definition interfaces and the
larger downstream normal-subgroup comparison, but no theorem with this node's statement.
Searching this item's blueprint id in WeilConjectures gave no declaration. Existing
upstream abstract K-injective preservation and Hom-localization theorems are reused.
The searches' exact wrapper results are recorded in sandbox searches.jsonl.

Source read: main-20261015 direct-images proof paragraph (3). As the node explicitly says,
this detailed condensed-action lemma is agent-formulated categorical input, not an
explicit assertion in that blueprint paragraph. Each theorem docstring includes its
corresponding proof steps from the accepted eight-step split and the relevant dependency
ids. No statement fault or STATEMENT-DISPUTED issue was found.

Validation: the server scompile wrapper compiled the full module cleanly (sandbox and
library checks); only theorem proofs are postponed. The final delivery dry run also
checks the packet and compiles the delivered file.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
