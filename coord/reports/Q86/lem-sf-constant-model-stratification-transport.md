## Worker report

The module `Sheaf.Paper.ConstantModelStratificationTransport` states every clause of
lem-sf-constant-model-stratification-transport. The natural-language node is unchanged;
only its lean record is supplied. All seven theorem proofs are `sorry`; the two
stratification adapters have concrete record data and no postponed proofs.

Clause-by-clause correspondence:

- The scheme T is `Scheme.{u}`. The arbitrary commutative condensed ring is
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. This is the unbundled object encoding of the recorded
  `Profinite.CondensedRing`; no topological presentation or coefficient-field
  hypothesis is imposed. The coefficient ring is the existing `condensedRingObj Λ T`,
  and modules are `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ...`.
- `Scheme.Stratification.toFiniteLocallyClosed` forgets only constructibility proofs.
  `Scheme.FiniteLocallyClosedStratification.withConstructibleStrata` adds just those
  proofs. Both literally reuse n, stratum, domain and immersion, and all locally
  closed, partition, immersion and range proofs. There is no choice of a reduced
  structure. `constructibleStratification_iff_locallyClosed` quantifies over every
  `P : ∀ S : Scheme.{u}, (S ⟶ T) → Prop`; its equivalence expresses the two existential
  witness presentations, and its other two clauses assert inverse repacking.
- `finiteConstantModelsOnCover_of_iso` takes the isomorphism `e : M ≅ N`, a fixed
  pro-etale cover `𝒰`, a fixed family of ordinary scalar modules
  `P : 𝒰.I₀ → Mod Ab (scalarRingObj Λ)`, their finite-presentation proofs hP, and the
  original model isomorphisms hM. Its conclusion uses exactly those same 𝒰 and P;
  the only changed object is N in the pulled-back module. Models use the dependency's
  actual `finiteConstantScalarExtension`, including the canonical scalar map.
- `finiteConstantPointModelsOnCover_of_iso` records the same fixed-witness assertion
  in the condensed-presentation encoding used in `HasFiniteConstantLocalModel` itself.
  It retains the given point modules and their finite presentations. This complements,
  rather than replaces, the preceding explicit ordinary-scalar formulation.
- `stratifiedConstantModels_of_iso` fixes `S : Scheme.Stratification T`, each stratum's
  cover `𝒰 a` and every scalar module `P a i` before transport. The conclusion contains
  the identical S, 𝒰 and P and the iterated restriction to cover members of the strata.
  Thus constructibility of strata remains part of the same S and no new immersion
  or replacement cover is allowed.
- `affineStratifiedConstantModels_of_iso` also fixes any `U : T.Opens` with
  `hU : IsAffineOpen U`. It first restricts along U.ι, then along each immersion of
  `S : Scheme.Stratification U.toScheme`, then along the specified cover. Its result
  retains all of these and the same scalar modules. It quantifies over arbitrary U,
  so covers every affine open separately, including on a non-qcqs scheme.
- `constantModelConstructible_transport` uses precisely the existing
  `IsConstantModelConstructible`: the qcqs branch uses a finite stratification;
  otherwise the condition is imposed on all affine opens. This states the existential
  constructibility consequence for the defining witness encoding.
- `constantModelCohomology_transport` takes the ambient unbounded `DerivedCategory`,
  a family M indexed by all integers, the isomorphisms
  `e q : M q ≅ (DerivedCategory.homologyFunctor _ q).obj L`, and constructibility of
  every M q. Its first conclusion is constructibility of every H^q(L). Its second
  quantifies over the SAME integers r and s supplied with the hypothesis
  `∀ q, q < r ∨ s < q → IsZero (M q)`. It concludes the existing
  `constantModelBoundedConstructible Λ T L` and explicit cohomology vanishing outside
  precisely [r,s]. The preceding fixed-witness transport statements apply to every
  e q. No tensor product or Tor-amplitude assertion is made.

Dependency declarations inspected and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, identified with
  `Mon (Sheaf (coherentTopology Profinite) Ab)`; its underlying ring-object encoding
  is used directly as in the other dependencies.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `upperStarFromPoint`, `condensedRingObj` and its commutativity instance.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its action encoding.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar`, the existing ringed pullback.
- `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel`,
  `IsFiniteConstantStratified`, `IsConstantModelConstructible` and
  `constantModelBoundedConstructible`; all definitions were read in full.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: `scalarRingObj`,
  `finiteConstantScalarExtension`, `HasFiniteConstantLocalModelOnCover` and
  `finiteConstantLocalModel_iff_exists_cover`; the explicit model uses this exact API.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Topology.FiniteLocallyClosedStratification` and
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `WeilConjectures.ConstructibleSheaf.Defs`: `Scheme.Stratification`, including its
  constructibility fields. The topological parent was inspected in
  `WeilConjectures.Topology.Stratification`.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`, the dependency's
  mathlib_match; no locally-closed-implies-constructible assertion is used.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  derived-conventions module, imported for the ambient derived-category dependency.
  The conclusion uses `DerivedCategory` and `DerivedCategory.homologyFunctor`,
  not the weaker arbitrary-lfp constructibility convention of that ambient node.

Edge cases checked before finalization: empty T and n = 0 (all indexed assertions
are vacuous with the original partition data retained); zero scalar modules and zero
model objects; identity isomorphisms; empty cover indices when they actually form a
cover; arbitrary non-reduced stratum realizations (never replaced); non-Noetherian
locally closed subsets (constructibility is explicit, never inferred); non-qcqs T
(separate witnesses on every affine open); r = s and r > s (the latter forces every
M q and hence every H^q to be zero, without imposing r ≤ s). The site object and
morphism universes follow the existing u/u+1 framework; no additional size equality
or nonemptiness assumption is introduced.

Searches actually run:

- msearch.py leanfinder: "Transport finite constant scalar models and constructible
  stratification witnesses along module isomorphisms retaining strata covers and
  scalar modules". Eight hits, including Module.Finite.of_equiv_equiv and
  LinearEquiv.cast: no match to the stratification and sheaf-witness statement.
- msearch.py loogle: `"Stratification", "Sheaf"`. No hits.
- msearch.py grep: `HasFiniteConstantLocalModel|IsConstantModelConstructible|FiniteLocallyClosedStratification`.
  No Mathlib hits.
- rg over lean/WeilConjectures and lean/Sheaf for those same identifiers and for
  constant-model/stratification transport names found the dependencies above and
  applications. Grep of the item id in lean/WeilConjectures found no declaration.
- A focused source search found private `constantModelConstructible_of_iso` in
  `Sheaf.Paper.ProperHeartConstructibleCohomology`; it proves only the existential
  constructibility consequence, is private, and supplies neither the stratification
  conversion nor the fixed-cover/scalar-module conclusions. It is not a complete
  existing match. `StratifiedLattice` contains a local one-way record unpacking for
  another lemma; it supplies no public inverse conversion or the present statement.
- The full new declaration names were checked in lean/Sheaf, lean/WeilConjectures
  and dag/lean_names_upstream.json before recording; no clashes were found.

Validation: scompile.py compiled the sandbox and the library-path module successfully
(41.1 s and 5.7 s respectively), with no errors or unexpected warnings. The adapters
are actual definitions; every postponed theorem has this node's blueprint annotation
and its relevant complete natural-language proof in its docstring. No new node,
dependency interface repair, statement correction or disputed statement is needed.

## Second reading by Q86

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
