## Worker report

The module `Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting` states the exact
factorized-endomorphism pasting equation and, separately, both K-flat representative
component formulas. All nine declarations are recorded in `lean.declarations`. The
seven helper definitions have real data; the two theorem proofs are `sorry`. Their
docstrings carry the six proof steps of the node. The node statement is unchanged.
No new node, dependency repair, or statement correction is needed.

Hypothesis and clause correspondence:

- Schemes and arbitrary scheme morphism: `{X Y : Scheme.{u}} (u : X ⟶ Y)`.
- Finite commutative coefficient ring: `(A : Type u) [CommRing A] [Finite A]` in
  both theorems. The helper constructions use the published arbitrary-ring API.
- The small sites are the recorded `Scheme.ProEt` and `ProEt.topology`.
  `proEtaleRingModules T (proEtaleConstantRing T A)` and
  `proEtaleDerivedCategory T A` are the published categories, using constant sheaves
  of `ULift.{u+1} A`; no replacement module or derived category is introduced.
  Site objects remain in `Type (u+1)`, morphisms in `Type u`, coefficient/module
  sections in `Type (u+1)`. No site universe equality is imposed.
- Canonical coefficient identifications: `proEtaleConstantRingDerivedPullback A f`
  uses `proEtaleConstantRingComparison f A`, the isomorphism of the actual
  constant-section inverse-image map. The compositor is precisely
  `proEtaleConstantRingPullbackComposition h k A`, whose inverse is the node's
  `c_{h,k}`. Its definition transports the general normalized compositor along
  `proEtaleConstantRingCompositeCoefficients_eq`, rather than choosing another iso.
- Endomorphisms: `(rX sX : X ⟶ X) (rY sY : Y ⟶ Y)`.
- The first two commuting squares: `er : u ≫ rY = rX ≫ u` and
  `es : u ≫ sY = sX ≫ u`. These are the node's equalities in Lean composition order.
- `t_T = s_T ∘ r_T` is written directly as `rX ≫ sX` and `rY ≫ sY`; the outer
  equality is the explicit proof argument `et`. This is the equality already
  implied by er and es, not an additional geometric condition: associativity,
  er, and es give u rY sY = rX u sY = rX sX u. Keeping its proof explicit covers
  every equality transport specified by the node; proof irrelevance makes the
  result independent of the proof chosen.
- `C_v` is `proEtalePastingDerivedSquare`. It is the compositor hom, followed by
  `eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e)`, followed by the
  other compositor inverse. Thus both the direction and transport are explicit.
- `P_u d_Y`, `C_r P_sY`, and `P_rX C_s`, in that order, are the three substantive
  factors of `proEtalePastingDerivedLeft`; the intervening associators only change
  parentheses. `proEtalePastingDerivedRight` is C_t followed by d_X P_u.
  The common target is P_u ⋙ (P_sX ⋙ P_rX), i.e. P_rX P_sX P_u in the node.
- The primary theorem compares `.hom` directly, so is an equality of natural
  transformations on all D_Y, not just a componentwise assertion on resolutions.
- For every unbounded complex K, the second theorem uses the exact recorded
  `IsKFlatIndependentCoefficients` predicate and the exact recorded
  `IsFlatOnSite` on each `K.X n`, for all `n : ℤ`.
- Its two conjuncts identify the left and right derived components at Q(K) with
  `Functor.mapDerivedCategorySquareIso` applied to their respective ordinary
  paths, then the canonical comparison expanding the triple target. By the
  definition in `MapDerivedCategoryMate`, this is the localization of the
  termwise ordinary map, conjugated by the canonical localization/composition
  factorization isomorphisms. Hence it is exactly the class of the corresponding
  termwise pasting map, with no assumption or new choice of representative maps.
- `proEtalePastingOrdinaryComposition` names the inverse of the ordinary
  comparison in the published `proEtaleConstantRingPullbackComposition_ordinary`.
  Its unit-section formula determines this object: adjunction sends a pullback
  map to its composite with the unit, whose section restrictions are fixed.
  Thus the defining choice is from a characterizing property, not a bare
  Nonempty or an undetermined existence theorem. Ordinary squares and both
  paths use the same explicit equality transports and associators as the derived ones.
- No Cartesian square, smoothness, finite type, flatness of scheme arrows,
  invertibility, boundedness or nonempty-scheme hypotheses occur.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingPullback`, `proEtaleConstantRingDerivedPullback`,
  `proEtaleConstantRingComparison`, and `proEtaleConstantRingAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `ProEtale.finiteCoefficientInverseImageMap_isIso` and its constant and empty
  normalization clauses. Imported for the exact canonical coefficient convention.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`:
  `Scheme.proEtaleCoefficientInverseImageMap_comp` (also the recorded declaration
  of lem-trf-constant-coefficient-composition).
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition`, the recorded reexport
  of the full arbitrary-ring-sheaf normalized compositor. It publicly imports
  `proEtaleCanonicalPullbackComposition`; no integral or p-adic specialization
  is used or assumed by this module.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`:
  `Scheme.proEtaleConstantRingPullbackComposition` and
  `proEtaleConstantRingCompositeCoefficients_eq`. Its landed owner
  pur713-def-pullback-comparison is added to stmt_deps, as for the coherence node.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence`:
  `Scheme.proEtaleConstantRingDerivedPullback_composition_coherence` for the proof
  plan and `proEtaleConstantRingPullbackComposition_ordinary` for the canonical
  ordinary representative interface. Its landed owner is added to stmt_deps.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.KFlatRingedToposPullback`:
  `SheafOfModules.isKFlat_ringedToposPullback` (proof-only import).
- `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`:
  `Functor.mapDerivedCategorySquareIso`, the canonical localization of a termwise
  square isomorphism; `Functor.mapDerivedCategoryCompIso` is the existing target
  reassociation into individual derived pullbacks.
- `Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit` supplies its public
  `ProEtale.continuousCohomology_locallyBijective` instance. This existing explicit
  coefficient-size instance avoids unresolved auxiliary max-universe constraints
  from a more general imported instance. It changes no sites, coefficients or
  mathematical hypotheses. Similarly `essentiallySmallSelf.{0} Y.ProEt` is supplied
  explicitly to K-flatness. No local/private instance is introduced.

Edge cases checked: empty X, empty Y (then every source admitting a map to it is
empty), zero coefficient ring, identity endomorphisms and identity u, equal factors,
and arbitrary unbounded K (including the zero complex). The constant-ring theorem
explicitly includes empty sources, and the construction contains no cancellation of
coefficient sections or nontriviality assumption. All equality proofs, including an
arbitrarily supplied proof et of the outer square, are transported by congrArg/eqToIso.
The target types of both paths are checked by Lean, including their associators.

Searches for existing declarations (2026-10-21):

- `msearch.py leanfinder`: "Canonical derived pro etale pullback comparisons respect
  pasting two commuting endomorphism squares with constant finite coefficients".
  Eight results, principally scheme fibre-product maps and ordinary O_X-module
  `Modules.pseudofunctor_associativity`; none states derived constant pro-etale pasting.
- `msearch.py leansearch`: "Canonical derived pullback of pro etale sheaves pasting
  commuting endomorphism squares". Eight results, ordinary categorical pullback
  pasting and `SheafOfModules.conjugateEquiv_pullbackComp_inv`; no exact match.
- `msearch.py loogle`: "SheafOfModules.pullback_assoc,
  AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity"; zero hits for the
  combined query. The individual ordinary pullback declarations were read in source.
- `msearch.py grep`: "pullback_assoc|pullbackComp" in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf`; five hits in PullbackContinuous.lean.
  Read `pullbackComp` and `pullback_assoc`: these compare ordinary site module
  pullbacks and do not state the required normalized derived pro-etale assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for derived pullback pasting,
  factorized pullbacks, and square comparisons found the existing normalized
  compositor and coherence module, plus unrelated tower/Cartesian pasting statements.
  Searching the item id in `lean/WeilConjectures` found no declaration.
- `rg` for every new declaration prefix in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing declaration.

Source read directly: literature/stacks-project/sites-cohomology.tex,
lemma-derived-pullback-composition, including the K-flat-with-flat-terms proof;
all six source/proof steps in the DAG node. No statement dispute found.

## Second reading by Q46

A separate second pass by this worker compared the node and completed file; the
maintainer's independent delivery review remains independent of this pass (the
worker brief forbids spawning agents). Checked the coefficient/compositor direction,
all three square transports, the factor order r then s, each whiskering and functor
associator, and both representative conjuncts. The left path starts with d_Y, then
C_r, then C_s; the right path starts with C_t then d_X. Both have exactly the same
source and target. The representative formulas use actual localization of the
canonical ordinary paths, not arbitrary isomorphisms. The imported ordinary
normalization fixes the only selected helper object. No mathematical mismatch was
found. Elaboration fixes made during the first pass were qualified Functor whiskering
names, explicit functor arguments to the square-localization API, explicit K-flat
universe/site arguments, and reuse of the existing fixed-coefficient locally-bijective
instance. These do not change the node statement or impose a universe equality.

Validation: scompile.py is used for every compile, with the required default limit.
The final compile and delivery preflight results are recorded by the delivery wrapper.
