## Worker report

The module `Sheaf.CategoryTheory.ProfiniteInvariantsSheafifiedCohomology` states
`Profinite.CondensedAction.SheafifiedCohomology.profiniteInvariants_sheafifiedCohomology`.
Only its proof is postponed. All helper constructions contain real data and reuse the
recorded sites, internal modules, invariants, scalar forgetting, object cohomology,
sheafification, injective resolutions and ordinary total right derived functor.

Hypothesis and clause correspondence:

* Arbitrary commutative condensed coefficient ring: `A : CategoryTheory.CondensedBar.Ring.{u}`,
  the existing `CommMon` bundle on coherent profinite abelian sheaves. Its underlying
  `A.toMon : Profinite.CondensedRing` is the coefficient input of the recorded presentation;
  no topological presentation of A is required.
* Compact Hausdorff totally disconnected topological group: `J : Type u` with `Group`,
  `TopologicalSpace`, `IsTopologicalGroup`, `CompactSpace`, `T2Space` and
  `TotallyDisconnectedSpace`. Universes and small-site models are the recorded ones:
  profinite spaces in u, site models and abelian groups in u+1, categories in u+2.
* Internal modules with the continuous generalized-element action: the existing
  `CategoryTheory.CondensedBar.Equivariant A J`, transparently the recorded
  `Profinite.CondensedAction.ActionModule A.toMon J`.
* Fully invariant sections after every profinite base change: the existing
  `(CategoryTheory.CondensedDerivedRestriction.invariants A J).functor`, with its actual
  inclusion. Its definition uses the recorded `FixedAll` predicate. No ordinary
  pointwise fixed-point substitute is introduced.
* Ordinary derived invariants and their nonnegative cohomology: the expression
  `DerivedCategory.singleFunctor ... 0 ⋙ derived A J ⋙ DerivedCategory.homologyFunctor ... q`.
  This is written explicitly, rather than using the parent's `higherInvariants` helper,
  avoiding any dependency on the downstream filtered-continuity module.
* The normalized action-site equivalence: parameters `P : SetPresentation J` and
  `D : ModulePresentation J P A.toMon`. These quantify over the normalized presentations
  already specified by the dependency, not an arbitrary equivalence or additional
  existence hypothesis. `D.data.ring` is the recorded R_J and
  `D.data.equivalence` is Phi. `presentationAdditive` reads `D.properties.additive`.
* The trivial-action parameter functor is `parameters J := AsSmall.up ⋙ trivialParameter J`.
  It uses all the original profinite parameters, without imposing exactness of evaluation.
* `objectPresheaf D q` is Phi followed by `SheafOfModules.toSheaf`, the exact recorded
  `Sheaf.cohomologyPresheafFunctor`, and precomposition by the opposite trivial-parameter
  functor. Thus its objects, coefficient maps and restrictions are precisely P_M^q and
  P_f^q in the node, including their Ext-based object-cohomology realization.
* Every nonnegative resolution: all `Q : InjectiveResolution M` are quantified. Its
  standard `Q.cochainComplex` and `Q.ι'` extend the natural-degree resolution by zero.
  `invariantPresheafComplex Q` is U Gamma(Q) before sheafification. Its homology is the
  presheaf S ↦ H^q(Gamma(Q)(S)), using exact presheaf evaluation; `cycleClass` includes
  the existing canonical `ShortComplex.mapHomologyIso` for that evaluation.
* The first existential `e` is an isomorphism of the entire presheaf complexes with
  the restriction of Phi(Q)_ab to tS. Conjunct 1 normalizes it by the invariant inclusion
  and the recorded represented evaluation `D.data.moduleSection`, degree by degree.
  Consequently neither the differentials nor the parameter restrictions are arbitrary.
* The second existential `beta` is the required presheaf isomorphism for every Q.
  Conjunct 2 specifies the acyclic-resolution comparison on every resolution cocycle,
  for every abelian injective resolution I and every chain map b over the augmentation.
  `freeParameterSheaf` is the actual sheafified free abelian representable;
  `generatorSection` evaluates its identity generator. `I.extEquivCohomologyClass`
  is Mathlib's canonical Ext computation. Thus beta is fixed by the canonical
  resolution comparison, rather than specified as an arbitrary presheaf isomorphism.
* Conjunct 3 gives compatibility with every equivariant coefficient map and every
  lift g over that map. The f = identity case gives independence of Q up to canonical
  resolution comparison. Different lifts give the same equation. Parameter naturality
  is already included because e and beta are morphisms in the presheaf category.
* The third existential `alpha` is a natural isomorphism of coefficient functors from
  sheafified P to U H^q R Gamma. Conjunct 4 is
  `sheafify(beta_Q.hom) ≫ alpha.hom.app M = sheafifiedComputation Q q`.
  The latter is explicitly the inverse exact-sheafification/homology comparison,
  cohomology of the sheafification counit, exact scalar-forgetting comparison and
  ordinary total-derived resolution computation. This fixes alpha = eta_Q beta_Q^{-1}
  for every resolution. `computation` uses the actual `rightDerivedFunctorUnitQ` and
  inverse of the localized augmentation, not an arbitrary map in a derived category.
* Conjunct 5 spells out the exact requested coefficient equation, in Lean composition
  order: `alpha_M ≫ U(R^q Gamma(f)) = sheafify(P_f) ≫ alpha_N`. This is also guaranteed
  by the natural-isomorphism type. No discreteness or cohomological bound is assumed.

Dependency declarations read and used:

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (reexported).
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.forget`, `Mod.regular`.
* `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `Modules`, `FixedAll`,
  `Invariants` and its inclusion (reexported by the calculus/presentation modules).
* `Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation`: `Space`, `coverage`,
  `trivialParameter`, `SetPresentation`, `ModulePresentation`, `ModuleData.moduleSection`,
  `ModuleProperties.additive` and its normalization/naturality equations.
* `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: the existing ordinary
  derived calculus, publicly reexporting `CondensedDerivedRestriction.invariants`,
  `derived`, action abelian/Grothendieck structures and `boundedBelowComputation`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.HomologySequence`:
  `DerivedCategory`, `singleFunctor`, `Q`, `homologyFunctor`, `homologyFunctorFactors`.
* `Sheaf.CategoryTheory.SiteCoveringAxioms` / Mathlib `SheafCohomology.Basic`:
  the dependency's retained `Sheaf.cohomologyPresheafFunctor` and `H'` conventions.
* `Sheaf.CategoryTheory.RingedSiteModules` / Mathlib `ModuleCat.Sheaf`:
  `ringedSiteModules` (the presentation's target) and `SheafOfModules.toSheaf`.
* Mathlib `Preadditive.Injective.Resolution`, `Abelian.Injective.Extend` and
  `Abelian.Injective.Ext`: `InjectiveResolution`, `cochainComplex`, `ι'`,
  `extEquivCohomologyClass` (public imports).
* Mathlib `Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction` and its counit.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionModuleEquivalence` and original section-module encoding (inherited by
  the action-module dependency). Scalar forgetting uses `Mod.forget` directly.
* Proof-only imports: `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
  `Sheaf.CategoryTheory.SheafTensor`. Other proof dependencies are Mathlib leaves already
  in the public imports or have no published Lean module yet, in particular
  `lem-sfb-module-resolution-derived-presheaf-comparison`; no duplicate theorem is written.

Edge cases checked before and while writing: q = 0 retains ordinary invariant sections;
q is an arbitrary natural number with no upper bound. The empty profinite parameter is
included in `parameters`; no nonempty-instance binder is present. Zero coefficients and
the zero module are allowed. For the trivial group, Gamma is the identity and positive
presheaf cohomology sheafifies to zero, as required: no claim of vanishing before
sheafification is made. Every arbitrary injective resolution and every lift over a map
is retained. The actual coefficient functor is unbounded-derived, even though the
resolutions of modules are nonnegative. No universe equality beyond the recorded
profinite-site size convention is imposed.

Searches (2026-10-24): msearch.py leanfinder, query “Sheafified action-site cohomology
computes higher derived internal invariants naturally”, returned `Sheaf.H`,
`Sheaf.cohomologyPresheaf`, `Sheaf.cohomologyPresheafFunctor` and topological continuous
cohomology; none is the theorem. msearch.py loogle, query
`CategoryTheory.Sheaf.cohomologyPresheafFunctor, CategoryTheory.InjectiveResolution.isoRightDerivedObj`,
returned no hits. msearch.py grep, query
`(invariants|fixedPoint).*(sheafif|cohomolog)|(sheafif|cohomolog).*(invariants|fixedPoint)`,
returned three ordinary/continuous representation-cohomology files, none matching.
msearch.py leansearch, query “Higher derived internal invariants of condensed modules are
sheafified object cohomology on the site of profinite group actions”, returned condensed
modules, discrete characterization and topological continuous cohomology, none matching.
The same regexp and the exact node id were searched with rg in both lean/WeilConjectures
and lean/Sheaf: only ingredients and the downstream continuity theorem's proof description
were found. Further rg searches located the existing Ext, resolution, evaluation and
homology interfaces used in the module. No second notion is defined; helpers specify
this comparison's own canonical complexes, maps and normalizations.

No statement correction, new DAG node, dependency-record repair or statement dispute.
The original statement and all dependency lists remain unchanged.

## Second reading by Q27

This reading was done by the maintainer's independent second reader. It replaces the
worker's own reread, which said it was not an independent review. I read the item node,
its 11 stmt_deps, Stacks sites-cohomology.tex Tag 072W (lemma-higher-direct-images and
its proof), the delivered module, and these declarations:
`CoherentPresentation.{SetPresentation, ModuleData, ModuleProperties, ModulePresentation,
trivialParameter, coverage, Space}`, `CondensedAction.{Invariants, FixedAll}`,
`CondensedDerivedRestriction.{invariants, derived, boundedBelowComputation}`,
`CondensedBar.{Ring, Modules, Equivariant}`, Mathlib `Sheaf.cohomologyPresheafFunctor`
and `InjectiveResolution.extEquivCohomologyClass`.

Node clauses and their Lean:

1. R, a commutative condensed ring on profinite sets with finite jointly surjective
   covers: `A : CondensedBar.Ring.{u}` (CommMon in coherent abelian sheaves on
   Profinite.{u}, values AddCommGrpCat.{u+1}). Correct.
2. J, a compact Hausdorff totally disconnected group: `J : Type u` with Group,
   TopologicalSpace, IsTopologicalGroup, CompactSpace, T2Space and
   TotallyDisconnectedSpace. No further assumption is made. Correct.
3. A_J(R): `Equivariant A J` = the recorded `ActionModule A.toMon J`. Correct.
4. Γ_{R,J} and R^qΓ = H^q(RΓ(M[0])): `(invariants A J).functor`, whose `Invariants`
   spec has inclusion image = `FixedAll` (fixed after every base change), and
   `singleFunctor 0 ⋙ derived A J ⋙ homologyFunctor q`, where
   `derived = rightDerivedFunctor` is the ordinary unbounded functor. Correct.
5. P_J, t and Φ with R_J = Φ(R): `(coverage J).toGrothendieck` on `Space J`,
   `parameters J = AsSmall.up ⋙ trivialParameter J`, and `D.data.equivalence` for an
   arbitrary `D : ModulePresentation J P A.toMon`. The theorem
   `profiniteAction_coherentPresentation` gives only ∃/Nonempty of such D. Quantifying
   over every normalized D is the faithful reading: the proof uses only exactness,
   additivity and the tS normalization, which every D satisfies. The ModuleProperties
   fields `trivialInjective`, `trivialImage`, `trivialMaps` and `trivialRestriction`
   are exactly "Φ(M)(tS) = Γ(M)(S) naturally".
6. P^q_M(S) = H^q(tS, Φ(M)_ab) with its restriction maps: `objectPresheaf D q` is
   Φ ⋙ SheafOfModules.toSheaf ⋙ Mathlib `cohomologyPresheafFunctor` (Ext from the
   sheafified free representable), whiskered by t^op. P^q_f is its `.map f`. Correct.
7. For every injective resolution M → Q^•, an isomorphism of presheaves
   H^q(Γ(Q^•)(S)) ≅ P^q_M given by the canonical acyclic comparison:
   - `e` is an isomorphism of presheaf complexes U Γ(Q) ≅ Φ(Q)_ab ∘ t. Conjunct 1 pins
     it degreewise: inclusion(x) = moduleSection(e x). It exists and is unique because
     both maps are injective with image FixedAll (`Invariants.injective/image`,
     `trivialInjective/trivialImage`).
   - `beta` is pinned by conjunct 2, for every abelian injective resolution I of Φ(M)_ab,
     every b over the augmentation and every Hom-complex cocycle z from the free
     representable sheaf: the class of the corresponding pointwise cycle y goes to
     `I.extEquivCohomologyClass.symm [z ≫ b]`. Each cycle y comes from such a z (Yoneda
     for the sheafified free representable, with the cocycle condition z ≫ d = 0), and
     I and b always exist, so beta is determined on all classes. The pin is exactly the
     072W/03FD comparison H^q(Φ(Q)(tS)) → H^q(I(tS)) = Ext^q. It is not vacuous and not
     an arbitrary iso.
8. Independence of the resolution, and naturality in coefficient maps and in parameter
   maps: conjunct 3 holds for every f and every lift g over f; f = id with any g gives
   resolution independence. beta is a morphism of presheaves on Profinite.{u}, which
   gives naturality in parameter maps. Correct.
9. α^q_M : (P^q_M)^# ≅ U(R^qΓ(M)), natural: `alpha`, a natural iso of functors on
   Equivariant A J. Conjunct 4, sheafify(beta_Q) ≫ α_M = η_Q, gives α = η_Q ∘ (β_Q^#)^{-1},
   as in proof step 4. `sheafifiedComputation` is the canonical η_Q, built from:
   - the inverse of the sheafification/homology iso;
   - the homology of the sheafification counit (an iso, because sheafToPresheaf is fully
     faithful);
   - the scalar-forgetting homology iso;
   - `computation` = homologyFunctorFactors⁻¹ ≫ H^q(rightDerivedFunctorUnitQ Q ≫ RΓ(inv Q(ι'))).
     It is invertible by `boundedBelowComputation`.
   Every factor is canonical; nothing is an arbitrary map.
10. Naturality equation U(R^qΓ(f)) ∘ α_M = α_{M'} ∘ (P^q_f)^#: conjunct 5, written in
    Lean's diagrammatic order. It is exact.
11. The node assumes no exactness of evaluation, no discreteness and no
    cohomological-dimension bound, and none appears in the Lean.

Edge cases: q = 0 is included, as is an arbitrary q with no bound. The empty profinite
S is included (no Nonempty binder). M = 0, A = 0 and trivial J are all allowed; for
trivial J, positive P^q sheafifies to 0 and no presheaf vanishing is claimed. Universes:
the single u, with the recorded u+1 coefficient and site-model levels and no extra
equality. The `HasExt.{u+1}` instance on action-site sheaves is a Prop instance
(`hasExt_of_enoughInjectives`), so it cannot create a diamond.

Records: the node copy differs from side-live only in `lean`, and `lean.statement`
matches the file verbatim (checked by script). The docstrings carry Stacks 072W/03FD and
`(blueprint: …)`. The theorem docstring has the five proof steps. The only proof is
`sorry`; the 19 helpers are real data or transparent instances.

Advisories, not faults:
- Space/coverage/trivialParameter are owned by def-sfb-profinite-action-space-site, and
  CondensedBar.* and invariants/derived by def-sfb-condensed-equivariant-bar-data and
  def-sfb-condensed-derived-invariants. None of these nodes is a stmt_dep. The node
  cites the presentation theorem and the calculus, which re-export them. S2 cannot add
  stmt_deps.
- SetPresentation and ModulePresentation are the specification structures of the cited
  presentation theorem's ∃. Quantifying over them is the witness form of that stmt_dep,
  not a plain-def-only citation.
- The proof dependency lem-sfb-module-resolution-derived-presheaf-comparison now has a
  Lean module (NO, 2026-10-24). The stage-3 proof can use its `abelian_resolution_comparison`.

Searches: rg in side-live lean/Sheaf and lean/WeilConjectures for
`SheafifiedCohomology`, `higherInvariants` and `cohomologyPresheafFunctor` found only the
downstream parent's `higherInvariants` (ProfiniteInvariantsFilteredContinuity, a
citer-side module) and unrelated site cohomology users. There is no duplicate of this
comparison.

Changed: only this report section. The Lean file and the node record are unchanged.

## Validation

The prescribed scompile.py wrapper compiled both the sandbox and named library versions
of the final file, with no errors or warnings. Temporary profiling and type checks were
removed. The prescribed deliver2.py --no-push dry run returned OK: the three-file packet
passes the maintainer’s preflight and compiles. Only the main theorem contains sorry;
all nineteen helper definitions and instances have complete data. The node copy differs
from the original only in lean, and its recorded signature is verbatim from the file.
