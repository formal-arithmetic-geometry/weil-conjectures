## Worker report

The module `Sheaf.CategoryTheory.SequencePushforwardLimitProjections` states
`SheafOfModules.SequenceProjection.pushforwardLimitProjections`, with one `sorry`
and no definitions or proved lemmas. It supplies the normalized comparison of the
sequence-projection right derived functor with derived inverse limit after termwise
scalar restriction, its actual projections, and the transported adjunction formulas.
The original node is unchanged except for `lean`. No new nodes or dependency repairs
are needed.

Sources read: `literature/stacks-project/sites-cohomology.tex`, the paragraphs and
lemmas at labels `section-derived-limits`, `lemma-derived-limit-is-ok` (0941),
`lemma-adjoint` (07A6), and `lemma-derived-pushforward-composition` (0D6E), together
with the node's eight proof steps. The module docstring reproduces those steps as
a proof plan, including the resolutions and the scalar transpose calculation.

Hypothesis and clause correspondence:

1. The small site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`
   with `[EssentiallySmall.{w} C]`. This allows independent object, morphism, and
   coefficient universes. The sheafification, locally-bijective, and sheaf-compose
   instances are the same size and sheaf infrastructure as the recorded
   sequence-site and sequence-projection dependencies, not new geometric
   assumptions. The site's precoverage formulation is the recorded
   `CategoryTheory.Precoverage.IsSiteForCoverings`; its associated topology is `J`.
2. The inverse sequence of commutative ring sheaves is
   `B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}`. Index `n` denotes the paper's `n+1`, so no
   positive level is omitted. The base ring sheaf is `A`, and all its compatible
   structural maps are the one natural transformation
   `α : (Functor.const ℕᵒᵖ).obj A ⟶ B`.
3. Strict semilinear systems use exactly `SheafOfModules.StrictRingSystem B`.
   Their level categories and evaluation functors are `systemLevel B n` and
   `systemEvaluation B n`. `strictSystemSequenceEquivalence` is the recorded
   equivalence with module sheaves on the product sequence site. No new system
   category or copied tensor construction is introduced.
4. All unbounded derived categories are the existing `DerivedCategory.{d}`,
   with localization `DerivedCategory.Q`. The explicit `HasDerivedCategory`
   binders select the common morphism-size convention for base modules, strict
   systems, constant-coefficient towers, and each level. There is no equation
   between the site and coefficient universes and no boundedness restriction.
5. The initial witnesses `G, F, e, π, adj, L, R, ε, η, derivedAdj` and their
   properties reproduce the normalized presentation in the recorded
   `SequenceProjection.derivedAdjunction`. This retains that dependency's actual
   objects: ordinary pullback `G`, ordinary pushforward `F`, `L = Lp*`, `R = Rp*`.
   These are existential conclusions, not extra hypotheses. The six ordinary
   conditions specify the natural level tensor comparison `e`, the actual
   semilinear transitions, naturality and compatibility of the projections `π`,
   their compatible-family limit universal property, and the transpose on tensor
   generators using the existing `tensorSection`. The following derived
   conditions give universal left/right derived pairs, their computations on
   K-flat/K-injective representatives, the common K-flat resolution model, and
   the chain-map normalization of `derivedAdj`.
6. Termwise scalar restriction is the existential exact functor `U0` to
   `ℕᵒᵖ ⥤ Modules A`, with `uObj` fixing each object to the actual
   `(restriction A B α n).obj (N.level n)`. The first two conditions after all
   witnesses fix its maps and transitions to those of the given system, on
   sections. `uEval` is an ordinary natural isomorphism whose component is
   exactly `eqToHom (uObj N n)`. Thus neither the tower nor its maps are arbitrary.
   `U = U0.mapDerivedCategory` is Mathlib's exact induced functor, not another
   freely chosen derived restriction.
7. `πOrd` packages the already specified `π` as a natural transformation;
   `(πOrd n).app N = π N n`. The ordinary identification `fLim` has the condition
   `fLim.hom.app N ≫ limit.π ... ≫ (uEval n).hom.app N = π N n`.
   This realizes `p_* N = lim_n Res_n N_n` with the actual limit projections.
8. `RL` with `etaLim` is the total right derived functor of the ordinary `lim`,
   by `RL.IsRightDerivedFunctor etaLim ...`; its comparison is invertible on
   K-injective tower complexes. Consequently `U0.mapDerivedCategory ⋙ RL` is
   the node's `𝓛 = Rlim U`.
9. `piLim n : RL ⟶ eval_n.mapDerivedCategory` is fixed by
   `etaLim.app T ≫ (piLim n).app (Q.obj T) ≫ evalFactors.hom.app T =
   Q.map ((NatTrans.mapHomologicalComplex (lim.π (op n)) ...).app T)`.
   This normalizes projections by the ordinary projections on every complex,
   and in particular gives the actual total-limit projections after resolution.
   `xi n` identifies restricted tower evaluation with level evaluation followed
   by derived scalar restriction. Its displayed equation normalizes it by
   `uEval` and the existing `mapDerivedCategoryFactors` isomorphisms.
   The node's `π_n` is therefore
   `(piLim n).app (U.obj N) ≫ (xi n).hom.app N`.
10. The natural comparison is the actual functor isomorphism
    `c : R ≅ U0.mapDerivedCategory ⋙ RL`. Its resolution equation quantifies over
    every K-injective strict-system complex `I`, every K-injective tower `T`, and
    every quasi-isomorphism `j : U0(I) ⟶ T`. It asserts that `lim(j)` is a
    quasi-isomorphism and that the component of `c` is its class, after the
    `fLim`, `η`, `etaLim`, `U.mapDerivedCategoryFactors` identifications and
    `RL.map (inv (Q.map j))`. This specifies the comparison from actual
    resolutions, rather than an isomorphism of unspecified homotopy-limit objects.
11. The next equation starts with `η.app I`, then `c.hom.app (Q.obj I)`, then
    `piLim`, `xi`, and the level/restriction factor isomorphisms. Its right side
    is `Q.map ((NatTrans.mapHomologicalComplex (πOrd n) ...).app I)`.
    This is precisely preservation of actual pushforward/total-limit projections.
    It is stated for every system complex, so no implicit K-injectivity condition
    is imposed on its underlying restricted tower or its levels.
12. `levelAdj n : G ⋙ systemEvaluation B n ⊣ restriction A B α n` is normalized
    by `tensorSection`: the inverse transpose of `h` sends `b ⊗ x` to
    `b • h(x)` after the same `e` identification. `derivedLevelAdj n` is the
    corresponding adjunction with left functor
    `L ⋙ (systemEvaluation B n).mapDerivedCategory`. Its equation on every
    chain map uses `ε`, the level comparison, and the exact restriction's
    `mapDerivedCategoryFactors`. This is the canonical derived scalar-extension
    adjunction, not an arbitrary adjunction between the same functors. The
    simultaneous K-flat computation of `L` above identifies its left functor
    with `- ⊗ᴸ_A B_n`.
13. Transport is literally Mathlib's `derivedAdj.ofNatIsoRight c`. Its unit and
    counit are thus the specified old unit followed by `c`, and `L(c.inv)`
    followed by the old counit, respectively. These constructions are fixed by
    that API and are not separately existentially chosen transformations.
14. The projected unit equality is
    `(derivedAdj.ofNatIsoRight c).unit.app P ≫ piLim ... ≫ xi ... =
    (derivedLevelAdj n).unit.app P`. It states exactly the reduction-unit clause.
15. Evaluating the transported counit by
    `(systemEvaluation B n).mapDerivedCategory.map` equals
    `((derivedLevelAdj n).homEquiv ...).symm (piLim ... ≫ xi ...)`.
    This is precisely that its nth component is the scalar-extension adjunct
    of the actual total-limit projection.
16. For arbitrary `h : P ⟶ (U ⋙ RL).obj N`, the evaluated inverse transported
    Hom bijection equals `(L ⋙ evalDerived_n).map h` followed by the evaluated
    transported counit. In paper notation this is
    `e_{N,n} ∘ (h ⊗ᴸ_A B_n)`.
17. The last two clauses explicitly give both triangle identities, with right
    side `𝟙`, in the actual selected derived categories. Naturality in `P,N`
    comes from the named functors, natural isomorphisms, and adjunctions.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (the site convention).
- `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction`:
  `SheafOfModules.SequenceProjection.Modules`, `restriction`, `tensorSection`,
  and `derivedAdjunction` (the normalized initial witness presentation).
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `SheafOfModules.strictSystemSequenceEquivalence`, together with the imported
  `StrictRingSystem`, `systemLevel`, and `systemEvaluation` interfaces.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients` supplies
  the total right derived `lim` and its K-injective normalization, at independent
  site/coefficient universes. Its older companion does not force equal universes
  in this statement.

The proof-only imports include the recorded modules for scalar restriction,
K-flat resolutions, the cochain derived-change-of-rings model, resolving-class
adjunction, ringed-topos pushforward composition, module adjunction, and
K-injective resolutions. No missing or unusable statement dependency was found.

Edge cases checked: the zero ring and zero complexes are allowed; no nonzero,
faithfulness, flatness of `A → B_n`, or surjectivity of transitions is assumed.
Constant sequences, identity maps, and arbitrary varying ring sequences are all
allowed. The empty site is allowed. The index is the full positive sequence,
reindexed by all of `ℕ`; no terminal truncation or eventual-constancy assumption
is present. Complexes are unbounded in `ℤ`, including the zero and degree-zero
cases. No exactness of countable products is imposed. There is no K-injectivity
assumption on a restricted system or on its evaluated complex. Morphisms `h` are
arbitrary derived morphisms, not only classes of chain maps. Scalar adjunction
normalization is stated for arbitrary target complexes.

Searches actually run with `batch2/msearch.py`:

- LeanFinder query: "Derived pushforward of semilinear ring module sequence equals
  derived inverse limit after scalar restriction preserving projections and
  adjunction units". Eight hits: linearity of `mapDerivedCategory`, ordinary
  pushforward adjunctions, and module-presheaf pushforward formulas. None states
  the varying-ring, resolution-normalized total-limit comparison.
- Loogle query: `Adjunction.ofNatIsoRight, Functor.IsRightDerivedFunctor`.
  The service returned zero hits and `unknown identifier 'Adjunction.ofNatIsoRight'`.
  This is an identifier-resolution failure, not evidence of absence. The exact
  Mathlib API was located and read directly in `CategoryTheory/Adjunction/Basic.lean`.
- Mathlib grep query: `ofNatIsoRight|rightDerived.*[Ll]imit` in `CategoryTheory`.
  Fourteen hits, including `homEquiv_ofNatIsoRight_apply` and its inverse version.
  They supply abstract transport, not this ringed-sequence comparison.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `SequenceProjection`, `totalLimitProjection`, and `limitProjection` located the
  normalized dependency, specialized coefficient sequence projections and completed
  coefficient comparisons. Those latter modules are specialized to coefficient
  data; none supplies the present arbitrary site/ring-sequence statement.
- Direct `grep -rn` of the exact item id in `lean/WeilConjectures` gave no match.
  A further `rg` of `dag/lean_names_upstream.json`, Mathlib and project source for
  the proposed name found no conflicting declaration. Generic `ofNatIsoRight`
  uses elsewhere are not matches for this theorem.

Validation: `scompile.py NL lem-coef-sequence-pushforward-limit-projections` was
used for every compile. Initial scratch checks verified the exactness instances
for actual level evaluation and scalar restriction, and the ordinary tower limit
instance; these temporary `example` and `#check` declarations were removed. The
first full compile exposed the `SheafOfModules.evaluation` namespace collision;
all tower evaluation uses were qualified as `CategoryTheory.evaluation`. Both
sandbox and real-module checks then compiled, with only a long-line warning;
that line was wrapped. Final verification is recorded below after the delivery
preflight.

There is no STATEMENT-DISPUTED finding and no statement correction.

Final verification: the delivery dry run returned
`OK (dry run): commit fc625553875 passes the preflight and compiles; nothing pushed`.
The final module compiles in both sandbox and actual-module checks without warnings.
The local record check found only the `lean` field changed, a verbatim signature,
exactly one postponed theorem, and no source line longer than 100 characters.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
