## Worker report

Item: `lem-pur-system-block-repetition`. Module:
`Sheaf.Paper.SystemBlockRepetition`, namespace `WeilConjectures.SemilinearSections`.
This is a statement-only delivery: all postponed proofs are named theorems with
source, blueprint identifier and natural-language proof docstrings. Definitions
construct the actual ringed-site reindexing functors and canonical derived maps;
none chooses an arbitrary functor or map from an existence assertion. The node's
non-Lean fields are unchanged. The multiple declarations in `lean.declarations`
state the successive clauses of this single lemma.

The source was read in Zheng, Construction 4.1 (printed p. 21) and the geometric
morphism paragraph preceding Lemma 4.10 (printed p. 23), in the PDF named by the
node. Finite nonempty blocks are the node's stated generalization. The proof also
uses the cited Stacks results on K-injectives, exact functors and derived
adjunctions, as recorded in the node and the declaration docstrings.

Clause-by-clause translation:

1. **Sites, rings and strict semilinear systems.** `C : Type c`,
   `[Category.{v} C]`, `J : GrothendieckTopology C`, the coefficient sheaves `B`
   and transition morphisms `τ` are explicit binders. `Systems J B τ` is the
   dependency's actual sheaf-of-modules category on its ringed sequence site;
   it is not replaced by a product of independent module categories. `DS` and
   `DerivedCategory` are ordinary unbounded derived categories. The size
   assumptions are those of the dependency's small-site presentation. The site
   object and morphism universes remain separate.
2. **Geometric morphism and pulled-back coefficients.** In `GeometricSystems`,
   `J'`, `uInv`, `uPush`, `adjSet`, `A : Data ...` and `G : Geometry ...`
   are the dependency's geometric data. `G.coefficients`,
   `G.coefficientTransition`, `G.inverseImage`, `G.levelPush`, `G.pull`,
   `G.push` and `G.ordinaryAdjunction` provide the specified coefficients and
   geometric functors, rather than new unrelated choices.
3. **Block map and first endpoints.** `SystemBlockMap.index : ℕ →o ℕ`,
   `onto : Function.Surjective index` and `finite` give nondecreasing,
   surjective, finite nonempty fibers. Fibers are intervals by monotonicity.
   Index `n` represents the paper's positive index `n+1`, covering all its
   indices without excluding the first. `SystemBlockMap.first` is `Nat.find`
   of surjectivity, hence the least point, not a chosen point. The endpoint,
   interval and no-skipped-boundary assertions are `systemBlockMap_endpoints`.
4. **Repeated rings and transitions.** `blockCoefficients B t m` is
   `B (t.index m)`. `blockTransitions` is the actual `coefficientMap` along
   monotonicity. Thus it is the identity within a block and the given adjacent
   transition at a boundary; the no-skipped-boundary clause justifies the latter.
   This is applied on both sites, including the pulled-back ring sequence.
5. **Repetition on objects, arrows and transitions.** `blockSite` is the
   actual product of the index functor and the identity on the site.
   `blockRepeatRing` identifies its pulled-back ring with the repeated ring.
   `blockRepeat` is `SheafOfModules.pushforward` along this ringed-site map.
   In `SystemBlockRepetition`, `repetition_canonical`, `evaluation`,
   `evaluation_sections` and `repeat_restrictions` specify the actual functor,
   its module coefficients, identity section realizations, all arrows and all
   horizontal and vertical restrictions. Functoriality gives its action on
   compatible system morphisms.
6. **First-endpoint functor and its transitions.** `blockEndpointRing` gives
   the canonical ring identification at the least endpoints, and
   `blockEndpoint` is restriction along `t.endpoints`. The package's
   `endpoint_canonical`, `endpoint_sections`, `endpoint_maps` and
   `endpoint_restrictions` specify precisely `P_(a_i)`, component morphisms
   and composite transitions along `a_i ≤ a_(i+1)`.
7. **Exact additive adjunction and adjunct formula.**
   `SystemBlockRepetition.adjunction : endpoint ⊣ repetition` has the required
   direction. Its `adjunct` field identifies each section of the adjunct with
   the composite transition to the first endpoint followed by `f_i`.
   `repeat_additive`, `repeat_limits`, `repeat_colimits`,
   `endpoint_additive`, `endpoint_limits` and `endpoint_colimits` give
   additivity and exactness in the abelian categories. `systemBlockRepetition`
   asserts existence of this entire specified package for every tower and map.
8. **K-injective preservation.** `kinjective` quantifies over unbounded
   `CochainComplex (Systems J B τ) ℤ` and uses Mathlib's `IsKInjective`.
   The wrapper instance `SystemBlockRepetition.preservesKInjective` supplies
   the existing derived-functor API. The proof docstring uses the exact LEFT
   adjoint on acyclic complexes and homotopy classes, never an unsupported
   claim that component evaluation preserves K-injectives.
9. **Canonical derived comparison.** `blockDerivedComparison` is an explicit
   composite of the existing canonical right-derived composition isomorphisms
   and the derived image of the ordinary square. Its type is
   `RX.mapDerivedCategory ⋙ GD.rightDerivedFunctor ≅
   G.rightDerivedFunctor ⋙ RY.mapDerivedCategory`, the node's κ orientation.
   `SystemBlockGeometry` and `systemBlockGeometry` supply the actual repeated
   geometric functors on the repeated coefficient categories. Their
   `pull_evaluation` and `push_evaluation` use the given level functors at
   `t(m)`; the two squares are identities on every section. The definition
   `SystemBlockGeometry.comparison` specializes the canonical construction
   directly to these system categories.
10. **Normalization, uniqueness, arrows and transitions.**
    `blockComplexComparison` is the actual complex comparison induced by the
    ordinary system square. `blockDerivedComparison_normalization` states
    the derived-unit equation for every complex, including non-K-injectives,
    with the explicit `mapDerivedCategoryFactors` identifications. Its second
    conjunct says that normalization already on all K-injective representatives
    uniquely determines the natural isomorphism. Since the normalization is
    an equality of system maps before localization, it includes transitions;
    equality of natural isomorphisms fixes their action on every derived arrow
    and makes resolution choices irrelevant. It does not infer system equality
    from faithfulness of derived component evaluations.
11. **Inverse image and units/counits.** `SystemBlockGeometry.pull_square`
    is the inverse-image commutation square, with `pull_square_sections`
    fixing its strict realization. `push_square_sections` fixes the direct
    square similarly. Its `unit` and `counit` are the ordinary geometric
    equations. `blockDerivedComparison_adjunction` states BOTH equations
    for the actual `mapDerivedCategoryRightDerivedAdjunction` unit and counit,
    with the derived inverse-image square and κ (or its inverse) in their
    typed positions. Applying it to the geometric package supplies the node's
    adjunction compatibility.
12. **Compatible coefficient maps and exact restriction of scalars.**
    `blockRepeat_restrictScalars` binds `B'`, `τ'`, `b` and its compatibility
    `hb`, supplies the repeated compatibility `hd`, and states the strict
    functor equality using the dependency's `systemMap` and `res`. This gives
    `R U_b = U_d R` on either site. Exactness of `res` is inherited from the
    dependency. No flatness assumption is introduced.
13. **Universal β and the coefficient equation.**
    `blockCoefficientComparison` defines β from
    `rightDerivedFunctorCompMapDerivedCategoryIso` and
    `rightDerivedPullback`, thus from the total-right-derived universal
    comparison, not from a chosen inverse. `blockCoefficientComparison_naturality`
    gives the node's two routes as an equality of derived system morphisms.
    The `b`, `d`, `ex`, `ey` ordinary squares and their `cube` are the
    section-identity squares in the coefficient specialization. The direction
    of the written equation is β_d, then κ_B on one side and κ_B', then β_b
    on the other (Lean's `≫` composes left to right). Neither restriction of
    scalars preserving K-injectives nor β being invertible is a hypothesis.
    The proof uses the normalization on the possibly non-K-injective `U_b I`.
14. **Composition and identity.** `SystemBlockMap.comp` and `.id` give the
    actual composite and identity index functions. `blockRepeat_comp` and
    `blockRepeat_id` state the strict functor identities, including explicit
    coefficient-transition equalities. `blockDerivedComparison_comp` states
    that the composite comparison is the composite of comparisons under the
    canonical derived composition identifications; its ordinary `coherent`
    equation is the strict reindexing identity. `blockDerivedComparison_id`
    supplies the identity law under the canonical identity identifications.
15. **Open localization and extension by zero.** `blockOpenRepeatRing` and
    `blockOpenRepeat` use the actual restricted tower on the slice site
    `J.over U`, with its coefficient presentation. `blockOpenRepeat_exact`
    supplies its exactness and additivity. `blockRepeat_extensionByZero`
    provides compatible `OpenSystems` realizations and a UNIQUE comparison
    whose evaluation agrees with the identical level extension of
    `P_(t(m))`. The dependency's `OpenSystems` already supplies exact actual
    extension by zero and its level direct-sum/sheafification construction.
    Its arbitrary level-identification choices are not assumed normalized;
    the theorem chooses compatible realizations and fixes the comparison by
    the displayed normalization. Heterogeneous equalities express identity
    through the explicitly identified coefficient presentations. For these
    realizations it is the strict levelwise identity in the node. The final
    `blockRepeatDerivedExtensionByZero` definition is its termwise derived
    descent. Substitution by a second block index leaves the same normalized
    section formula, giving the stated compatibility with the reindexings;
    uniqueness prevents a different comparison from appearing.

Dependency declarations read and used:

- Statement dependency `lem-coef-semilinear-derived-sections`:
  `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`, together with
  its exported `Systems`, `DS`, `Data`, `Geometry`, `OpenSystems`, `evaluation`,
  `coefficientMap`, `systemMap`, `res`, `openRings` and `openTransitions`.
- `def-sfb-right-derived-functor`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  the universal, uniqueness and unit-isomorphism interface for
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`. The concrete canonical
  `rightDerivedFunctor` and its unit are the upstream library implementations.
- `lem-sf-kinjective-derived-map-computation`:
  `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`,
  `CategoryTheory.Functor.kInjectiveDerivedMapComputation` and the resolution-transition
  computation/naturality interfaces.
- `lem-sfb-grothendieck-k-injective`:
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`,
  the existing Grothendieck-abelian K-injective-resolution instance.
- `lem-weil-pbc-adjunction-of-natural-bijection`: Mathlib
  `CategoryTheory.Adjunction.mkOfHomEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Basic` (its `mathlib_match` is used).
- `lem-weil-pbc-exact-functor-derived-factorization`: the existing
  `CategoryTheory.Functor.mapDerivedCategoryFactors` exact-functor interface
  from Mathlib/upstream (its `mathlib_match` is used).
- `lem-weil-pbc-exact-square-derived-counit`:
  `Sheaf.CategoryTheory.ExactSquareDerivedCounit`,
  `CategoryTheory.exactSquare_derived_counit`.
- Canonical-map APIs reused from upstream:
  `Functor.mapDerivedCategoryCompRightDerivedFunctorIso`,
  `Functor.rightDerivedFunctorCompMapDerivedCategoryIso`,
  `Functor.rightDerivedFunctorNatIso`, `Functor.rightDerivedPullback`,
  `Functor.rightDerivedFunctorUnitQ`, `Functor.mapDerivedCategorySquareIso`,
  `Functor.mapDerivedCategoryCompNatIso`, `Functor.mapDerivedCategoryNatIso`,
  `Functor.mapDerivedCategoryIdIso` and
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`, from the imported
  derived composition, short-exact pullback, cocycle and mate modules.

Edge cases checked by reading the formulas and types: zero-based first index;
singleton blocks and identity map; unequal finite block lengths and their
boundaries; consecutive blocks with an endpoint transition crossing a whole
interval; composition and its finite fibers; zero rings, zero module sheaves,
empty/degenerate topoi; arbitrary unbounded complexes; nonflat ring maps and
restriction of scalars that need not preserve K-injectives. No boundedness,
nonzero ring/module, nonempty site, constant block length or invertible β is
assumed. The geometric coefficient universe is the dependency's `max c v r`,
not an identification of site object and morphism universes.

Searches (the launcher search output is retained in `searches.jsonl`):

- `msearch.py ... leanfinder` with “Repeating finite blocks of inverse systems
  of sheaves of modules preserves K-injectives and commutes with unbounded
  derived direct image”: eight unrelated hits, headed by
  `localCohomology.diagram`, with no finite-block system adjunction/comparison.
- `msearch.py ... loogle` with `CategoryTheory.Functor.whiskeringLeft`:
  twelve generic whiskering declarations, no instance of this statement.
- `msearch.py ... grep` with
  `blockRepetition|block.repetition|semilinear.*[Ss]ystem`:
  only `Mathlib/Algebra/Ring/CompTypeclasses.lean`, an unrelated comment.
- `msearch.py ... leansearch` with “Repeating blocks of a sequence of module
  sheaves has an exact left adjoint and preserves K injective complexes”:
  eight generic sheafification/limits/exact-colimit hits; none states this lemma.
- Direct `rg` searches of `lean/WeilConjectures`, `lean/Sheaf`, DAG records and
  upstream names for block repetition, endpoint and semilinear-system vocabulary,
  and the literal item identifier, found the dependency's system framework but
  no existing block-repetition declaration. The final exact-name search for
  `lem-pur-system-block-repetition|blockRepetition|blockRepeat|SystemBlockMap|systemBlockRepetition`
  in both source trees and `dag/lean_names_upstream.json` returned no hits.

No new independent notion, dependency-module repair or statement correction is
needed: the local helper constructions are the reindexing, endpoints and
comparisons that this very node introduces. No statement dispute remains.

Validation: `scompile.py Q22 lem-pur-system-block-repetition
<.../lean/Sheaf/Paper/SystemBlockRepetition.lean>` compiled the final module on
the live server both as sandbox and as its library module, with no errors or
warnings (other than the permitted postponed-theorem status). Auto implicits
are disabled, universes are explicit, and declaration lines are at most 100
characters. The prescribed `deliver2.py --no-push` dry run passed preflight and per-file
compilation (commit `8634dc7b8d2`; nothing pushed). The report was then corrected
to spell the existing map-computation namespace as `CategoryTheory.Functor`.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
