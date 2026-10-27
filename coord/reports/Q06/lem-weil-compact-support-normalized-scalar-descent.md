## Worker report

The module `Sheaf.Paper.CompactSupportNormalizedScalarDescent` states
`WeilConjectures.sfCompactSupportNormalizedScalarDescent`, with `sorry` as its entire
proof. It asserts only the two unit/tower equations of the assigned node; no
common-stage independence, shifts or additional coherence conclusions are asserted.
The node's statement, dependencies and proof are unchanged. There are no new nodes
or dependency repairs.

Hypothesis and clause correspondence:

- The base field is `(K₀ : Type u) [Field K₀]`. The prime is `(l : ℕ)
  [Fact l.Prime]` and its invertibility is `hl : IsUnit (l : K₀)`.
- `X Y : Scheme.{u}` carry `Over (Spec (.of K₀))`. Each structure morphism has
  `LocallyOfFiniteType` and `QuasiCompact`, precisely finite type. The morphism
  `f : X ⟶ Y` carries `IsOver`, `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact`. No separatedness of either structure morphism is imposed.
- The fixed compactification is `(c : Compactification f)`.
- The algebraic closure is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`, allowing its universe to differ from the scheme's.
- Every finite subextension is in `Padic.FiniteCoefficientFields l Ω`. The existing
  `Coefficient.{u} l Ω A` is its canonical small coefficient model. `Stage l Ω X A`
  is definitionally the recorded raw `sfRationalConstructibleCategory`, whose objects
  are integral representatives and whose morphisms are the scalar-localized Hom groups;
  no idempotent completion is substituted.
- The integral and rational compact-support functors are exactly
  `sfCompactSupportFiniteIntegralFunctor` and `sfCompactSupportFiniteFunctor`, with
  the same `l K₀ hl c`. Their already fixed integral value normalization and pure-tensor
  Hom action are used, rather than assumed anew or replaced by arbitrary functors.
- Completed integral scalar extension is the existing `integralTransition` and raw
  rational scalar extension is `transition`, in both X and Y.
- The supplied normalized integral isomorphisms are the family `b A B h`.
  `_hb` is exactly the `SfCompactSupportIntegralBetaSpec` conjunct from
  `sfCompactSupportNormalizedScalarIsomorphisms`, retaining the finite mate's full
  mixed-unit homotopy-category normalization and its Hom bijection for every target.
  `_hsystem` is exactly that theorem's second conjunct: the underlying component is
  `sfCompactSupportScalarSystemMap`, the fixed whole-system/derived-limit realization.
  Both conditions are retained: degreewise reduction alone is insufficient.
- The family `β A B h` has precisely the raw rationalized functor endpoints.
  `_hβ` is the componentwise localization condition, literally the final conjunct
  of `sfCompactSupportNormalizedScalarIsomorphisms`. The `HEq` here expresses the
  dependency's prescribed identification of endpoints; neither conclusion uses `HEq`.
- The canonical scalar `a` is the existing `associator l Ω W A M N h k`, which
  transports `sfRationalScalarComp` along the coefficient-inclusion composition law.
  The canonical scalar `e` is `unitor l Ω W A`, which transports
  `sfRationalScalarUnit` along the identity coefficient-inclusion law. Neither
  associator nor unit is an arbitrary parameter.
- First conclusion: for every A and K the first conjunct reads
  `β_A/A,K ≫ G_A.map(e_X,K) = e_Y,G_AK`. This is exactly
  `G_A(e_X,K) ∘ β_A/A,K = e_Y,G_AK`, in Lean's diagrammatic order.
- Second conclusion: for every `A M N`, `h : A ≤ M`, `k : M ≤ N` and
  `K : Stage l Ω X A`, the second conjunct reads
  `a_Y,G_AK ≫ β_N/A,K = T_Y,N/M.map(β_M/A,K) ≫ β_N/M,T_X,M/AK ≫ G_N.map(a_X,K)`.
  This is the displayed tower equation in diagrammatic order. The direct inclusion
  uses `h.trans k`, and both sides are arrows in the actual rational N-category.

Dependency declarations read and used:

- `def-weil-scheme-morphism-properties` is a convention record with no declaration.
  Its finite-type/separated/over-field clauses use the standard scheme predicates
  listed above, exposed by the recorded modules.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`, and
  `sfRationalScalarExtension` (the localization signature and full scalar-extension
  object and pure-tensor specification were read).
- `Sheaf.Paper.QcqsCompactSupportRealization`, publicly retaining
  `Sheaf.Paper.IntegralRationalQbarCompactSupport`: the recorded
  `sfIntegralCompactSupportValue` and its normalization, used through the fixed
  compact-support functor; no substitute value construction.
- `Sheaf.Paper.CompactSupportFiniteAction`:
  `sfCompactSupportFiniteIntegralFunctor`, `sfCompactSupportFiniteFunctor`,
  `sfCompactSupportFiniteHomMap`, and the fixed finite-reduction interface.
- `Sheaf.Paper.IntegralScalarExtensionUniverses` publicly retains
  `integralScalarExtension` and its independent-universe interface; the restrictions
  in `integralTransition` are the already recorded completed extension.
- `Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms`:
  `sfCompactSupportNormalizedScalarIsomorphisms`, `sfCompactSupportScalarSystemMap`,
  and its publicly retained `SfCompactSupportIntegralBetaSpec` from
  `Sheaf.Paper.CompactSupportCoefficientAction`.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarComp` and
  `sfRationalScalarUnit`, reused by `GeneralAlgebraicallyClosedCoefficients.associator`
  and `.unitor` from `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.

All eight additional recorded proof-dependency modules are plain imports. The proof
nodes `lem-weil-compact-support-system-transpose-normalization` and
`lem-weil-mixed-reduction-unit-composition` have no recorded module in the current
DAG and therefore no import is invented for them. The theorem docstring retains all
seven proof steps, including whole-system transposition, restriction cocycle,
iterated-unit normalization, injectivity of the whole-system Hom bijection, counit
cancellation in realization and finally raw rationalization.

Edge cases checked by reading the signatures and checking both equation endpoints:
A=M, M=N and A=M=N are allowed by non-strict `≤`; the first conjunct explicitly
uses `le_rfl`. Empty schemes, zero objects and zero morphisms are unrestricted.
The source category contains all raw rational objects, with no chosen nonzero
representative, Tor-domain, separated-base, smoothness or positive-degree hypothesis.
The closure universe v is independent; the coefficient small models are the same as
in the dependency, rather than an extra coefficient/site universe equality.

Searches before writing (all via the prescribed tools):

- msearch leanfinder: "The normalized compact support scalar comparisons satisfy
  identity and tower compatibility in rational derived categories". Eight unrelated
  scalar-tower results (`IsScalarTower.rat`, `.nnrat`, rational casts); no match.
- msearch loogle: `CategoryTheory.Functor.mapIso`. Twelve general functor/isomorphism
  results; none assert the normalized compact-support coefficient equations.
- msearch grep, CategoryTheory: `compactSupport.*[Cc]oher|[Nn]ormalizedScalarDescent|[Nn]ormalized.*[Tt]ower`.
  Zero results.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for normalized scalar descent and
  compact-support coherence: no exact statement. Existing site/compactification
  coherence and `RationalCompactSupportCoefficientCoherence` concern other categories
  and normalized base-change exchange, not these prescribed maps. The latter was
  opened and its full signature checked; its PBC coefficient-family conclusion is
  different from this node. The normalized scalar-isomorphisms theorem explicitly
  supplies only individual inclusions, with no tower equation.
- `grep -rn` for this node id in `lean/WeilConjectures`, and `rg` for the proposed
  declaration in `dag/lean_names_upstream.json`, `lean/WeilConjectures` and
  `lean/Sheaf/Paper`: no result before writing.

The current blueprint's `lem-fix-operation-reduction.md`, its compact-support scalar
comparison source, and `sk-thm-sf-pf-field.proof.md` were read under
`literature/blueprint/latest`. The older precise sublemma filename in the DAG's
source record no longer exists in latest; the current operation-reduction statement
retains coefficient extension and preservation of associativity, units and counits.
This does not require changing the node statement. No statement is disputed.

Validation: the new module compiled on the server through `scompile.py`, with no
errors or warnings. The full final import list is also checked by delivery preflight.

## Second reading by Q06

Independent second reading (maintainer review service, delivery 6ad6b1ec), written
after opening the node, the source record, the module and every declaration used.
It replaces the earlier self-check, which was not a separate reading.

Node clauses and their Lean:

- K₀ a field: `(K₀ : Type u) [Field K₀]`. Correct.
- X, Y finite-type K₀-schemes: `X.Over`, `Y.Over (Spec (.of K₀))` with
  `LocallyOfFiniteType` and `QuasiCompact` structure maps. Correct; no separatedness of
  X or Y is added.
- f separated finite type over K₀: `f.IsOver`, `IsSeparated f`,
  `LocallyOfFiniteType f`, `QuasiCompact f`. The binder block is byte-identical to the
  `variable` block of the landed dependency module
  `Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms`, so nothing is stronger.
- ℓ prime invertible in K₀: `(l : ℕ) [Fact l.Prime]`, `hl : IsUnit (l : K₀)`. Correct.
- Ω algebraic closure of Q_ℓ: `[IsAlgClosure (Padic l) Ω]`, Ω in an independent
  universe v. Correct.
- compactification c: `(c : Compactification f)`. Correct.
- finite subextensions A ⊆ M ⊆ N: `Padic.FiniteCoefficientFields l Ω` with `≤`; the
  categories C_A^Z / D_A^Z are `sfIntegralConstructibleCategory` and
  `Stage l Ω Z A` (definitionally `sfRationalConstructibleCategory l (Coefficient l Ω A) Z`,
  the raw Hom localization, no Karoubi completion). Correct.
- F_A, G_A: the fixed `sfCompactSupportFiniteIntegralFunctor` and
  `sfCompactSupportFiniteFunctor` of def-weil-compact-support-finite-action. Not free.
- T̂^Z_{B/A}, T^Z_{B/A}: `integralTransition` (= `sfConstructibleIntegralScalarExtension`)
  and `transition` (= `sfRationalScalarExtension`), with the coefficient inclusion.
- b_{B/A} the prescribed normalized comparisons: family `b` with `_hb`
  (`SfCompactSupportIntegralBetaSpec`, full mixed-unit Hom-bijection normalization) and
  `_hsystem` (components equal `sfCompactSupportScalarSystemMap`, the fixed derived-limit
  realization). These are exactly the first two conjuncts of
  `sfCompactSupportNormalizedScalarIsomorphisms`; `_hsystem` pins every component, so
  b is determined and the hypothesis is satisfiable (by that theorem's ∃ for each h).
- β_{B/A} their raw localizations: `_hβ`, literally the dependency's final conjunct
  (HEq with `sfRationalConstructibleLocalization.map (b.hom.app K.obj)`). β is pinned.
- a^Z_{N,M,A}, e^Z_A canonical scalar associator/unit of
  lem-weil-scalar-extension-composition: `associator` = `sfRationalScalarComp` followed by
  `eqToIso` along `coefficientInclusion_laws` (∃!-pinned by HEq to `scalarAssociator`),
  `unitor` = `eqToIso` then `sfRationalScalarUnit`. The canonical maps, not parameters.
- Unit equation G_A(e^X_K) ∘ β_{A/A,K} = e^Y_{G_A K}: first conjunct
  `(β A A le_rfl).hom.app K ≫ G_A.map ((unitor X A).hom.app K) = (unitor Y A).hom.app (G_A K)`.
  Endpoints and diagrammatic order checked. Correct.
- Tower equation β_{N/A,K} ∘ a^Y = G_N(a^X_K) ∘ β_{N/M,T K} ∘ T^Y_{N/M}(β_{M/A,K}):
  second conjunct `a^Y.hom.app (G_A K) ≫ β_{A,N}(h.trans k) = T_{MN}.map β_{AM} ≫
  β_{MN}.app (T_{AM} K) ≫ G_N.map (a^X.hom.app K)`. Endpoints checked
  (T_MN T_AM G_A K → G_N T_AN K). Correct.
- "Only the unit and tower equations": no further conclusion (no integral equations,
  no common-stage claim). Correct.

Edge cases: A = M, M = N, A = M = N allowed (non-strict ≤; `le_rfl` in the unit clause);
Ω's universe free; empty schemes and zero objects unrestricted; no characteristic
restriction on K₀ beyond ℓ invertible.

Searches: the worker's leanfinder / loogle / grep searches recorded above, plus a
reading of `GeneralAlgebraicallyClosedCoefficients` (associator, unitor,
associator_cocycle) and `CompactSupportNormalizedScalarIsomorphisms`: no existing
statement of these two equations.

Records: the node differs from the base only by its `lean` record; `lean.statement` is
verbatim the file's signature; no line exceeds 100 characters; module and theorem
docstrings carry the source place, `(blueprint: …)` and all seven proof steps; the
proof is `sorry`.

Advisory: `Stage`, `transition`, `integralTransition`, `associator`, `unitor` are owned
by def-weil-algebraically-closed-coefficients, which is not in stmt_deps. They are forced
by the landed dependency's own interface (its b/β types use the same declarations
without that citation) and are thin wrappers of the cited sfRationalScalarExtension /
sfRationalScalarComp / sfRationalScalarUnit; stage-2 may not add a non-new stmt_dep (H2).

Changes: none to the Lean or the node; this section replaces the self-check.
