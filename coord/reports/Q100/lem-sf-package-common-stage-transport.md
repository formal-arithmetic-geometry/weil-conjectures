## Worker report

`Sheaf.Paper.SfPackageCommonStageTransport` states
`WeilConjectures.sfPackageCommonStageTransport`. Its only postponed proof is the
named theorem realizing this item. There are no new definitions, private notions,
extra theorem assumptions about scalar faithfulness, or data chosen from a bare
existence assertion. The theorem docstring contains all six steps of the DAG proof.
The item's statement, statement dependencies and proof are unchanged.

The current source was read at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.md`
and its proof, clause (1). This is an auxiliary assembly node, not the unit's own
statement; the literal raw and pair presentations are exactly those specified by
this node and its coefficient-category comparison dependency. I also read the
node's six proof steps and its stage-1 review, which explicitly requires keeping
the SF and PBC presentations distinct and assumes no coefficient linearity of Phi.

Hypotheses, clause by clause:

- `D : FiniteFieldDatum.{u}` fixes p,a,q,k0,k and the algebraic closure of the finite
  field. `C : D.CoefficientDatum` supplies the coefficient prime, its primality and
  `C.different : C.l ≠ D.p`. The binders `E₀`, its field/algebra/finite-dimensional
  instances, `n`, `hn`, and `_operations : SixFunctorOperationDatum D C E₀ n hn`
  spell out the parameters of the source's fixed operation datum. E₀ is only that
  datum's indexing coefficient field, not a restriction on the varying stages E.
- `Ω : Type w` with field, Padic-algebra and `IsAlgClosure` structures is the fixed
  algebraic closure of Q_l. The site universe u and closure universe w are independent.
  The operation datum's auxiliary closure C.Qbar imposes no equality on Ω.
- `T S : SixFunctorSpace D` means schemes over k with locally finite-type and
  quasi-compact structure maps; the two `IsSeparated` instances give separatedness.
  Their schemes are `T.obj.left` and `S.obj.left`. No scheme morphism is an input to
  this general family-descent assertion, so there is no further morphism condition
  to encode.
- The Noetherian instances and the four `Fact` binders dT,iT,dS,iS expose exactly
  the comparison/PBC interfaces' geometric hypotheses. They are consequences of
  finite type over the field k and l≠p: finite type over a field is Noetherian of
  finite Krull dimension, and l is a unit in k and every stalk. They add no
  mathematical restriction to the stated source domain. The dimension bound is
  existential and includes dimension zero and the empty scheme.
- `JT JS : FdCoefficientComparison ...` are the specified comparison equivalences,
  not arbitrary maps between unrelated categories. Their `stage`, `family`,
  `finite_functor`, `scalar_shift`, `equivalence`, `pair_functor`, `pair_exact`, and
  `pair_inverse_exact` fields record the finite/raw and common-stage comparisons,
  the j isomorphisms, their tower equations, shifts and triangulation. These are
  the coefficient components supplied by `rationalCoefficientCategoryComparison`.
- `F : StageSystem.CoherentExactMorphism` is the family Phi_E on the two prescribed
  SF stage systems. `base.Φ` is Phi_E; `base.β` has the displayed beta direction;
  `base.coh` is the associator equation; `commShift`, `betaCommShift`, `triangulated`
  and `additive` give exactness and the shift equations. The identity equation is
  forced by coherence at repeated stages and invertibility, using the specified
  unitor/associator normalizations; no extra strictness or linearity is assumed.

Conclusions, clause by clause:

- `StageSystem.Morphism.DescentSpec F.base` asserts exactness of the actual
  `F.base.functor` and its representative formula. This is the upstream literal
  construction, whose `obj` is definitionally `(E,(F.base.Φ E).obj K)` and whose map
  is the quotient map defined in `StageSystem.Morphism.functor`. The second clause
  of DescentSpec gives `mkHom M ... (beta.hom ≫ Phi_M.map u ≫ beta.inv)`, in Lean's
  left-to-right composition convention. `ExactDescent` includes additivity and a
  coherent integer shift structure under which this functor is triangulated.
- The remaining DescentSpec clauses quantify over ALL compatible transformation
  families `Morphism.Hom`, give their finite component formula, descend every
  componentwise equation, and preserve identities and vertical composition.
  Thus no compatibility hypothesis or equation-descent clause is omitted.
- `HT` is a family of equivalences with `(HT E).functor = JT.family.Φ E`.
  This presents the already given J_T,E in the literal stage types, together with
  its inverse, unit and counit. It is an existential conclusion, not an extra
  hypothesis. Inverse-equivalence choices are allowed here exactly as in step 2
  of the node's proof. The forward functor equality fixes them up to the canonical
  unit/counit isomorphism. This avoids repeatedly converting the small-field
  presentations `Coefficient` and `pbcFiniteField` during signature elaboration.
- The existential exact PBC family G has the precise finite functor equality
  `G.base.Φ E = (HT E).inverse ⋙ F.base.Φ E ⋙ JS.family.Φ E`.
  This is J_S,E Phi_E J_T,E inverse in the paper's composition order.
- G's scalar comparisons are specified by the compatible family
  `τ : Hom (JT.family.comp G.base) (F.base.comp JS.family)`. Its `comm` field is
  the mixed scalar square. The components are isomorphisms, and the `HEq` formula
  fixes each component to `J_S,E.map (Phi_E.map (HT E).unitIso.inv.app K)`.
  The HEq only accommodates the object equalities in the preceding functor
  specification; it compares actual morphisms, with no arbitrary component.
  Expanding Hom.comm and Morphism.comp.beta gives precisely the j_S inverse,
  beta, inverse h_T composite in node proof step 3. Since J_T,E is an equivalence,
  the square with this fixed inverse-unit component determines every G beta
  uniquely, including equal fields. This is an equivalent canonical
  characterization of the induced scalar comparisons, not a bare arbitrary
  scalar-compatible family.
- `DescentSpec G.base` is the PBC descent on the actual PBC scalar systems and pair
  categories. The displayed `Nonempty` natural isomorphism relates
  `F.base.functor ⋙ JS.equivalence.functor` to
  `JT.equivalence.functor ⋙ G.base.functor`; this is exactly the requested natural
  comparison under J_T,J_S. This is an existence assertion in a theorem, not a
  definition selecting unnormalized data.
- The last two conjuncts assert `IsTriangulated`, `IsIdempotentComplete`, and exact
  `GeneralAlgebraicallyClosedCoefficients.inclusion E` for each of T and S.
  These use the existing raw pair type and its existing shift and common-stage
  distinguished triangles. No Karoubi envelope or replacement structure is used.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`,
  and its publicly imported `SixFunctorSpace` definition.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory`, underlying the SF stage type.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `Stage`, `stageSystem`, `Pair`, `inclusion`, the shift and pretriangulated
  instances, and `generalAlgebraicallyClosedConstructibleCategory`.
- `Sheaf.Paper.PbcRationalCategory`:
  `AlgebraicGeometry.Scheme.PbcRationalDerivedCategory`, used through `pbcStageCategory`.
- `Sheaf.Paper.PbcQbarCategory`: `AlgebraicGeometry.Scheme.pbcQbarCategory` and its
  canonical scalar and triangulated instances; the item imports the PBC module directly.
- `Sheaf.Paper.RationalCoefficientCategoryComparison`:
  `rationalCoefficientCategoryComparison`; its public interface
  `FdCoefficientComparison` and the fields listed above were read in full.
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension`; the normalized
  transition and associator data used by `pbcScalarSystem`.
- `Sheaf.Paper.PbcDescentFunctors`: `StageSystem.Morphism.ExactDescent`,
  `StageSystem.Morphism.DescentSpec`, and `pbcDescentFunctors`. Its public
  `PbcDescentInterfaces` import supplies `StageSystem.CoherentExactMorphism`.
- `WeilConjectures.CategoryTheory.StageSystem.Functor`: the existing
  `Morphism`, `Morphism.functor`, `Morphism.Hom`, `descNatTrans`, their object,
  representative, identity and composition specifications. These were read in full.
- Proof imports: `Sheaf.Paper.PbcIdempotentCompleteTriangulation`,
  `AlgebraicGeometry.Scheme.pbcIdempotentCompleteTriangulation`;
  `WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer`,
  `CategoryTheory.triangulatedEquivalenceTransfer`.
- Mathlib's `Pretriangulated`, `IsTriangulated`, `Functor.IsTriangulated` and
  `IsIdempotentComplete` are the genuine category/functor predicates. Their full
  signatures and class fields were inspected in the recorded Mathlib sources.

Edge cases checked before writing: E=F=M (no strict inclusion assumption); arbitrary
common overfields and repeated fields; zero objects and zero arrows; empty schemes;
identity functors and identity/zero/composite transformations; F families that are
additive and exact but are not E-linear. The finite-stage index is the fixed directed
set of ALL finite intermediate fields, hence contains Q_l. Universes u and w remain
independent, and the canonical shrink models retain all finite subfields. Neither
full faithfulness of scalar transitions nor scalar linearity of F is added.

Searches performed using the prescribed msearch.py wrapper (raw results are also in
searches.jsonl):

- leanfinder: "Transport scalar-compatible exact functors between common finite
  coefficient stage categories along coherent equivalences": 8 hits, generic exact
  functors and Ext scalar compatibility; no matching assembly theorem.
- loogle: "CategoryTheory.IsIdempotentComplete": 12 hits, including the genuine
  predicate and equivalence transfer; none states the common-stage descent theorem.
- grep, Mathlib CategoryTheory: "common.?stage|coefficient.*descent": 0 hits.
- leansearch: "Exact descent of scalar compatible functors on common finite
  coefficient stage categories": 8 hits (exact functors, pseudofunctor descent,
  scalar restriction); no coefficient-category assembly match.
- rg on project Sheaf and upstream WeilConjectures sources for the item id,
  `sfPackageCommonStageTransport`, and common-stage transport found no existing
  theorem. Concept searches found the reusable StageSystem functor construction,
  FdCommonStageComparisonDescent, and CoefficientDualModelTransport; the latter two
  address coefficient-comparison and duality, not the present assertion.
- The explicitly requested grep for the item id under WeilConjectures returned
  no match. DAG searches found the item and its existing dependencies, with no
  separate definition needed for the inverse-unit scalar square.

No statement dispute or statement correction is needed. The only node fault found
is the unusable Qbar dependency binding addressed by the lean-only repair below.

Validation: scompile.py compiled the module both as a sandbox probe (7.9 s) and
at its delivered library module path (6.5 s), clean under the default 60-second
limit and default heartbeat budget. No diagnostic commands remain in the module.

## Dependency check

The item imports `Sheaf.Paper.PbcQbarCategory` directly for the PBC pair category and its
scalar, linear and triangulated declarations. The recorded dependency module
`Sheaf.Paper.IntrinsicQbarCategory` publicly imports that module, so no dependency-node
repair is needed or included. The dependency JSON is intentionally absent from this
delivery; the live dependency record is unchanged. This follows the maintainer return
for Q89 (H13), which requires restoring that landed record rather than rebinding it.

## Second reading by Q100

(Written by the maintainer's stage-2 reviewer NT-cc; the delivered section was a
self-reread by the worker, kept in substance in the worker report above.)

Node clauses against `WeilConjectures.sfPackageCommonStageTransport`:

- k = F̄_q, ℓ ≠ p, fixed operation datum: `D : FiniteFieldDatum.{u}`, `C : D.CoefficientDatum`
  (C.different), `_operations : SixFunctorOperationDatum D C E₀ n hn`. Matches.
- T, S separated of finite type over k: `SixFunctorSpace D` (locally finite type ∧ quasi-compact
  over Spec k) + `IsSeparated`. The `IsNoetherian`/dimension/ℓ-unit `Fact`s are consequences
  (finite type over a field; ℓ invertible in char p); the dimension bound is existential, so the
  empty scheme is covered. No restriction. Matches.
- Ω = Q̄_ℓ: `Ω : Type w`, field, `IsAlgClosure (Padic C.l) Ω`, universe independent of u. Matches.
- C_E(W) = raw rationalization: `GeneralAlgebraicallyClosedCoefficients.Stage` =
  `sfRationalConstructibleCategory l (Coefficient E) W` (record of def-weil-rationalization-karoubi);
  C_W = `generalAlgebraicallyClosedConstructibleCategory` (record of
  def-weil-algebraically-closed-coefficients), the literal pair category with common-stage shift
  and the ∃!-specified common-stage triangulation (`distinguished_iff`). Matches.
- P_E(W), P_W and their scalar systems: `pbcStageCategory`, `pbcScalarSystem`, and the target
  `pbcQbarCategory` of `FdCoefficientComparison.equivalence`. These are the PBC objects, kept
  distinct from the SF ones. Matches.
- J_{W,E}, J_W, j: `JT JS : FdCoefficientComparison`, fields `family` (Morphism, its `β` = j with
  the coherence equation), `finite_functor` (= the exact stage equivalences), `scalar_shift`,
  `equivalence` with `pair_functor : equivalence.functor = family.functor`. lem-fd is an ∃
  theorem, so quantifying over all comparison structures is the right reading. Matches.
- Φ_E exact with β_{F/E} : T^S Φ_E ≅ Φ_F T^T, identity/associator/shift equations:
  `F : StageSystem.CoherentExactMorphism` (β h : Φ_i ⋙ T' h ≅ T h ⋙ Φ_j, `coh`, `additive`,
  `triangulated`, `commShift`, `betaCommShift`). The unit equation follows from `coh` at repeated
  stages for invertible β. Matches the upstream interface of prop-weil-pbc-descent-functors.
- Exact Φ with (E,K) ↦ (E,Φ_E K) and [M,u] ↦ β_{M/F}^{-1} Φ_M(u) β_{M/E}: `DescentSpec F.base`,
  where `ExactDescent` gives exactness and the representative clause is
  `(F.β hK).hom.app ≫ (F.Φ M).map u ≫ (F.β hL).inv.app` (diagrammatic order, same composite).
  Matches.
- Compatible transformations and equations descend: the remaining `DescentSpec` clauses cover
  ALL `Morphism.Hom` between any two families (component formula, equation descent, id, comp).
  Matches; slightly more general.
- Comparison with the descent of J_{S,E}Φ_E J_{T,E}^{-1}: ∃ HT (functor = JT.family.Φ E),
  ∃ G CoherentExactMorphism on the PBC systems with `G.base.Φ E = HT.inverse ⋙ Φ_E ⋙ J_{S,E}`,
  and scalar comparisons pinned through τ : Hom (JT.family.comp G.base) (F.base.comp JS.family)
  with components J_S Φ_E(η⁻¹_K). Since τ and j are invertible and J_{T,E} is essentially
  surjective, the `comm` square fixes G.β uniquely; this is the step-3 composite. Then
  `DescentSpec G.base` and `Nonempty (F.base.functor ⋙ JS.equivalence.functor ≅
  JT.equivalence.functor ⋙ G.base.functor)` — the node says "naturally isomorphic". Matches.
- Idempotent-complete triangulated literal C_W, exact finite-stage embeddings, no Karoubi
  envelope: `IsTriangulated`, `IsIdempotentComplete`, `(inclusion E).IsTriangulated` for T and
  S, on the literal pair category with its own instances. Matches.

Edge cases: E = F = M and repeated fields (h = le_refl), zero objects, empty schemes,
identity families and transformations, non-linear Φ_E (no linearity assumed), independent
universes u and w. All covered.

Gates: no definitions in the module; one theorem with `sorry` only; module and theorem
docstrings carry the source place and `(blueprint: lem-sf-package-common-stage-transport)`;
the theorem docstring carries all six proof steps; `lean.statement` is verbatim the file
signature. Only the item node changed versus the live DAG; no dependency record is delivered.

Advisories for the maintainer: the statement uses `CoherentExactMorphism`
(def-weil-pbc-descent-interfaces), `DescentSpec` (declared by theorem node
prop-weil-pbc-descent-functors) and `pbcScalarSystem` (FiniteStagePairCategory); these owners
are not in stmt_deps, which a stage-2 fix cannot change. The live record of
def-weil-pbc-qbar-category, `intrinsicPbcQbarCategory`, is an abbrev of the SF category
`generalAlgebraicallyClosedConstructibleCategory`, not P_W. The item does not use it; it takes P_W
from lem-fd's `FdCoefficientComparison.equivalence` (`pbcQbarCategory`).

## Current repair status, 2026-10-24

Following the Q89 maintainer return (H13), I removed the dependency-node copy from this
packet and restored the item note so the landed `def-weil-pbc-qbar-category` record is
unchanged. Its `Sheaf.Paper.IntrinsicQbarCategory` module publicly imports
`Sheaf.Paper.PbcQbarCategory`; the item module directly imports and uses
`AlgebraicGeometry.Scheme.pbcQbarCategory` and its existing declarations. The previous
lean-only rebinding was therefore unnecessary and triggered the validator's pre-existing
cycle check. No statement, dependency edge, or source module was changed.
