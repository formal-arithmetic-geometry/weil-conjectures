## Worker report

`Sheaf.Paper.CompletedPullbackReduction` states
`AlgebraicGeometry.Scheme.completedPullback_reduction`. Its statement is unchanged
from the DAG. Every theorem proof is `sorry`; every definition has real data.
The canonical finite arrows, their representative normalizations, and their
coherence maps belong to this item's notion and are listed in `lean.declarations`.

The source read was the full item, its five detailed proof steps and blueprint
sketch, all three statement-dependency nodes and their recorded modules, and
[Stacks Tag 099N](https://stacks.math.columbia.edu/tag/099N), clauses (2) and (5),
with [Tag 099M](https://stacks.math.columbia.edu/tag/099M) for completion. The
blueprint Markdown path and local Stacks checkout are absent; the imported DAG
retains the blueprint statement and detailed proof. The theorem docstring gives
all five proof steps, including the Koszul tail calculation, identification of
the projection adjunct, and the transition and normalization cancellation.

Hypothesis-by-hypothesis correspondence:

- `g : X ⟶ Y` is the arbitrary scheme morphism T' → T. Both schemes have universe u.
- `A : Type (u + 1)` and `[CommRing A]` use the published coefficient size on the
  small site, whose object/Hom universes remain u+1/u. Smaller coefficient rings
  can be lifted to this size. The two site universes are never identified.
- `d : AdicCoefficientDatum A` carries the Noetherian ring, finitely generated
  ideal, torsion A/I, and perfect finite positive quotients. `reductionCoefficient`
  is the existing sheafification of continuous functions from connected components
  to A/I^(n+1). `pbcAdicCompletion` is the actual limit of these sheaves.
- `r`, `f : Fin r → A`, and `hf : Ideal.span (Set.range f) = d.ideal` supply exactly
  the chosen finite generators of I. The empty generator tuple is allowed.
- `K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))` is the unbounded
  derived object over the completed coefficient sheaf, with no ordinary-module
  derived-category identification.
- `C` and `e : DerivedCategory.Q.obj C ≅ K` expose an arbitrary representative
  required by the recorded intrinsic-completion interface. `_hK` is exactly
  `IsDerivedCompleteIntrinsic Y d r f hf K C e`, the invertibility of its specified
  (u,0) Koszul-fiber unit. No flatness or boundedness is required of C.
- K_n is `reductionDerivedChange Y (completedReductionProjection Y d n)` applied
  to K. Its finite coefficient action is retained. A natural number n represents
  the positive exponent n+1; this covers exactly all n ≥ 1 in the node.
- L is the already recorded `completedPullbackObject g d K`, the derived inverse
  limit of `completedTowerPullback g d` applied to `completedReductionTower Y d`.
  `completedPullbackFunctor` only exposes that existing construction on morphisms.
- `completedReductionFiniteModules` is the existing tensor-formula
  `proEtaleRingModulePullback` along `completedFiniteCoefficientMap`, using its
  recorded invertibility. `completedReductionFiniteDerived` is its exact derived
  functor. `completedReductionFiniteTarget` is consequently Lg_n^* K_n.

Clause-by-clause correspondence:

- The first conjunct asserts `IsDerivedCompleteIntrinsic` for L on every complex
  P and realization eP of L. This uses the recorded predicate directly and expresses
  intrinsic completeness independently of the chosen representative.
- The second conjunct asserts `IsIso (completedPullbackReductionArrow g d K n)`
  at every positive level. This arrow is the scalar-extension adjunct of the actual
  derived-limit projection followed by the canonically normalized finite evaluation
  comparison. It is therefore the node's projection-induced alpha_n.
- The third conjunct is naturality for every morphism v between complete objects.
  Arbitrary representatives C',e' expose completeness of K' in the recorded interface.
- The fourth conjunct asserts invertibility of the pulled tower's normalization and
  its quotient transition square. The square is written in the P_b coefficient
  category, before exact restriction to the completed coefficient ring. Restricting
  it is precisely the underlying completed-coefficient transition square.
- The fifth conjunct extends alpha_b along P_b → P_a and composes with the pulled
  tower's normalization, obtaining alpha_a after the canonical scalar associativity
  comparison. `completedPullbackSourceNormalization` uses the existing
  `pbcReductionNormalization`, fixed by the normalized scalar adjunctions.
- The sixth conjunct is the c ≥ b ≥ a quotient cocycle, using the same existing
  balancing comparison and `reductionCoefficientMap_comp`.
- The final conjunct identifies equal-index normalization with the canonical scalar
  unitor `completedReductionUnit`. That map uses identity-on-sections restriction
  and the normalized scalar adjunction counit; it is not an arbitrary automorphism.

The finite evaluation comparison is uniquely normalized on K-flat representatives
by the actual reduction and pullback counits. Its ordinary comparison is uniquely
fixed on inverse images of the strict quotient unit, including generators over
arbitrary arrows U → g*V. The finite quotient transition is independently fixed
on all inverse-image tensor generators; its derived descent is normalized by the
same universal counits. Thus no comparison is selected from a bare `Nonempty`,
and no transition or normalization is defined by conjugating through alpha.
Large normalization predicates are named to avoid repeatedly elaborating their
sectionwise formulas inside choice terms. `completedReductionFiniteGenerator`
is the same explicit generator, named once. `completedReductionSectionEquation`
states its literal section equality over abstract rings before specialization,
so the kernel need not unfold the concrete finite coefficient diagrams to compare
restricted and unrestricted section carriers. This preserves the full formulas.
The ordinary source's zero-preservation instance explicitly supplies the existing
additive structures before inheriting zero preservation for their composite.

Dependency declarations used:

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `reductionCoefficient`, `completedReductionCoefficient`,
  `completedReductionProjection`, `reductionCoefficientMap`,
  `reductionCoefficientMap_comp`, `completedReductionProjection_comp`,
  `reductionChange`, `reductionDerivedChange`, `reductionTensorSection`,
  `completedReductionModuleTowerFunctor`, and `completedReductionTower`.
- `Sheaf.Paper.CompletedTowerPullback`: `completedCoefficientMap`,
  `completedFiniteCoefficientMap`, `completedFiniteCoefficientMap_isIso`,
  `completedTowerModulePullback`, `completedTowerPullback`,
  `completedTowerPullbackComplexCounit`, `completedReductionModuleUnit`,
  `completedReductionTowerCounit`, `completedPullbackObject`, and
  `CategoryTheory.Functor.leftDerivedCounitOnComplex`.
- `Sheaf.Paper.IntrinsicCompletion`: `IsDerivedCompleteIntrinsic`.
- `Sheaf.Paper.BoundedConstructibleTower` (publicly imported by the dependencies):
  `pbcModules`, `pbcTowers`, `pbcAdicRings`, `pbcAdicCompletion`, `pbcTowerEvaluation`,
  `pbcRestrict`, `pbcDerivedRestrict`, `pbcComplexCounit`,
  `pbcDerivedScalarAdjunction`, and `pbcReductionNormalization`.
- `Sheaf.Paper.CompletedTowerDerivedLimitFunctor`: `completedTowerRlim`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations` and its inverse-image dependency:
  `proEtaleRingModulePullback`, its exactness instances, `proEtaleModuleInverseImage`,
  `proEtaleModelRingUnit`, and the small-site module transports.
- Mathlib/right-derived API: `Functor.rightDerivedFunctorNatTrans`,
  `rightDerivedFunctorIsoMapDerivedCategory`, `mapDerivedCategoryFactors`,
  and `Functor.mapDerivedCategoryNatIso`.

The earlier sandbox copied a competing dependency implementation. Current server
source was checked with `scompile.py --source Sheaf.Paper.CompletedTowerPullback`;
this delivery uses that landed module. The stale CompletedPullback module and the
two dependency-node overrides are excluded from the delivery. No dependency node
is changed, no new independent notion is introduced, and no statement correction
is needed.

Edge cases checked: empty schemes; zero coefficient ring and zero quotients; I=0
and the empty generator tuple; I=A; zero derived object; unbounded representatives;
positive exponent 1; equal a=b and b=c; identity and arbitrary scheme morphisms.
No nonzero, nonempty, proper, flat, or boundedness assumption is added.

Searches:

- `msearch.py leanfinder`, query "derived complete completed pullback finite
  coefficient reduction functorial isomorphism": eight generic sheaf pullback,
  scheme-cover, and shift-comparison hits, including
  `SheafOfModules.freeFunctorCompPullbackIso`; no completed reduction theorem.
- `msearch.py loogle`, query `"AdicCompletion"`: ordinary module-adic completion
  declarations; no derived completed sheaf-pullback reduction theorem.
- `msearch.py grep`, query `completedPullback|completed.pullback|Rlim.*tensor`:
  no Mathlib hits.
- `msearch.py leansearch`, query "Derived completion commutes with finite quotient
  reduction after pullback": eight ordinary adic-completion hits, including
  `AdicCompletion.map_val_apply` and `AdicCompletion.eval_comp_of`; no exact match.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and the upstream-name
  index for completed-pullback/reduction names and the item id found the recorded
  dependency's finite-evaluation assertion and downstream citations, but no theorem
  stating all of this item's completeness, invertibility and coherence clauses.
- The earlier attempt also searched all server delivery branches and read Q24's
  dependency source. Its superseded copy is not used now that the recorded Q31
  module is published.

No `STATEMENT-DISPUTED` issue remains.

Validation: the prescribed `scompile.py` passed on the current server sources,
compiling `Sheaf/Paper/CompletedPullbackReduction.lean` in 15.4 seconds under the
60-second limit, without errors or warnings. The local overlay initially lacked
a dependency artifact; the wrapper automatically confirmed against the server.
The item JSON differs from the repository only in `lean`; all 34 declarations
are recorded and the primary signature is copied verbatim.

## Second reading by N2

I independently read the repository node, its five proof steps, the sandbox Lean
module, all three statement-dependency node statements and signatures, and the
actual dependency sources. No statement mismatch was found and no Lean or node
change was necessary. This reading adds this report section only; it does not
rely on the worker's compilation or search conclusions.

Source check: the local literature checkout is absent. I fetched the upstream
`stacks/stacks-project` `proetale.tex` into the sandbox and read lines 4273–4384,
including `section-derived-completion-noetherian`, `lemma-naive-completion`
(Tag 099M), and `lemma-pushforward-Noetherian-case` (Tag 099N), not merely the
individual displayed claim. The section works over a Noetherian constant ring
and an ideal, and explicitly distinguishes its completed ring sheaf, explaining
the equivalence on derived-complete subcategories. Clauses (2) and (5) of 099N
identify completed pullback and its reduction-limit construction for any topos
morphism. No properness, flatness, nonemptiness, boundedness, or characteristic
assumption is implicit there. The node's additional finite/perfect/torsion datum
is explicitly inherited from its dependency. The blueprint file itself is absent;
I read the imported statement, detailed proof, and blueprint sketch in the node.
The online source pages are https://stacks.math.columbia.edu/tag/099N and
https://stacks.math.columbia.edu/tag/099M.

Objects and hypotheses, independently listed before the conclusion check:

- Arbitrary schemes T', T and a morphism g: rendered by `{X Y : Scheme.{u}}`
  and `(g : X ⟶ Y)`. Verdict: exact; no geometric property is required of g.
- Noetherian commutative ring A and the adic datum I with finite perfect positive
  quotients and torsion A/I: `{A : Type (u + 1)} [CommRing A]` and
  `(d : AdicCoefficientDatum A)`. I opened `CompletedAdicCoefficientDatum` and
  `CompleteCoefficientDatum`: the former extends the latter by `quotientFinite`;
  the inherited structure supplies Noetherianity, finite generation, torsion and
  perfectness. Verdict: the dependency's exact datum, not a field or DVR special case.
- A finite generating tuple for I: `(r : ℕ) (f : Fin r → A)` with
  `hf : Ideal.span (Set.range f) = d.ideal`. Verdict: exposes the generators used
  by the recorded intrinsic predicate, without strengthening finite generation.
- Quotient sheaves and their completed limit: `reductionCoefficient T d n`,
  `completedReductionProjection T d n`, and `pbcAdicCompletion T d`. I opened
  `AdicCoefficientDatum` and `BoundedConstructibleTower`; both presentations
  reuse the identical `AdicCoefficients.ringSystem`, its actual limit, and its
  projections. Verdict: the node's sheafified continuous component functions and
  completed coefficient ring, not constant A coefficients.
- K in the unbounded completed-coefficient derived category: `K : DerivedCategory
  (pbcModules Y (pbcAdicCompletion Y d))`. `pbcModules` is precisely the recorded
  category of left module sheaves. Verdict: exact, with no ordinary-module or
  constant-coefficient identification.
- Intrinsic completeness of K: arbitrary `C`, realization `e`, and
  `_hK : IsDerivedCompleteIntrinsic Y d r f hf K C e`. I opened
  `IntrinsicCompletion`: this predicate is invertibility of the transported
  published Koszul-fiber `(u,0)` unit, via identity-on-sections coefficient
  round trips. Verdict: the dependency predicate itself; no K-flat or bounded
  hypothesis is imposed on C.
- K_n: `reductionDerivedChange Y (completedReductionProjection Y d n)`. Verdict:
  extension to the finite quotient coefficient category, with its action retained.
- L: `completedPullbackObject g d K`. I opened `CompletedTowerPullback`, including
  the coefficient map, derived levelwise tower functor, and the object's definition.
  Verdict: precisely Rlim of the pulled strict reduction tower, with no assumption
  that the completed coefficient structure map is invertible.
- Finite pullback g_n*: `completedReductionFiniteModules` is an alias for the
  existing tensor-formula `proEtaleRingModulePullback` along
  `completedFiniteCoefficientMap`; `completedReductionFiniteDerived` is the
  existing exact `proEtaleRingDerivedPullback`. I read `ProEtaleOperations`,
  including its coefficient-isomorphism input and exactness instances. Verdict:
  these assumptions are furnished canonically at finite level by the dependency,
  not added as hypotheses to the completed structure map.

Conclusion, clause by clause:

- L is intrinsically complete: the first conjunct asserts the recorded
  `IsDerivedCompleteIntrinsic X d r f hf` for every representative P and realization
  eP of L. Verdict: intrinsic completeness, independent of representative.
- Every positive reduction has the projection-induced alpha_n: the second conjunct
  is `∀ n : ℕ, IsIso (completedPullbackReductionArrow g d K n)`. I traced that
  definition through `completedReductionLimitProjection`: the latter is the right
  derivation of the actual `lim.π`, followed by the exact evaluation factorization.
  Its composite with the finite evaluation comparison is sent through the fixed
  scalar-extension adjunction. Verdict: exactly the specified projection adjunct,
  in the finite coefficient derived category, not existence of some isomorphism.
- Functoriality: the third conjunct is the commuting square for every v : K ⟶ K'
  between complete inputs, using `completedPullbackFunctor.map` and
  `completedReductionFiniteTarget.map`. The former's object map is definitionally
  `completedPullbackObject`. Verdict: exact; invertibility gives natural inverses too.
- Quotient transition compatibility: the fourth conjunct writes the square in the
  P_b coefficient category using the adjunct of source normalization and the actual
  target quotient transition. Verdict: this is the quotient transition square
  before the exact restriction to completed coefficients, and retains all actions.
  Its `IsIso` clause expresses the normalization isomorphisms referred to by the node.
- Normalization compatibility for b ≥ a ≥ 1: the fifth conjunct extends alpha_b,
  then applies `completedReductionTargetNormalization`, and equates this with
  `completedPullbackSourceNormalization.hom` followed by alpha_a. Verdict: correct
  order, source, target, and canonical scalar associativity map.
- Three-level quotient cocycle: the sixth conjunct compares successive target
  normalizations with `completedReductionQuotientAssoc.hom` followed by the direct
  normalization. I opened `pbcReductionNormalization` and its normalized scalar
  adjunction in `BoundedConstructibleTower`. Verdict: the actual canonical balancing
  comparison, at all c ≥ b ≥ a, with no strict-inequality restriction.
- Equal-index unit: the final conjunct identifies target normalization with
  `completedReductionUnit`. Its restriction comparison is uniquely identity on
  every section, and its scalar unitor uses the fixed adjunction counit. Verdict:
  canonical unit identity, not an arbitrary chosen endomorphism.

Canonical helper check (H4/H5): the six postponed helper theorems have `sorry`
proofs and proof docstrings; they provide proof data or uniquely characterized
maps belonging to this node's finite-arrow construction. The ordinary comparison
is fixed on tensors of inverse-image quotient-unit generators for every U→g*V;
those generate after sheafification. The ordinary transition is fixed on all
finite tensor generators, including both quotient coefficients. Their derived
descents are fixed by equations with the actual universal counits on every K-flat
representative. Thus the uses of choice are of uniquely normalized constructions,
not choices from an unconstrained existence theorem or bare `Nonempty`. In
particular, the dependency's existing `completedPullback_reductionEvaluation`
only asserts `Nonempty` of a natural isomorphism; it cannot by itself define the
canonical projection arrow. The helper retains that same comparison with the
necessary representative characterization; it does not introduce a competing
notion. Neither target transitions nor normalizations are defined by conjugation
through alpha. No new DAG node or dependency-module override is delivered.

Edge cases: r=0 and I=0 are admitted by `Fin 0` and the span equality; no nonempty
index hypothesis is introduced. The quotient tower itself is the nonempty set of
positive levels reindexed by ℕ. Lean n=0 is exponent 1; exponent 0 is not an
original node case. Zero K, the zero ring, zero quotients, I=A, and empty schemes
are admitted. Both identity and arbitrary g are included. All inequalities allow
equality, including a=b=c. No characteristic condition is added. No boundedness,
flatness, constructibility or finite generation of K is assumed. Universes are
explicitly bound, following the dependency's coefficient size u+1 and the small
site object/Hom sizes u+1/u; no equality of those two site universes is imposed.

Independent searches:

- `msearch.py ... leanfinder`, query “A derived complete sheaf complex pulled back
  and completed has canonical finite quotient reductions with coherent scalar
  extension”: eight generic condensed/sheaf-module hits, including
  `LightCondensed.instIsGrothendieckAbelianLightCondMod` and
  `SheafOfModules.IsFinitePresentation`; none states this theorem.
- `msearch.py ... loogle`, query `"IsAdicComplete"`: twelve ordinary module-adic
  completeness hits. I checked the returned signature: it is a predicate on an
  ordinary R-module, not this derived sheaf construction.
- Independent `rg` searches for reduction/completion in both orders, adic pullback
  in both orders, and the exact new declaration names in Mathlib, slopmaster2
  `WeilConjectures`, project `lean/Sheaf`, and the shared upstream framework
  `lean/WeilConjectures`, plus `dag/lean_names_upstream.json`. The nearby upstream
  `CategoryTheory/DerivedCategory/Complete/Defs` concerns constant-coefficient
  `Sheaf J (ModuleCat R)` and does not state this completed-ring finite pullback
  theorem or its coherence clauses. The project's dependency evaluation theorem
  is the incomplete comparison interface discussed above. No exact existing
  statement or competing canonical helper was found.

H6/H8/H9 and record checks: all seven theorem bodies are exactly `by sorry`;
there is no proof filled, hollow definition, private construction, local notation
or local instance. Each declaration has source/blueprint documentation. The main
proof docstring contains all five DAG steps: strict coefficient comparison,
Koszul-reflector completeness, finite-tail calculation and product triangle,
projection-adjunct cancellation, and transition/normalization coherence. Proof
imports are present. Every line is within 100 characters; variables and the
universe are bound explicitly. The 34 declarations are listed in `lean.declarations`.
A mechanical comparison confirms `lean.statement` equals the file's theorem
signature verbatim, and the node differs from the repository only in `lean`.
No statement correction is present or needed, so no citer audit is required.

Additional independent LeanSearch query: “The canonical map from derived completed
pullback tensored with each finite adic quotient to pullback of that quotient is
an isomorphism” returned eight ordinary `AdicCompletion` hits, including
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply` and
`AdicCompletion.ofTensorProduct_surjective_of_finite`; none is a derived sheaf
pullback statement.

Second-reader validation: the prescribed `scompile.py` completed successfully
on the unchanged sandbox module and its library-module check, without errors or
warnings (55.9 s and 31.4 s, respectively). The prescribed `deliver2.py --no-push`
then printed `OK (dry run)` for commit `7a4c094ade`: the complete packet compiles
and passes preflight, including this second reading. The delivered changes of
this reading are this report only; the worker's Lean and node signature stand.
