## Worker report

`Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` states the comparison of the
specified integral mapping-complex adjunction with actual reconstruction descent.
Its helper definitions contain real composites; all postponed proofs are named
`theorem`s with `sorry`. The item's statement is unchanged. The returned §1(B)
rebind has been withdrawn: the full live `prop-coef-integral-exceptional-adjoint`
node and its Lean record are untouched. The explicitly authorized review option
(b) is implemented by the new definition node described below.

Hypotheses, one by one:

- The global finite-field datum is `D : FiniteFieldDatum.{u}`. The coefficient data
  are `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`, `E`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. The recorded ring, uniformizer
  and quotient constructions are used transitively by the system calculus; its
  index `n : ℕ` denotes exponent `n+1`, so every positive finite level occurs.
- `X,Y : Scheme.{u}` have the recorded `.Over (Spec (.of D.k))` structures,
  separated, locally finite-type and quasi-compact structure morphisms. The last
  two properties together mean finite type. `f`, its `.IsOver` instance and the
  same three morphism properties render the separated finite-type k-morphism.
- `c : Compactification f` is the fixed open/proper factorization. No alternative
  compactification or finite-level choice is introduced.
- `SX,SY` are the recorded `CoefficientDerivedSystemCalculus`; `SZ` supplies the
  intermediate compactification scheme's calculus required by the realization.
  The small pro-etale sites and completed ring sheaves are those in the recorded
  modules, with scheme universe u, site object universe u+1 and morphism universe u.
- `r : FiniteAdjunctionDiagram.Realization ...` is the functorial normalized system
  realization. `domain` is normalization AND finite-Tor constructibility separately
  at each level. In particular it does not demand any common interval across levels.
  `g,s,βX,βY,a : Enriched r g s βX βY` express the specified enriched system map.
  `CX,CY` supply its recorded unit/counit and mapping-limit coherence.
- `sfIntegralConstructibleCategory` is exactly the completed bounded constructible
  category, not all complete objects. `Domains` supplies the preservation and
  actual reconstruction facts; the new definition node’s `exists_unique` theorem states existence of these
  proof data without imposing them as new geometric assumptions. `left` and `right`
  are literal L_Y F_f R_X and L_X E_f R_Y, including their morphism actions.
- `adj` with `IsSpecified r h a.iso adj` means precisely the adjunction whose Hom
  action is H-zero of lambda_X inverse after Rlim(Psi) after lambda_Y. The dependency
  theorem supplies and uniquely characterizes it. This is not an arbitrary adjunction.

Conclusions, one by one:

- For every `M`, `domain ... (SY.reduction.obj M.obj)` gives N in N_Y.
- `domain ... (r.G.obj ...).obj` gives E_f N in N_X.
- The following two `IsIso` clauses concern the actual `SX.adjunction.counit` at
  E_f N and `SY.adjunction.unit` at M. These are not replacement comparison maps.
- `kappa` applies L_Y to `r.F.map` of that actual counit, using explicitly named
  source/target full-subcategory objects. Its `IsIso` clause is explicit.
- `(adj.counit.app M).hom = descendedCounit r h M` is exactly epsilon_M equals
  kappa_M followed by L_Y(epsilon_sys_N), followed by inverse u_M. Lean's `≫`
  writes categorical composition in the order arrows are traversed.
- `descendedUnit` is actual u_X followed by L_X(system unit), followed by
  L_X E_f of inverse e_Y. Its equality with the specified unit is explicit.
- `descendedHom` composes full-inclusion Hom equivalences, the actual target unit,
  inverse reduction/limit Hom equivalence, actual system counit isomorphism,
  system adjunction, and source reduction/limit adjunction. It is defined before
  any finite evaluation and equals `adj.homEquiv` for all K,M.
- `descendedAdjunction` is constructed with `Adjunction.mkOfHomEquiv` from that
  composite, using the named naturality theorem. The final clauses assert equality
  of adjunctions and of their unit and counit natural transformations. Thus the
  comparison concerns specified natural integral maps, not merely finite reductions.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient constructions
  and `Padic.finite_coefficientExtensionRing` (through the recorded finite domain).
- Mathlib scheme conventions: `Scheme.Over`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `Compactification`; `Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization` and
  the existing `sfCompactSupportFiniteIntegralFunctor` used for the identification.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `coefficientSequenceLimit`, `coefficientSequenceGlobalHom`,
  `coefficientIntegralGlobalHom`, `coefficientIntegralHomEquiv`,
  `coefficientMappingLimit`, `CoefficientDerivedSystemCalculus.gamma`, and actual
  adjunction fields.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`, actual normalized quotient
  rings and transition/restriction conventions.
- `Sheaf.Paper.FiniteTorAmplitudeSites` and
  `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: finite-Tor/constructible
  predicates, as used by `FiniteExceptional.domain` and `FiniteAdjunctionDiagram.domain`.
- `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`:
  `Realization`, `Enriched`, `reducedConstructible`, the specified system adjunction.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: completed ring-sheaf
  conventions and `integralConstantToCompletionOfUniverses`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`: actual reconstruction,
  restricted equivalence and `PurReconstruction` transport formulas.
- `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction`, owned by the new
  `def-coef-specified-integral-mapping-adjunction`: `Domains`, `reductionX`,
  `reductionY`, `left`, `right`, `mappingMap`, `homMap`, `IsSpecified`, `exists_unique`.
  Both lambda and Psi are literal composites inside `mappingMap`; there is no
  reference to the projection theorem's `integralMappingLimitMap` and no duplicate
  declaration of the already recorded system `psi`. The inverse counits, unit
  postcomposition and gamma are imported from their actual notion owners.
  Proof-only `IntegralResidueTor` records the residue-Tor step.

Edge cases: the coefficient indexing starts with the residue quotient (n=0 means
exponent 1); there is no exponent-zero quotient. Identity f is admitted with any
fixed compactification, and the formulas reduce to triangle identities. Zero
objects satisfy every relevant interval. Empty X and empty Y are permitted: all
bounds remain per-object or per-level, and no positive dimension or nonempty
scheme is required. Full subcategories retain all ambient arrows. The only same-u
binders are the already recorded finite realization's size convention; no equality
of the small site's object and morphism universes is imposed.

Searches:

- msearch LeanFinder, "Integral exceptional adjunction counit obtained from normalized
  coefficient systems by reduction and derived inverse limit": eight unrelated
  scheme-normalization results, no match.
- msearch Loogle, `CategoryTheory.Adjunction.comp_counit_app`: the generic composite
  counit lemma, not the specified integral mapping-complex comparison.
- msearch LeanSearch, "Conjugation of an adjunction by an equivalence and its counit
  formula": generic `conjugateEquiv_counit`, adjunction transport and equivalence
  lemmas, no coefficient-system statement.
- msearch grep, `comp_counit_app|homEquiv_counit`, Mathlib CategoryTheory/Adjunction:
  generic Basic, Unique, Restrict, Mates declarations, no matching integral result.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `integralExceptionalDescended`, `IntegralExceptionalAdjunction`, and descended /
  adjunction terminology: no existing statement. Read the finite realization,
  reconstruction calculus, integral mapping-limit and upstream etale adjoint files.

The latest blueprint's `sec-six-functors-basics/sk-prop-int-brown/_section.md` and
section were read. The old detailed coefficient paragraph is absent there, as the
accepted node's proof_origin and review already record. This delivery follows that
accepted six-step comparison and does not change the unit's statement or route.
No STATEMENT-DISPUTED claim is made.

## Repair of immutable head 7cbbcce0ea44

H13: the return correctly observed that the old §1(B) rebind stated only the
mapping-adjunction clauses, while `prop-coef-integral-exceptional-adjoint` also
states duality, finite reduction, Tor bounds, coefficient unit/counit comparison
and dualizing specialization. I chose the return's explicit option (b). The
sandbox dependency-node copy is removed, so delivery leaves every byte of its
live record alone. In particular the existing citer
`lem-coef-dual-formula-scalar-transpose` retains its full formula dependency.
The mapping-adjunction interface now belongs to the new definition node, and
the item adds exactly that id to `stmt_deps`. No proposition clause is rebound
or dropped. The item's accepted comparison theorem and its signature are unchanged.

H2: `Domains.lambdaX`, `Domains.lambdaY` and both lambda factors in `mappingMap`
now directly spell out `coefficientIntegralGlobalHom.map (1,u_Q) ≫ S.gamma.hom`.
The public import of `IntegralMappingLimitProjections` is replaced with the recorded
calculus module. `integralMappingLimitMap` is absent from both delivered modules.
The middle Psi is also inlined, to reuse the recorded actual system construction
without declaring another `psi` in its namespace. All three factors have the same
endpoints as the returned, accepted mapping-complex formula.

## New nodes

`def-coef-specified-integral-mapping-adjunction` owns
`Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction`. It defines the domain
proof package, actual restricted functors and specified Hom normalization, and
states the auxiliary existence/uniqueness theorem explicitly permitted by review
option (b). Its source is the latest integral compact-support/adjoint sketch,
with the inherited detailed mapping-complex construction retained in the accepted
DAG proof; the latest sketch no longer prints those detailed coefficient paragraphs.
It does not assert the item's comparison with the descended adjunction.

Every clause of this new node is rendered as follows. The coefficient, scheme,
compactification, calculus, realization and enriched-map binders are the same as
listed above for the item; `_CX,_CY` are the coherence hypotheses of `exists_unique`.
`Domains.reductionX/reductionY` express reduction membership.
`Domains.left/right` express constructible preservation of the literal composites.
`Domains.unitX/unitY` concern every constructible input; `counitX/counitY` concern
every normalized finite-Tor system in the recorded domain. `lambdaX/lambdaY`
state invertibility of the displayed actual unit/gamma composites for all
constructible pairs. `reductionX/reductionY` restrict the existing reduction
functors; `left/right` lift the actual composites to the full constructible
subcategories using only those membership proofs. `mappingMap` is the literal
lambda_Y, Rlim(Psi), inverse lambda_X composite, including both inverse actual
counits in Psi. `homMap` applies degree-zero homology and the recorded Hom
identifications. `IsSpecified` equates this action with `adj.homEquiv` on every
input arrow. Finally `exists_unique` has exactly the displayed existential witness
`h`, natural compact-support identification, and unique specified adjunction;
the new node's last sentence records the exact quantifier order. It asserts
existence of proof data, not choice of an arbitrary map. No helper def has sorry.

Fresh actual searches for this new notion are recorded in its `mathlib_searches`
and in the sandbox `searches.jsonl`: LeanSearch's integral inverse-limit mapping
adjunction query returned eight generic derived/limit adjunctions; LeanFinder's
normalized coefficient-system query returned eight unrelated Dold–Kan maps;
Loogle's `CategoryTheory.Adjunction.mkOfHomEquiv` returned the generic constructor
and its three formula lemmas; Mathlib grep `mappingLimit|[Ii]ntegral.*[Aa]djunction`
in CategoryTheory returned zero hits. The project rg found only the recorded
system-Psi construction and the projection theorem's lambda helper. Neither is
the specified constructible integral adjunction interface. DAG rg found the item,
full exceptional proposition, system-map theorem and unrelated consumers, but no
interface definition. `blueprint_refs.py search 'mapping-complex adjunction'`
returned zero matches; `ancestor` returned `lem-coef-rational-operations`. The
new node records this ancestor and prepends this item to the inherited via route.
These results support a new definition owner, not a replacement for the full
exceptional-adjoint theorem.

## Second reading by NP

A second pass by this worker (the dispatched brief forbids another agent) read
the repaired item, the new definition node and both concrete files together.
The item's signature is identical to the returned signature accepted by L.
The extra definition's geometric binders match the item; the structure's ten
fields match its stated membership, preservation, actual-unit/counit and lambda
conditions. The two reduction functors and the left/right composites use the
existing calculus and full-subcategory lifts. The three factors of `mappingMap`
start at RHom_Y(FK,M), pass through Rlim H_Y(R_Y FK,R_Y M) and
Rlim H_X(R_X K,R_X GM), and end at RHom_X(K,GM). Contravariance of the
first argument accounts for the inverse e_B; the last factor uses inverse e_T.
`homMap` then has exactly the categorical Hom endpoints needed by `IsSpecified`.
`exists_unique` supplies those proof fields and a unique normalized adjunction,
with a natural identification of the actual left functor and integral compact
support. It carries no counit-descent conclusion.

For the item, kappa starts at L_Y F_f R_X L_X E_f R_Y M and ends at
L_Y F_f E_f R_Y M. `descendedCounit` follows with L_Y(epsilon_sys) and inverse
u_M to land at M. The actual unit has the dual direction. The independently
constructed `descendedHom` uses full-inclusion Hom equivalences, actual unit and
counit isomorphisms, the system adjunction and actual reduction/limit adjunctions.
Its naturality theorem is named and its proof postponed; `descendedAdjunction`
is real `Adjunction.mkOfHomEquiv` data. The final theorem compares all these
maps, all Hom bijections and the whole adjunction. Empty schemes, zero objects,
identity f and n=0 (positive exponent 1) still occur, with no added nonemptiness,
dimension, common Tor-bound or site-universe equality.

The second pass specifically checked both returned points: the full live
exceptional-adjoint record is no longer a delivery file, and no delivered Lean
identifier refers to `integralMappingLimitMap`. The new node is the sole owner
of its module and every docstring has its new blueprint id. This repairs the
returned ownership defects while preserving the accepted mathematical comparison.

Validation: both repaired modules compiled individually through `scompile.py`
with no errors or unexpected warnings (29.1 seconds for the interface and
6.5 seconds for the item). The repaired packet passed `deliver2.py --no-push`
(preflight and per-file compilation, dry-run commit 81f626382df). No global build
or direct repository/Git write was performed.
