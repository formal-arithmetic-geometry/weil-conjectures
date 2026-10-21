## Worker report

The delivery states `CategoryTheory.AdicSites.PerfectQuotientExchange.perfectQuotientExchangeNormalization`
in `Sheaf.Paper.PerfectQuotientExchangeNormalization`. Its only postponed proof is the
item's theorem. The auxiliary declarations are transparent aliases, actual comparison
maps, and normalized presentation records for the canonical constructions in this item.
No mathematical object is selected from an unconstrained existence theorem.

The node's statement and Lean module are unchanged from the returned delivery
(e69a32791471). The statement dependencies now name the new definition node
`def-pur-adic-site-strict-quotient-interface`, plus the already published perfectness
predicate and exact quotient evaluation. The new node records the existing small-site
interface; there are no dependency-module repairs.

The theorem concludes existence of a normalized realization of the specified operations;
these realization records are not hypotheses. Ordinary quotient inverse image is fixed by
its evaluations and its comparison with the actual inverse image of the underlying strict
A-tower. Thus the coefficient restrictions and every transition are those of the published
quotient ring sheaf. The ordinary adjunction Hom equivalence is fixed at each coefficient
level by the Hom-equivalence clause of `PresentationNormalized`. Its derived adjunction is constructed by
`Adjunction.mapDerivedCategoryRightDerivedAdjunction`, not chosen independently.
Derived reduction/pullback and restriction/pullback comparisons are fixed on whole cochain
representatives. They are not specified only by equations after derived evaluation.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative Noetherian A and ideal I | `(A : Type u) [CommRing A] (I : Ideal A)` and `[IsNoetherianRing A]`. |
| Small presenting sites and a geometric morphism u | `Y X : AdicSites.Site.{u}`, `f : AdicSites.Morphism Y X`. `Site.objects : Type u` and `SmallCategory` put objects and arrows in the module bound. `Morphism` stores the geometric adjunction, finite-limit-preserving inverse image and its algebraic operation lift. |
| A_n = A/I^n for all n ≥ 1 | `quotientRing A I n = A ⧸ I^(n+1)`; `n : ℕ` enumerates exactly the positive exponents. |
| Ordinary unbounded module derived categories, u* ⊣ P | `Site.modules`, `Site.derived`, `f.pull A`, `f.push A`, and `f.adj A`. The adjunction is derived from the fixed ordinary module adjunction. |
| Completion reflector, full complete subcategory and fixed unit | `Site.completion`, `Site.IsComplete`, `Site.Complete`, and `Site.unit`, inherited from `ConstantCompletion`. No new completion or unit is defined. The completed adjunction is the one already supplied by the dependencies; no completeness assumption is imposed on the input. |
| Strict diagram site, ΔA, B and actual quotient transitions | `StrictQuotientDiagonalPresentation` for `atY` and `atX`, using `strictDiagonalRing` and `strictQuotientRing`; the latter is `systemSequenceRing (finiteSystem ...)`. |
| U, S and R = SΔ | `atY.restrictionD`, `extend atY.ringMap`, `atY.reductionD`, and their X versions. `reduction0` is the same construction before localization. |
| Quotient augmentation and L U R = C | The existing quotient augmentations and completion units are retained. `ReductionNormalized`'s third clause fixes the comparison on a full K-flat complex by the existing `d.representative`, which retains the actual quotient insertion. `tower` followed by the existing Rlim identifies the result with the existing completion. |
| Derived termwise G and P^J | `f.towerPull A`, `f.towerPush A`, `f.towerAdjunction A`. |
| G_B ⊣ P_B induced from the module adjunction | `Presentation.pull`, `push`, `adjunction`, the levelwise Hom-equivalence clause of `PresentationNormalized`, and `Presentation.derivedAdjunction`. `P_B` is `push.rightDerivedFunctor`. |
| Each quotient is represented by bounded finite projectives | `hperfect : AdicSites.PerfectQuotients A I`, whose body is `DerivedCategory.IsPerfectRingComplex` of the quotient in degree zero, for every n. This predicate explicitly gives a bounded cochain complex with every term `Module.Projective` and `Module.Finite`. |
| h is the mate of scalar extension of Δε | `exchange p`, formed by `mateEquiv (f.adj A) p.derivedAdjunction` from `p.reduction.hom`. `PresentationNormalized`'s K-flat reduction clause fixes this comparison on the whole ordinary tensor/pullback cochain map. |
| h^A is the strict augmented projection mate using χ | `strictExchange p` is the equivalent counit-transpose construction, transported by the representative-normalized `tower` comparisons. Its central mate is exactly the existing `f.reductionPullIso` followed by reduction of the ordinary derived counit. This is the equivalent-transpose clause of `augmentedDiagramProjectionMate`; the fixed constant-tower counit equation supplies its χ identification. |
| d is the specified derived-composition comparison | The theorem supplies `d : P_B ⋙ U_Y ≅ U_X ⋙ P^J` and `d.hom = restrictionMate p`. `restrictionMate` is the right adjunction mate of the exact scalar-restriction/inverse-image comparison. The canonical adjunctions fix this comparison uniquely; this is the adjunction characterization of the common-composite comparison in Tags 07A6/0D6E and the coefficient-restriction counit lemma. |
| d U_Y(h_F) = h^A_F before evaluation | First universally quantified displayed equality, `atY.restrictionD.map ((exchange p).app F) ≫ d.hom.app ... = (strictExchange p).app F`. |
| Quotient-linear evaluation h_{F,n} with the specified endpoints | `finiteExchange p n` applies exact quotient evaluation to `exchange`, with `reductionY.finite`, `pushEvaluationD`, and `reductionX.finite` at the endpoints. Its type is `P ⋙ finiteReduction_Y ⟶ finiteReduction_X ⋙ push_(A/I^(n+1))`. |
| Evaluated h is the quotient counit-defined projection | `(finiteExchange p n).app F = f.finiteProjection A I n F`. The existing `finiteProjection` is explicitly the adjunct of `finitePullIso.inv` followed by scalar extension of the ambient counit. |
| Restriction to A is evaluation of h^A and the ordinary projection | The second finite equation evaluates `strictExchange`, inserts the existing `evaluatePushIso`, `finiteEvaluationIso`, and `finiteRestrictionPushIso`, and equals `finiteRestriction.map (finiteExchange ...)`, with all endpoint comparisons written. Together with the preceding equality, this is the claimed coefficient-restriction normalization. |
| h and all h_n are natural isomorphisms | `IsIso (exchange p)` and `∀ n, IsIso (finiteExchange p n)`. These are natural transformations before their components are evaluated. |
| ρ = a inverse after L(h^A), through L U R = C | `completionExchange p F`: the inverse source `tower` comparison, `Rlim_Y.map (strictExchange ...)`, `(f.directLimitIso A).inv`, and P of the target `tower` comparison. |
| ρη_Y = Pη_X | `(Y.unit A I).app ((f.push A).obj F) ≫ completionExchange p F = (f.push A).map ((X.unit A I).app F)`. Lean's composition reads left to right. |
| No finite-cardinality, flatness, scheme or complete-input restriction | No such binder occurs. F ranges over all `X.derived A`. |

Dependency APIs read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-finiteness meaning.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `Q`.
- `Sheaf.Paper.ProjectionMateExact`: `ringedProjectionMateExact` and the counit-defined tensor mate, as a proof import through `AugmentedDiagramProjectionMate`.
- `Sheaf.Paper.CompletedPullbackAdjunction`: `ConstantCompletion.completedPullbackAdjunction`; its constant-module category, inverse-image and completion interfaces are public through the strict quotient and AdicSites modules.
- `Sheaf.CategoryTheory.DiagramSiteRealization`: `exists_diagramSite_realization`, with the vertical topology and exact module equivalence.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`: `ringedStrictTowerHomotopyLimitIndependentCoefficients`, for the standard strict derived inverse limit, also used through the existing completion API.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`: `ringedToposDerivedPushforwardComposition`.
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`: `ringedTowerPushforwardLimitComparison`; `AdicSites.Morphism.directLimitIso` is its adjunction characterization on the chosen ordinary/derived functors.
- `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization`: `ringedConstantTowerPushforwardNormalization`, including χ's strict counit and limit normalizations; imported publicly by the augmented-diagram statement.
- `Sheaf.Paper.AugmentedDiagramProjectionMate`: `StrictReduction.augmentedDiagramProjectionMate`, especially its equivalent-transpose and evaluation clauses.
- `Sheaf.Paper.StrictQuotientDiagonalNormalization`: `strictQuotientDiagonalNormalization`, `StrictQuotientDiagonalPresentation`, its `reductionD`, `restrictionD`, and `representative`.
- `Sheaf.Paper.CompletionMateComparison`: public `AdicSites.Site`, `Morphism`, the ordinary and derived adjunctions, `PerfectQuotients`, `finiteProjection`, and the normalized finite/tower comparisons. These existing generic definitions are now owned by
  `def-pur-adic-site-strict-quotient-interface`, with `existing: true` on the unchanged
  module. The theorem `completionMateComparison` is neither invoked nor cited as a
  statement dependency. The former dependency's record points at
  `ProEtaleConstantReductionTower`, which did not own these definitions.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`: `DerivedCategory.IsPerfectRingComplex`, the universe-independent bounded finite-projective model predicate.
- `Sheaf.CategoryTheory.SystemEvaluationTopos`: `systemSequenceEvaluationAdditive`, `systemSequenceEvaluationLimits`, `systemSequenceEvaluationColimits`.

The remaining imports are the stated proof dependencies: diagram coefficient restriction,
the coefficient-restriction counit, exact realization of constant modules, finite-projective
coefficient packages, perfect ringed-site projection, canonical tensor pullback, and the
cohomology criterion for derived isomorphisms. The proof dependency
`lem-pur-quotient-diagram-projection-evaluation` has no recorded Lean declaration on the
read base, so there is no module to import for it. The delivered canonical evaluation data
are specified directly, and their construction is part of the item's seven-step proof.

Edge cases checked before drafting: `I = ⊥` gives the constant A-quotient sequence; `I = ⊤`
gives zero quotient coefficients and zero completed output; a subsingleton coefficient ring
is allowed; an empty site is allowed by `Site` and all section formulas are universally
quantified; all unbounded F, including zero, are permitted. No uniform amplitude or rank
bound across n occurs. No independent small test-object universe is introduced.

Searches (2026-10-21):

- msearch LeanSearch, `Derived projection formula for a perfect coefficient and compatibility with the derived completion unit`: eight results, including `CategoryTheory.Adjunction.derivedε`, `derivedη_fac_app_assoc`, and ordinary adic-completion maps. No strict quotient exchange/unit theorem.
- msearch LeanFinder, `Perfect quotient coefficient exchange isomorphism derived pushforward strict towers completion unit normalization`: eight unrelated perfection/tilt results; no match.
- msearch Loogle, `CategoryTheory.Adjunction.homEquiv, IsIso`: no result (`IsIso` was not recognized by that search endpoint). The follow-up name-only `CategoryTheory.Adjunction.homEquiv` query returned 12 adjunction Hom-equivalence declarations, including `homEquiv`, `homEquiv_apply`, `homEquiv_unit` and `comp_homEquiv`; none states the item.
- msearch grep, `coefficientExchange|quotientExchange|perfect.*projection`: no Mathlib match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for `perfect.quotient`, `PerfectQuotient`, `coefficientExchange`, `quotientExchange`, and related exchange patterns found the existing AdicSites helpers and `StrictQuotientExchangeUnitEquation`. The latter concerns a four-corner exchange square and does not state this single-morphism completion-unit normalization. The whole item id had no upstream WeilConjectures match.
- rg in Mathlib's derived-functor and derived-category directories for quotient exchange, coefficient exchange and completion unit found no declaration of the item.

No statement fault or disputed mathematical claim was found. No correction is proposed.

## Second reading by NO

This is the worker's clause-by-clause rereading, not a claimed independent second agent
review: the dispatcher explicitly forbids starting agents, and the maintainer performs
the independent review. I reopened the node and the module while checking the table above.
The quotient evaluation is quotient-linear, not merely an A-linear evaluated arrow.
Both ordinary and derived adjunction normalizations are retained. The whole-diagram
cochain equations prevent accidental replacement of the strict map by unrelated evaluated
maps. The rho equation uses the existing reflector unit, with both endpoint comparisons
and the inverse of the direct-image/limit comparison in the specified direction.
No hypothesis was added and no clause was dropped. Compiler repairs make exact evaluation and quotient-category K-injective instances explicit,
and separate comparison data from their normalization predicates; they do not change the
mathematical statement. The canonical scalar-restriction/pushforward isomorphism is included
in the finite evaluation equation so its endpoints retain their quotient coefficients.

Validation before this repair: the saved packet's required initial `deliver2.py
--no-push` passed preflight and both sandbox/published-name compiles (dry-run commit
3f8f8206e4a). That result did not resolve the independent review's ownership defect;
the repair below is included in the new packet and checked again before delivery.


## Repair of return L (H2/H12)

The returned immutable head is e69a32791471. Compared the retained packet with the
current shared read clone: only `lean` and `stmt_deps` differ on the item. The required
initial dry run rebased the retained packet through the authorized delivery wrapper.
The theorem, all its helper declarations, its seven-step proof docstring, and its
hypotheses and equations remain byte-for-byte the retained Lean module.

Replaced the added theorem dependency `lem-sp-completion-mate-comparison` by
`def-pur-adic-site-strict-quotient-interface`. The definition node records the actual
unchanged module `Sheaf.Paper.CompletionMateComparison`; its declaration inventory owns
`AdicSites.Site` and `Morphism`, their module and derived adjunctions, strict tower
operations, reduction, completion/unit/limit and complete-subcategory aliases,
finite reduction/restriction/evaluation, `evaluatePushIso`, `finitePullIso`,
`finiteRestrictionPushIso`, `finiteModuleRestrictionPullIso`, `reductionPullIso`,
`directLimitIso`, `finiteProjection`, and `PerfectQuotients`. It also records the
normalized predicates and all nine `existsUnique` helpers used by the corresponding
`.exists.choose` definitions: `Site.deltaAdjunction`, `Site.finiteModuleAdjunction`,
`Site.finiteAdjunction`, `Site.finiteEvaluationIso`,
`Morphism.moduleReductionPullIso`, `Morphism.reductionPullIso`,
`Morphism.evaluatePushIso`, `Morphism.finitePullIso`, and
`Morphism.finiteModuleRestrictionPullIso`. Their exactness/K-injective instance support
is included. The new node does not claim the unrelated completed-square/mate theorem.

Retained `lem-pur-system-evaluation-topos`: the report and Lean lines 98–111 use its
Additive, finite-limit and finite-colimit instances to type exact `evaluationD`.
The reviewer explicitly passed this genuine dependency. No statement correction,
citer audit, new theorem, new module, or new sorry is required for the metadata repair.
The advisory overlap with `augmentedDiagramProjection` does not justify changing the
mathematically accepted strictExchange definition during this ownership repair.

## New nodes

`def-pur-adic-site-strict-quotient-interface` owns the existing small-site/strict
quotient interface (84 declarations), with `existing: true` and no new module or copy
of any definition. Its self-contained TeX introduces a small site, the geometric
adjunction and algebraic lift, constant coefficients, ordinary and derived module
categories, strict quotient towers and actual transitions, completion and its unit,
finite coefficient functors, normalized comparison maps, the direct-image/limit
comparison, the finite counit-defined projection and the perfect-quotient predicate.
The main record `structure Site` is verbatim before `where`; `lean.declarations` lists
the remaining existing signatures and normalization helpers. Source: Stacks 099M
(lemma-naive-completion), 099N (lemma-pushforward-Noetherian-case), 0941
(lemma-derived-limit-is-ok), 07A4 (lemma-pullback-tensor-product), 0B56
(equation-projection-formula-map), 03CU and 03D2. I opened the source passages for
completion, strict limits, tensor pullback and the counit-defined projection; this
node supplies their existing presentation interface, without asserting exchange
invertibility or the completion-mate identity. All notions it names by node id occur
in its stmt_deps. Its blueprint ancestor is `thm-pur-rational-and-qbar-purity`,
confirmed with `blueprint_refs.py ancestor`; via begins with the repaired item.

Searches run in this repair: msearch LeanSearch query "Small site geometric morphism
strict quotient towers derived reduction completion unit normalized comparison
interface" returned eight general site/smallness/normalization hits and no interface.
msearch LeanFinder query "Canonical derived inverse image direct image on a small site
with strict quotient reduction tower and uniquely normalized finite coefficient
comparisons" returned eight general site/functor hits and no interface. msearch Mathlib
grep `AdicSites|finiteEvaluationIso_existsUnique|reductionPullIso_existsUnique`
returned zero hits. rg of `lean/WeilConjectures` returned zero; rg of `lean/Sheaf`
located precisely the published module used here and its consumers. DAG rg for the
same declarations found no owner; the completion-mate node's recorded declarations
are in `ProEtaleConstantReductionTower`. Blueprint search "adic site" returned zero;
"strict quotient" returned three distinct reconstruction/completeness results,
none defining this interface. Exact query results are recorded in the new node.
`scompile.py --source Sheaf.Paper.CompletionMateComparison` confirmed the live server
module is identical to the read clone. Thus the interface already exists in Lean and
is reused, while its DAG ownership is new as the reviewer requested.

Additional second reading by NO: reopened the consumer's signature and its actual
uses (lines 65–453), the new node, and the recorded existing declarations. Site and
Morphism carry the same smallness, direction and algebraic lift; no new binder was
added to the consumer. Its ordinary/derived adjunctions are still the canonical
ones, not independent choices. Strict reduction still derives a whole diagram;
finite coefficient restriction and evaluation preserve the original quotient rings.
The nine unique-normalization predicates fix the chosen adjunctions/comparisons on
insertions, universal units or full representatives, precisely as the source module
does; no unconstrained existence data were introduced. `finiteProjection` is the same
adjunct of inverse finitePullIso then reduction of the ambient counit. `directLimitIso`
is the same conjugate, in the direction used inversely in rho. PerfectQuotients still
means a bounded finite-projective model separately for each positive quotient. The
new node excludes the completionMateComparison theorem. I rechecked I=0, I=A, zero
ring, empty site and F=0: neither the new record nor the consumer excludes them.
This reading repairs H2/H12 without reopening the clauses already accepted by L.
