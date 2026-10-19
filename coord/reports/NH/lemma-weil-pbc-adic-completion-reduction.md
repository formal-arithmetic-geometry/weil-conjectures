## Worker report

The module `Sheaf.Paper.AdicCompletionReduction` states
`AlgebraicGeometry.Scheme.adicCompletionReduction_isIso`, with `sorry`, and the
naturality theorem `adicCompletionReduction_naturality`, also with `sorry`.
Its helper definitions specify the actual adjoint of the canonical evaluation;
they do not choose an unrelated morphism or an isomorphism of the two objects.
All definitions have real data. Every postponed theorem has the owning blueprint
identifier and its source and natural-language proof in its docstring. The helper
theorems supply exact restriction, the scalar-adjunction Hom bijection, and strict
naturality of quotient transitions, all used in the node's construction/proof.

Hypotheses and clauses, in the node's order:

- The scheme X is `X : Scheme.{t}`. The small pro-etale site and constant ring
  sheaves are the recorded `proEtaleDerivedCategory`, `adicConstantRing`, and
  `adicModuleRing`, not the completed-coefficient sheaves used in other nodes.
  Site objects remain in t+1 and morphisms in t.
- The commutative ring is `Λ : Type t` with `[CommRing Λ]`. The datum
  `d : CompleteCoefficientDatum Λ` contains precisely `noetherian`,
  `ideal : Ideal Λ`, `finitelyGenerated : ideal.FG`, `quotientTorsion`, and
  `quotientPerfect`. Finite generation is recorded without choosing a generating
  tuple, since no conclusion depends on its choice. `quotientTorsion` means
  every element of Λ/I is annihilated by a positive natural integer.
- `K : proEtaleDerivedCategory X Λ` is arbitrary. There is no completeness,
  constructibility, boundedness, flatness of K, or finiteness-of-quotient-sets
  hypothesis. Each positive power quotient is perfect in degree zero by
  `d.quotientPerfect`.
- `M : AdicKFlatModel X Λ K` is the one fixed K-flat flat-term representative
  for every reduction. This is a model parameter, not a restriction on K:
  the recorded `adicKFlatModel_exists` provides it for every K.
- `adicReduction X d M ⟨n+1, Nat.succ_pos n⟩` is K_a, with a=n+1. It uses
  `adicChange` and `adicLocalization`, retaining the quotient-coefficient
  action. `adicReductionComplex` is its scalar-restricted strict chain model,
  and `adicReductionComplexStep` is the canonical quotient transition.
- L is the recorded `adicCompletionObject X d M`. This is Q of the explicit
  product-cone fibre of 1-s for that very strict tower, rather than an arbitrary
  chosen Roos triangle. On this pro-etale module category, exact countable
  products identify termwise and derived products. The `CompletionMap` module's
  `adicCompletion_distinguished`/`adicCompletionLimit` provide its derived-limit
  identification with the specified projections. The generic strict-tower
  theorem describes the same total derived inverse limit; using the explicit
  cone model here avoids imposing its older equal-universe small-site interface
  on the pro-etale site. No site universe is collapsed.
- `adicCompletionEvaluation X d M n` is p_a: Q of the cone-to-product chain
  projection followed by the n-th product projection, with no arbitrary lift.
- `N : AdicKFlatModel X Λ (adicCompletionObject X d M)` computes the derived
  extension of L. Thus `adicReduction X d N ⟨n+1, Nat.succ_pos n⟩` is exactly
  L tensor^L P_a in the quotient-coefficient derived category. Again N exists
  for every L and places no additional restriction on K.
- `adicDerivedRestrict` is the exact termwise restriction derived functor.
  `adicDerivedRestrictFactors` is its canonical comparison with termwise
  restriction, including the isomorphisms required to type the evaluation.
- `adicReductionDerivedUnit` uses the uniquely characterized quotient
  augmentation from `CompletionMap`, m ↦ 1 tensor m, transported through N's
  realization and the restriction comparison. The bijection
  `adicReductionAdjunction_bijective` has the formula f ↦ unit followed by
  restriction(f). `adicReductionHomEquiv` is `Equiv.ofBijective` of that
  specified function, so its inverse is uniquely determined.
- `adicCompletionReduction` is that inverse Hom bijection applied to p_a,
  transported by the restriction comparison. The main theorem asserts
  `IsIso (adicCompletionReduction X d M N n)`, in the P_a-coefficient category,
  for every `n : ℕ`. This covers every a≥1, including a=1, without an a=0 case.
- Functoriality is `adicCompletionReduction_naturality`. For every chain map f
  between fixed K-flat representatives, `adicReductionComplexMap` is its actual
  termwise changed and restricted map; `adicReductionComplexMap_step` gives
  strict transition compatibility; and `adicCompletionModelMap` is the recorded
  cone map with the product map in both coordinates. `adicReductionMap` is
  derived scalar extension on an arbitrary derived morphism, characterized
  using the scalar unit. The displayed naturality square uses these maps on K
  and on L, for any choices N,N' of their K-flat representatives. Maps between
  K-flat representatives generate the derived localization (including roofs
  and inverted quasi-isomorphisms), so this records functoriality in K and
  independence of its representative. No compatibility condition is assumed
  on f and no arbitrary map of limits is substituted.

Dependency declarations used:

- `Sheaf.Paper.CompleteCoefficientDatum`: `CompleteCoefficientDatum`,
  `AdicKFlatModel`, `adicKFlatModel_exists`, `adicConstantRing`, `adicModuleRing`,
  `adicModuleMap`, `adicLocalization`, `adicChange`, `adicRestrict`,
  `adicChangeHom`, `adicReduction`, `adicTransitionComplex`.
- `Sheaf.Algebra.Homology.DerivedTensor`: `derivedTensorRing`; the recorded
  `adicReductionUnderlying_tensor` in CompleteCoefficientDatum identifies
  its underlying derived tensor with the chosen scalar-extension model.
- `Sheaf.Paper.CompletionMap`: `adicReductionComplex`,
  `adicReductionComplexStep`, `adicReductionAugmentation`,
  `adicReductionProduct`, `adicCompletionProjection`, `adicCompletionObject`,
  `adicCompletionTowerMap` and its characterization theorem. This exact
  landed definition is now added to stmt_deps, as allowed by the standing brief.
- `Sheaf.Paper.AdicDerivedInverseLimit`: `adicReductionSequence` (transitively
  imported with CompletionMap), used as the target of evaluation.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`.
- The recorded modules `Sheaf.Algebra.Homology.DerivedChangeOfRingsGeneral`
  (`SheafOfModules.derivedChangeOfRingsGeneral`),
  `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
  (`SheafOfModules.module_pullback_pushforward_adjunction`),
  `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
  (`CategoryTheory.Adjunction.exists_derived_adjunction_of_essentially_constant`),
  and `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
  (`CategoryTheory.ringedStrictTowerHomotopyLimit`) are imported for the proof
  and canonical adjunction construction. Their full recorded interfaces and
  source docstrings were read. In particular the generic adjunction's large
  existential interface is not used to choose an arbitrary adjunction here:
  the required Hom bijection is specified by the actual unit's formula.
- Other available proof modules are imported directly or through CompletionMap
  and CompleteCoefficientDatum: perfect ring complexes, strict perfect
  coefficient packages, K-flat resolutions, derived-limit products, exact
  countable pro-etale products, K-projective map representatives and exact
  sheafification. The unstated intrinsic Koszul completion and Koszul/quotient
  limit nodes have no modules yet; they are proof prerequisites, not objects
  needed to state this theorem. They are named in its proof docstring.

Edge cases checked before writing: n=0 denotes a=1 and removes no initial
levels in the proof; the zero complex and the empty scheme are included;
I=0 (empty generating list allowed) and I=top (zero quotient coefficients)
are included whenever the datum's explicit hypotheses hold. Unbounded K is
allowed, and no quotient is assumed flat over Λ. The comparison retains the
quotient action instead of merely asserting an underlying Λ-isomorphism.

Searches (no existing statement of this assertion was found):

- `msearch.py leanfinder`, query "Derived adic completion modulo a perfect
  ideal power quotient recovers the derived reduction": eight ordinary
  AdicCompletion hits, including `AdicCompletion.of_apply` and
  `AdicCompletion.exists_smodEq_pow_smul_top_and_mkQ_eq`; no derived sheaf
  completion or adjoint-evaluation assertion.
- `msearch.py loogle`, query `"IsDerivedLimit"`: zero hits.
- `msearch.py grep`, query `derived.*complet|complet.*derived`, subdirectory
  RingTheory: zero hits.
- `rg` across the upstream WeilConjectures tree and the project's Sheaf tree
  for adic completion, towers and adjoints: ordinary ring-completion results,
  the coefficient/derived-limit modules, and the exact cone construction in
  CompletionMap; no finite-reduction assertion. An exact upstream grep for
  the item identifier returned no result. Searches for derived restriction
  found same-universe/private restriction-exactness helpers, none usable as
  a public interface on the actual pro-etale site; this module's named helper
  states that exactness for the recorded coefficient maps without extra data.
- DAG inspection found the existing completion-map node that owned the missing
  cone construction in the earlier wait. It has now landed and is reused.
  The item's blueprint source and full proof, the six statement-dependency
  records, their signatures/docstrings, and the pro-etale framework notes
  were read. The cone construction, strict tower or coefficients are not
  duplicated in this delivery.

No statement correction, dependency-record repair, new independent notion, or
STATEMENT-DISPUTED finding is needed. Only the item's lean record and addition
of the landed completion-map statement dependency are delivered.

Validation: the final file compiled cleanly with the prescribed scompile.py
wrapper, as a sandbox module and under its final library module path. No global
build was run. The delivery dry run is the final mechanical validation; the
second reader supplies the independent reading and performs delivery.

## Second reading by NH

I read the node and its six-step proof independently against the complete module,
the blueprint source at order 1260, and the recorded dependency declarations. The
source's displayed map is the adjoint of projection, not a tensor of projection
followed by an unspecified isomorphism. The following is my object/hypothesis/clause
inventory, with the corresponding Lean and verdict.

- Scheme X: `X : Scheme.{t}`; `proEtaleDerivedCategory X Λ` unfolds to the small
  `X.ProEt` site, constant ULift ring sheaf, and standard derived localization.
  The site has object universe t+1 and morphism universe t. Match.
- Commutative Noetherian coefficient ring Λ: `{Λ : Type t} [CommRing Λ]` and
  `d.noetherian : IsNoetherianRing Λ`. Match; no field or nonzero-ring assumption.
- Finitely generated ideal I=(f_1,...,f_r): `d.ideal` and
  `d.finitelyGenerated : d.ideal.FG`. The theorem depends on the ideal, not a
  selected list; existence of a finite generating list is exactly sufficient.
  There is no regularity or nonempty-list assumption. Match.
- Positive quotient powers P_a: `Λ ⧸ d.ideal ^ (n + 1)` and the positive-natural
  argument `⟨n + 1, Nat.succ_pos n⟩`. Every a≥1 occurs exactly once. Match.
- Additive torsion of Λ/I: `d.quotientTorsion` quantifies over every quotient
  element and asks for a positive natural annihilator. Match.
- Every positive quotient perfect in degree zero over Λ:
  `d.quotientPerfect`, through `adicQuotientPerfect`, is the recorded
  `DerivedCategory.IsPerfectRingComplex` on the actual quotient module in
  degree zero. This is not an assumption of flat quotients or finite sets. Match.
- Arbitrary K in D(X_proet,Λ): `{K : proEtaleDerivedCategory X Λ}`.
  `M : AdicKFlatModel X Λ K` contains the one fixed complex, K-flatness, flat
  terms, and a realization isomorphism. `adicKFlatModel_exists` supplies this
  for every K. It adds representative data, not a restriction on K. Match.
- Constant coefficient reductions K_a: `adicReduction X d M ...` is localization
  of termwise `adicChange` along the quotient ring map. It retains P_a action.
  `adicReductionUnderlying`, `adicRestrict`, and `adicReductionUnderlying_tensor`
  identify its Λ-object with the recorded derived tensor. Match.
- Strict inverse tower from the same representative: `adicReductionComplex`
  and `adicReductionComplexStep` reuse CompletionMap and the uniquely specified
  quotient transition in CompleteCoefficientDatum. No arbitrary tower or new
  coefficient sheaf is introduced. Match.
- Total derived limit L: `adicCompletionObject X d M` is localization of the
  explicit mapping-cocone of 1-s on the product of this strict tower.
  `adicCompletionProductComparison_isIso` and `adicCompletion_distinguished`
  identify that model and its projections with the derived product-cone limit.
  `adicCompletionLimit` packages that very triple. The generic recorded
  `ringedStrictTowerHomotopyLimit` has a same-universe interface; the explicit
  landed CompletionMap interface avoids imposing that equality here. Match.
- Canonical evaluation p_a: `adicCompletionEvaluation` is Q of the specified
  cone projection followed by `Pi.π ... n`. Match, including the map itself.
- Derived extension of L to P_a: `N : AdicKFlatModel X Λ
  (adicCompletionObject X d M)` and `adicReduction X d N ...`. Again N exists
  for every L, and does not assume completeness or boundedness. Match.
- Extension/restriction adjunction: `adicDerivedRestrict` is Mathlib's exact
  derived functor of the existing restriction functor; its factorization
  comparison is Mathlib's `mapDerivedCategoryFactors.app`.
  `adicReductionDerivedUnit` localizes the uniquely characterized ordinary
  augmentation m ↦ 1 tensor m and transports it through N's realization.
  `adicReductionAdjunction_bijective` states bijectivity of the exact function
  f ↦ unit ≫ restriction(f). `adicReductionHomEquiv` uses `Equiv.ofBijective`
  of that function. Its inverse is uniquely determined; no arbitrary Hom
  equivalence or triangle lift is chosen. Match.
- Specified isomorphism in D(X_proet,P_a): `adicCompletionReduction` is that
  inverse equivalence applied to evaluation, with the necessary restriction
  comparison. `adicCompletionReduction_isIso` asserts IsIso of this very map,
  in the quotient-coefficient category. Match, stronger than merely specifying
  an underlying-object isomorphism only in the sense required by the node.
- Functoriality: `adicCompletionReduction_naturality` quantifies over every
  chain map between the fixed K-flat models and every choice of N,N'.
  `adicReductionComplexMap` is actual changed/restricted scalar extension;
  `adicReductionComplexMap_step` is its strict transition compatibility;
  `adicCompletionModelMap` uses the cone map uniquely specified in both
  coordinates. `adicReductionMap` is specified by the scalar unit on any
  derived morphism. The equality is exactly the naturality square. K-flat
  representatives localize at quasi-isomorphisms, so these squares also
  express naturality through roofs, as the proof docstring explains. Match.
- No completeness hypothesis on K: none is present. Match.

I opened CompleteCoefficientDatum, DerivedTensor, CompletionMap,
AdicDerivedInverseLimit, DerivedChangeOfRingsGeneral, the derived adjunction
module, the module adjunction signature and its tensor/unit characterization,
and RingedStrictTowerHomotopyLimit. In particular, the last two generic
same-universe site interfaces do not become hidden instance assumptions of
this theorem; its specialized exact restriction/Hom-bijection interface is
stated explicitly on the actual pro-etale category. The available arbitrary-
site derived-change-of-rings interface has independent site universes and
computes extension on the same K-flat complexes. No private replacement of a
recorded coefficient or completion construction occurs.

Source checks: Stacks 099M (`proetale.tex`, lemma-naive-completion) assumes a
Noetherian ring and ideal and uses constant quotient sheaves; it imposes no
completeness assumption on K. Stacks 091Z (`more-algebra.tex`,
lemma-characterize-derived-complete-Koszul) uses Situation situation-koszul,
with an arbitrary ring and a finite generating list, and positive-power Koszul
towers. Neither adds a properness, characteristic, or scheme finiteness
condition. The blueprint's extra perfect-quotient hypothesis is explicitly in
the node and Lean, and is the input for tensor/product interchange. I checked
all six proof steps against the main docstring: Koszul comparison; bounded
finite-projective tensor/product calculation; tail removal; zero differential
and a-fold transitions; constant/pro-zero tower limits; identification of the
adjoint and quotient-action reflection. Nothing is proved in this delivery:
all five theorem bodies are `sorry`. All definitions have actual data; the
only new inverse is obtained from a bijectivity theorem fixing its function.
Every declaration has source/blueprint documentation. No unbound variables or
universes occur in the signatures or their defining expressions.

Edge cases: n=0 is a=1, with no discarded prefix. There is no requested a=0
case. Empty generating sets (I=0), I=top, the zero ring, zero K, and the empty
scheme are allowed whenever the stated datum holds. The tower index is always
the nonempty natural numbers; there is no arbitrary empty index set in this
statement. Unbounded complexes are allowed. No characteristic or common
positive annihilator is imposed on the torsion quotient. A common universe t
for the scheme and coefficient ring is the recorded site's size convention;
raising t accommodates both, and the site's unequal object/morphism universes
are preserved.

Independent searches on 2026-10-15:

- `msearch.py ... leanfinder` with “Tensoring a homotopy limit of powers of an
  ideal with its perfect quotient recovers the quotient complex”: eight
  ordinary AdicCompletion tensor-product results; none concerns the derived
  sheaf tower or the adjoint of evaluation.
- `msearch.py ... loogle '"AdicCompletion"'`: twelve ordinary module-completion
  declarations, not this assertion.
- `msearch.py ... grep 'completion.*quotient|quotient.*completion'`: sixteen
  unrelated or ordinary-completion results, no derived comparison.
- Independent `rg` searches across Mathlib, upstream WeilConjectures and this
  project's Sheaf tree used `derived.*[Cc]omplet|[Cc]omplet.*derived` and
  isomorphism/completion variants. I opened upstream Complete/Principal.lean:
  its relevant comparison uses a principal nonzerodivisor and first quotient,
  and the category of sheaves of modules, so it is not this arbitrary ideal,
  every-level quotient-action assertion. IntegralCoefficient's existing
  comparison instead characterizes completeness, also not this statement.
  Project matches are the reused datum/cone/Koszul definitions. No exact
  existing statement or replacement for this specialized Hom bijection was
  found.

Mismatch and repair: the worker report said intrinsic Koszul completion was
not yet available, but its node and module have now landed. I read its
signature and added the proof import `Sheaf.Paper.IntrinsicKoszulCompletion`,
required by the stage-2 import rule. Its empty-generating-list and unbounded
interfaces agree with the proof. The quotient/Koszul-limit theorem still has
no recorded module and remains a proof dependency, not a missing object needed
to type this statement. No mathematical signature, definition, or node field
needed changing. There are no new nodes or dependency repairs in this packet,
and no statement_change or citer audit is needed.

Validation: the original module passed the required wrapper in both sandbox
and final module modes (4.6s and 4.7s). The final module is recompiled after the
newly available proof import; delivery dry run and delivery follow.
