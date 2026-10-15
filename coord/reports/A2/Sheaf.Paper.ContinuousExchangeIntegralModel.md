## What changed

Replaced the assigned `continuousExchange_integral_model` hole with a complete construction
of an isomorphism in the full derived arrow category. Obtain an integral model M of K,
construct canonical endpoint comparisons, and transport the commuting exchange square along
the realization isomorphism. The final equation uses naturality and associativity and is
supplied to `Arrow.isoMk`. The original signature, visibility and target statements stay.

Proved `integralScalarExtension_exact` for the actual continuous integral-to-E coefficient
map. Construct the localization sequence explicitly in presheaf internal modules, prove its
colimit universal property on compact profinite tests, and transport it by monoidal
sheafification and inverse image from the point. Regular integral modules are flat;
`ObjectProperty.flat_colimit` gives flatness of the restricted regular E module. The
extension/forget/tensor comparison gives preservation of finite limits.

Constructed the bounded constructible scalar functor, actual pull and push comparisons,
and their source/target composites in `ContinuousIntegralComparisons`. These are real data;
no definition chooses data from an admitted mere-existence theorem.

Proved `continuousIntegral_exchange_square` from push-comparison invertibility and the
coefficient/exchange equation. Properness of f' follows by base change. Fully faithful
bounded constructible inclusions reflect isomorphisms, giving canonical endpoint
isomorphisms. No exchange morphism is inverted.

In `ContinuousIntegralExchangeEquality`, private proved lemmas establish the abstract
iterated-mate/counit identity and the exchange algebra from coherent pull comparisons.
The concrete compatibility statement remains an explicit mathematical obligation. The
attempted concrete restriction/normalization proof is not counted as proved. Its source
and complete proof plan, including the inverse-image cube, are in the public docstring.
Updated the original route and added six nodes. No other existing module was adapted.
No change record is needed: existing statements and definitions are unchanged.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.CondensedRing.continuousExchange_integral_model`.
The combining Lean proof is complete. This is a decomposition, not a claim that its entire
dependency closure is proved.

New public theorems proved without local holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralScalarExtension_exact`.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousIntegral_exchange_square`.

Every new remaining `sorry`, by declaration:

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_model`, in
  `Sheaf.Paper.ContinuousConstructibleIntegralModel`. Still needs constructible integral
  lattices on strata, extension by zero, and clearing denominators in the finitely many
  bounded-truncation extension classes, identifying rationalization with the actual scalar
  functor. Source: Bhatt--Scholze Lemma 6.8.13 and Proposition 6.8.14(2).
- `AlgebraicGeometry.ProEtale.CondensedRing.integralScalarPushHom_isIso`, in
  `Sheaf.Paper.ContinuousIntegralPushComparison`. Still needs the localization telescope on
  a representative with a common lower bound, qcqs pushforward continuity, and identification
  of its cohomology comparison with the specified mate `derivedPushHom`. Scalar exactness
  and the coefficient localization colimit are proved here. Source: Hemo--Richarz--Scholbach
  Lemma 5.3(1) and Bhatt--Scholze Lemma 6.8.2.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_equality`, in
  `Sheaf.Paper.ContinuousIntegralExchangeEquality`. Still needs the derived pull-comparison
  cube, restriction of the actual full derived adjunction counits, identification of the
  specified three-factor exchange with its adjunct, and concrete instantiation of the
  private proved mating algebra. The docstring gives the tensor-balancing and derived
  comparison argument. Source: Bhatt--Scholze Remark 6.8.15 and ChangeOfCoefficients.lean.

Original holes closed: 1 of 1. New holes added: 3. Local net: -2, a decomposition into three
strictly separate mathematical parts. No hole is in a definition or a private helper.
Existing imported admissions remain obligations of their own nodes.

## No longer needed

No existing mathematical dependency is claimed pruned: the old lattice and condensed
realization steps remain below model existence, and qcqs continuity below push comparison.
No original import was removed. Redundant MorphismDefs imports were omitted from the new
model and endpoint-square modules. The unused continuity proof import was removed from the
admitted push-comparison module; its planned DAG dependency stays.

The unlanded draft `ContinuousIntegralPullCoherence` and its proposed node are omitted:
its mathematical argument is included in the remaining exchange-compatibility obligation.
The draft inverse-component and pull-square-component wrapper definitions were omitted from
`ContinuousIntegralComparisons`, as the delivered proof does not use them. The new comparison
node lists all six retained declarations. Unused concrete normalization helpers and the
`import all MorphismDefs` proof import were removed from the exchange-equality module.
No existing Lean file or DAG node is withdrawn. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original lattice/realization dependencies have no Lean attachment, so their signatures
cannot simply be imported and applied. The integral-model statement isolates precisely the
existence part needed here, without reproducing the arrow theorem. The mathematical plan
was not found false.

The original node's inherited blueprint points to the created wrapper `nt-target-proetale-e`.
The new nodes instead point through it to the imported ancestor `thm-weil-pbc-finite-extension`,
second proof paragraph on rational transport. The existing blueprint field is outside this
proof-route update and is reported for metadata maintenance.

The derived coefficient comparisons need an actual exactness instance. This delivery proves
it internally; ordinary ring flatness alone does not supply this sheaf-module instance.
The concrete pull-comparison cube also requires proof; isomorphic endpoints do not identify
specified morphisms. The remaining compatibility statement records that requirement.

The concrete exchange proof attempt did not pass Lean's kernel check. Named morphism
interfaces, isomorphism-level component equalities, targeted rewrites and counit interfaces
were tried. The delivery makes no claim that the concrete compatibility is proved; the
checked generic algebra is retained as private helpers for completing that obligation.

Edge cases checked include zero complexes, empty schemes, and non-Cartesian squares in the
compatibility statement. That statement uses no properness or exchange invertibility.
Push continuity uses a common lower bound, not arbitrary unbounded coproduct preservation.
LeanSearch was unavailable, recorded as such; other searches and source matches are recorded
in each new node. No duplicate blueprint statement was found.

## New nodes

- `lem-weil-pbc-continuous-constructible-integral-model`: remaining model existence.
- `lem-weil-pbc-continuous-integral-scalar-exact`: proved internal-module exactness.
- `def-weil-pbc-continuous-integral-comparisons`: six constructed canonical declarations.
- `lem-weil-pbc-continuous-integral-push-comparison`: remaining bounded qcqs comparison.
- `lem-weil-pbc-continuous-integral-exchange-equality`: remaining concrete compatibility,
  with the abstract mating algebra proved in its module.
- `lem-weil-pbc-continuous-integral-exchange-square`: proved endpoint isomorphisms and square.

## Second reading by A2

1. **Statements and signatures.** Compared the delivered item module byte-for-byte with the repository version. The existing `continuousExchange_integral_model` signature and visibility are unchanged; its proof only is replaced. The six additional modules contain new declarations, and each declaration has a matching node and an explicit split status. No existing declaration was weakened, strengthened, or altered.

2. **Kernel-checked proofs and remaining holes.** Compiled all seven delivered modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry`s are the three named public split theorems `continuousConstructible_integral_model`, `integralScalarPushHom_isIso`, and `integralConstructible_exchange_equality`. There is no `sorry` in a definition and no `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declaration. The two new exactness/exchange-square results and the target theorem have proof terms; their imported obligations are reported rather than hidden.

3. **Truth and strength of split statements.** Checked each split statement against its docstring, source citation, and use sites. The integral-model statement gives exactly the needed existence and realization isomorphism; the push comparison states only invertibility of the specified mate under qcqs hypotheses; and the exchange compatibility states the concrete equality needed by the endpoint-square proof. The split statements are strictly smaller than the target and do not restate it. The comparison declarations are actual constructions from existing maps and isomorphisms, with no witness chosen from an admitted existence theorem.

4. **Pruning and proof route.** The target proof follows the constructed integral model, the concrete comparison data, and the endpoint exchange square, then uses naturality and `Arrow.isoMk`. Imports used only for proofs are private imports; statement-level imports remain public. The old condensed qcqs continuity import was removed from `ContinuousExchangeIntegralModel` after the proof was factored through the new push-comparison node. The draft pull-coherence module and unused wrapper helpers are omitted as recorded above. No unit-level step is bypassed.

5. **DAG and unit metadata.** Checked all six new node files for matching Lean declarations, complete source/proof/proof-origin/search metadata, split status, and `proof_deps`. The existing target node's proof and dependency route match the delivered Lean proof. The `sk-thm-properbasechange` unit record remains unchanged, including its realized statement and steps; the delivery supplies the lower-level nodes without replacing that route.

No further code changes were needed during this second reading.
