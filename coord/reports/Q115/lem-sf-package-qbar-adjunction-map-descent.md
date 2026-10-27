## Worker report

The module `Sheaf.Paper.SfPackageQbarAdjunctionMapDescent` states
`WeilConjectures.sfPackageQbarAdjunctionMapDescent`, with its sole proof `sorry`.
Its helper `SfQbarEvaluationDescent` is an explicit Prop-valued definition, with
no postponed data. It expands the class formula for evaluation and its naturality.
No dependency module, new DAG node, or mathematical statement correction is needed.

Hypotheses and conclusions, clause by clause:

- `D : FiniteFieldDatum.{u}` fixes the algebraic closure of the finite base field,
  including its characteristic `D.p`; `l`, `[Fact l.Prime]` and `hl : l ≠ D.p`
  are the distinct coefficient prime. `Ω : Type v`, its Field, Padic algebra and
  IsAlgClosure instances are the chosen algebraic closure of Q_l. The scheme
  universe `u` and coefficient-closure universe `v` are independent.
- X and Y have the specified Over structures, separated structure maps,
  LocallyOfFiniteType and QuasiCompact structure maps. The morphism f is over
  the same base and is separated, locally finite type and quasi-compact, hence
  finite type. `c : Compactification f` specifies the construction coordinates
  already used by the compact-support definition. It is universally quantified,
  so no choice or restriction of compactification is imposed.
- The categories are precisely `GeneralAlgebraicallyClosedCoefficients.Stage`
  and `Pair`, built from `sfRationalConstructibleCategory`, with the recorded
  scalar transitions and associators. The pair Hom has its published canonical
  `homCoordinates` equivalence with the abelian direct limit, not a replacement
  category or set of arbitrary maps.
- F and G are `StageSystem.Morphism` objects on these exact two stage systems.
  Their Φ fields give the rational operations and β their specified comparisons;
  Morphism.coh is the tower equation with the actual scalar associators. `hF`
  pins every F.Φ to the published compact-support rational functor.
  `a E : F.Φ E ⊣ G.Φ E` is precisely the assumed finite-field exceptional
  adjunction. This characterizes the exceptional right adjoint, including
  its maps, up to the unique adjunction-compatible isomorphism; it is not a
  freely supplied comparison or an assumption of the sought common-stage
  adjunction. The two displayed `unit` and `counit` hypotheses are exactly
  preservation by β of the specified finite adjunction maps.
- The equal-field comparison normalization is implicit in Morphism.coh,
  specialized to the identity inclusion, with the invertible scalar unitor:
  cancellation forces the normalized equal-field comparison to be identity.
  This uses no additional hypothesis or excluded equal-field case.
- `∃ A : F.functor ⊣ G.functor` supplies the induced natural adjunction.
  The first two conjuncts give BOTH directions of the displayed Hom-colimit
  bijection on EVERY common-stage representative. The β at each endpoint
  identifies the Hom systems in the question with the Hom of the literal
  output pair. Each β is invertible, so these displayed representatives
  exhaust the corresponding Hom groups, rather than just a restricted family.
- The next two conjuncts say that A.unit and A.counit are the images of the
  original finite maps through the canonical `inclusion`. This is exactly
  the notation [E,eta_E] and [E,epsilon_E]. The published inclusion uses
  T_(E/E) on an arrow, which is its unitor-normalized E representative.
- `SfQbarEvaluationDescent` is asserted for both X and Y. It uses
  `commonStageHomPairs`, hence only the pairs on which the dependency defines
  internal Hom. This is the domain already specified by
  def-weil-derived-pullback-tensor-hom, not a new restriction to perfect inputs.
  The base prime is transported to each residue field by an inline
  `IsUnit.invertible` term along the canonical residue-field point map;
  no residue-invertibility assumption is added.
- Its first conjunct spells out evaluation at any L. The implication identifies
  the operation's published object with its literal `commonStageHomObject`
  representative, as in `PodCommonTransposeNormalization`. Given any finite
  representative φ of the identity, evaluation is the class of its finite
  inverse transpose, conjugated by `commonStageTensorComparison` and
  `commonStageHomComparison`. For the identity representative this is exactly
  [L,ev_L] after those comparisons. The implications do not impose a condition
  on evaluation or exclude any arrow: the published operation-object equality
  and representative theorem supply such representatives at every sufficiently
  large L. The formula also covers every representative of that identity.
- The second conjunct is the combined naturality/dinaturality equation for an
  arbitrary arrow g of the full permitted-pair subcategory. Its first component
  is contravariant, its second covariant. Taking either component to identity
  gives separately the two equations in proof step 5, with the correct domain
  H(P',Q) tensor P for dinaturality.
- Independence of common field and eventual equality is built into the actual
  pair-category quotient and `Morphism.functor`, and the formulas quantify over
  every representative. They therefore also apply to identity-represented
  change-of-field isomorphisms and changes of object presentation. Naturality
  for all pair-category arrows is part of Adjunction, and is explicit for
  evaluation. Both triangles are fields of Adjunction, not extra assumptions.
- The final finite-diagram clause is rendered by the representative identities
  together with the existing category and functor structures: each expression
  in such a diagram is the image of its finite-stage expression. Composition,
  identities and application of F/G are preserved by Morphism.functor;
  tensor/Hom are the already recorded functors with their normalized comparisons;
  units, counits and evaluation are identified above. Thus equality of the
  finite expressions is equality of their classes. No additional predicate
  quantifying over an undefined language of 'finite diagrams' is introduced,
  and no tautological equality conjunct is appended in its place.
- No finite quotient reduction functor on the algebraically closed category is
  introduced or asserted.

Dependency declarations read and used:

- `Sheaf.Paper.SfRationalizationKaroubi`: sfRationalConstructibleCategory,
  sfRationalScalarExtension and its signature/docstring (raw scalar localization).
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: Stage, stageSystem,
  stageTransition, Pair, homCoordinates, ColimitHom, ofHom, inclusion; actual
  scalar associator and unitor. These are the literal common-stage construction.
- `Sheaf.Paper.QcqsCompactSupportRealization`: sfQcqsCompactSupportRealization,
  and its projection-normalization specification.
- Added owning stmt_dep `def-weil-compact-support-finite-action`, module
  `Sheaf.Paper.CompactSupportFiniteAction`: `sfCompactSupportFiniteFunctor`
  supplies the normalized rational functor in hF, with the exact source and
  target rational categories and its tensor-extended integral Hom map.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its public
  Data module: System, Operation, Comparison and FieldComparison signatures.
  Their finite F/G adjunction and completed unit/counit equations motivate
  exactly the two hypotheses used here, without assuming the System's already
  descended adjunction as a premise.
- `Sheaf.Paper.DerivedPullbackTensorHom`: commonStageDerivedTensor,
  commonStageDerivedInternalHom, commonStageHomPairs, commonStageHomObject,
  commonStageTensorObject, commonStageHomPairAtStage and both comparisons;
  rationalDerivedInternalHom and rationalDerivedTensor.
- Added already-landed stmt_dep `lem-pod-derived-automorphism-hom-evaluation`,
  module `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: podCommonClosed,
  podRationalClosed, PodPartialClosed.evaluation and the published
  PodCommonTransposeNormalization (read to specialize it explicitly here).
- Added genuine stmt_dep `lem-weil-structure-direct-images-constructible`,
  module `Sheaf.Paper.DirectImagesConstructible`: `finiteFieldDatumPrimeUnit`
  supplies its theorem conclusion `IsUnit (l : D.k)`, used both in `hF` and
  the inline residue-field transport.
- `WeilConjectures.CategoryTheory.StageSystem.Functor`: Morphism, mapAt,
  functor and its object and mkHom formulas; β/coh and the stage inclusions.
- Proof leaf `lem-coef-qbar-adjunction-hom-descent` has no lean record and does
  not need one: its recorded Mathlib match is AddCommGroup.DirectLimit.congr,
  congr_apply_of and congr_symm_apply_of in Mathlib.Algebra.Colimit.Module.
  Their full signatures and docstrings were read; the module is a proof import.

Edge cases checked: empty schemes and zero objects impose no nonzero condition;
identical coefficient fields use the scalar unitor; composita provide common
stages; arbitrary successive enlargements are allowed; transitions need not be
injective or faithful. The two universes remain independent. No finite-Tor,
perfectness or integral internal-Hom constructibility is silently assumed beyond
its already specified permitted-pair domain. The evaluation equation has the
correct contravariance, including mixed arrows and identity components.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: 'Compatible adjunctions on finite coefficient fields descend to
  the common stage pair category preserving unit counit and internal Hom
  evaluation': 8 general adjunction/closed-category hits, no statement match.
- Loogle: 'CategoryTheory.Adjunction, AddCommGroup.DirectLimit.congr': 0 hits.
- LeanSearch: 'Adjunctions compatible with scalar extension induce an adjunction
  on a directed common stage category with evaluation unit and counit formulas':
  8 ordinary adjunction/change-of-rings hits, no exact match.
- Mathlib grep: '[Aa]djunction.*[Cc]olimit|[Cc]olimit.*[Aa]djunction|PseudoColimit',
  CategoryTheory: 25 generic colimit/adjunction hits, no common-stage formula.
  A narrower CategoryTheory/Category/PartialFun search also returned 0 hits.
- rg of lean/WeilConjectures and lean/Sheaf for common-stage adjunction/descent,
  qbar adjunction and the item id found the generic StageSystem.Functor API,
  ExceptionalCommonStageDescent (closed/open localization with extra hypotheses),
  SmoothPurityQbar (a smooth purity right adjoint), and the normalized partial
  closed calculus. None states this package and its two Hom representative maps.
  The exact new declaration names were absent from both roots and Mathlib.

The item statement is unchanged. There is no STATEMENT-DISPUTED finding.
The one theorem has sorry as its entire proof; its docstring contains all six
DAG proof steps. There are no unbound implicits and no local notation/instances.

## Second reading by Q115

I reread the node and the final module in a separate pass; the dispatch explicitly
forbids starting another agent, so this is a worker self-check. The independent
maintainer review remains the independent review of this delivery.

The first pass exposed a namespace-open ordering error and expensive inference
through `ofHom`. These were repaired by opening the namespaces inside
WeilConjectures and naming the source/target of the existing mkHom constructor.
No compiler limit was increased in the final file. The complete final module
compiled through scompile.py with only the expected sorry status.

The rereading also replaced a broader inverse-transpose normalization conjunct
with its explicit identity specialization: the node asks for evaluation, so the
final helper spells out that evaluation class. Inverse transposition is used
with the recorded tensor/Hom comparisons, and its naturality includes the first
variable's reversed arrow. Unit and counit use the actual stage inclusion; both
Hom directions apply to all common-field arrows, not just same-field objects.
The final finite-diagram assertion is a consequence of those generator formulas
and the existing functor laws, as explained clause by clause above. No additional
comparison or map was chosen, and no definition is duplicated.

## Repair of the returned delivery

F1 (H2): removed `thm-trf-internal-hom-pullback` from `stmt_deps` and
removed its module import. The evaluation definition now constructs its
pointwise `Invertible (l : W.residueField x)` directly with `IsUnit.invertible`:
map `finiteFieldDatumPrimeUnit D l hl` along the ring homomorphism induced by
`W.fromSpecResidueField x ≫ (W ↘ Spec (.of D.k))`, and simplify `map_natCast`.
This is the exact term previously wrapped by `finiteHomPrimeInvertible`;
no new notion, theorem, or assumption is introduced. The theorem's statement
and the Prop defined by the evaluation helper are unchanged.

F2 (H2): added the existing definition node
`def-weil-compact-support-finite-action` to `stmt_deps` and explicitly imported
its owning `Sheaf.Paper.CompactSupportFiniteAction` module. Read its full
statement, Lean record, and `sfCompactSupportFiniteFunctor` signature and
docstring: the normalized rational compact-support functor in `hF` is precisely
its declaration. No copy of that definition is introduced.

The genuine dependency `lem-pod-derived-automorphism-hom-evaluation` is retained:
`podCommonClosed` and `podRationalClosed` select the closed calculus from its
conclusion, so this statement uses that theorem, as the return confirms.
Comparison with the current read-only main node confirms that the packet changes
only `lean` and the explicitly reviewed dependency additions; the mathematical
statement, proof, proof dependencies and maintainer fields are unchanged.

Self-check with the repaired module and node open: the canonical residue-point
map exists for every scheme over the base, including each empty-scheme case
vacuously. Mapping a unit adds no hypothesis; the inline expression is the
unfolded body of the previous helper. Both independent universes remain unchanged. The `hF` expression and every unit, counit, Hom
representative and evaluation clause remain verbatim. This directly repairs
both numbered findings while preserving the mathematics approved in the return.

Removing the large internal-Hom-pullback import exposed two previously transitive
imports. The first repaired compile diagnosed the missing names
`finiteFieldDatumPrimeUnit` and `CategoryTheory.StageSystem.Morphism`.
The module now imports their exact owning modules directly:
`Sheaf.Paper.DirectImagesConstructible` and
`WeilConjectures.CategoryTheory.StageSystem.Functor`. The former's DAG owner,
`lem-weil-structure-direct-images-constructible`, is also cited: unlike the
removed plain-definition dependency, the actual theorem conclusion
`IsUnit (l : D.k)` is used. Its recorded declaration and full docstring were
read. This keeps the dependency graph faithful after removing the broad import;
no theorem, helper definition or mathematical statement was altered.

Repair validation (2026-10-24 UTC): the final module passed `scompile.py` in
both sandbox and actual library-module modes with exit code 0 and no reported
errors or warnings. The serialized theorem signature was checked byte-for-byte
against the final Lean file, and all Lean lines satisfy the 100-character limit.
