## Worker report

The module `Sheaf.Paper.QbarTwistCommonStage` states
`WeilConjectures.qbar_twist_common_stage`, with its proof exactly `sorry`.
It uses the intrinsic category of arbitrary schemes, not the legacy finite-field
category or the different PBC coefficient presentation. There are two small owning
helpers: `qbarTwistIntegralMap` wraps the actual derived tensor map in the full
intrinsic subcategory, and `qbarTwistIntegralBeta` wraps the already published
completed canonical beta component in that same full subcategory. Both definitions
have real data and no new choice of an object or an isomorphism.

Hypothesis and conclusion correspondence, reading the node alongside the Lean:

- The prime ell is `(l : ℕ) [Fact l.Prime]`. The scheme is `S : Scheme.{u}`,
  with `[∀ x : S, Invertible (l : S.residueField x)]`. The chosen algebraic
  closure is `Ω : Type v`, `[Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. Scheme and algebraic-closure universes are
  independent. No finite-field datum or structure morphism on S is introduced.
- The integer is `m : ℤ`. The two signs are indexed by `s : Bool`:
  `if s then m else -m`; `!s` interchanges them. At m=0 both are the zero twist;
  no proof that m is nonzero is assumed.
- A finite coefficient field is `E : AlgebraicallyClosedCoefficients.Index l Ω`.
  `Coefficient.{u} l Ω E` is the existing small field model. `Stage l Ω S E`
  is exactly the recorded raw rationalization of the intrinsic integral category.
  `Pair l Ω S` is exactly `generalAlgebraicallyClosedConstructibleCategory l Ω S`.
- The supplied finite-stage rational twist is `T s E`. `_hobj` fixes its
  object to the actual `integralTwistCoherenceObject` followed by rationalization.
  `_hmap` fixes its action on EVERY localized pure morphism `a ⊗ₜ f` to
  `a ⊗ₜ qbarTwistIntegralMap ... f`. Pure tensors generate the actual Hom
  groups, so this does not replace the prescribed twist by an unconstrained functor.
- `B_{F/E}` is `(stageSystem l Ω S).T h`, i.e. the recorded completed
  integral scalar extension followed by rationalization, with its canonical
  tensor-normalized associators. There is no new scalar extension construction.
- `b s h` is beta, with Lean source `T s E ⋙ B` and target `B ⋙ T s F`:
  thus its component is `B(T_E C) → T_F(B C)`. `_hbeta` fixes it on every
  integral object to `1 ⊗ₜ qbarTwistIntegralBeta ... C`, using the named
  `integralTwistCompletedBeta` of the dependency. This is the canonical
  rationalized comparison, not an arbitrary natural isomorphism.
- The identity comparison assumption is `_hunit`: beta is the scalar unitor
  on the twisted object followed by T of its inverse on the original object.
  HEq only accommodates the existing stage-system normalization of the functor.
- The tower assumption for BOTH signs is `_htower`, using the existing
  `StageSystem.pairFunctorCoherent` predicate. Its equation is
  `B_GF(beta_FE) ≫ beta_GF ≫ T_G(a) = a_T ≫ beta_GE`, exactly the
  node's equation in Lean's left-to-right composition order.
- `e s E : T s E ⋙ T (!s) E ≅ 𝟭 _` supplies the assumed finite-stage
  line-evaluation inverse identities. Their scalar compatibility is `_heval`:
  `beta^{-s}_{T_s C} ≫ T_{-s}(beta^s_C) ≫ e_F = B(e_E)`.
  Both ordered evaluations are inputs, as in the node; the theorem does not
  replace their compatibility by a triangle identity or assume any descended map.
- The existential `U` gives BOTH common-stage functors. The first conjunct fixes
  `(E,C) ↦ (E,T_E C)` literally, including the original coefficient stage.
- The second conjunct fixes their action on EVERY representative at EVERY common
  finite stage to `mkHom F ... (beta_source ≫ T_F.map f ≫ beta_target.inv)`.
  This is the node's displayed formula. The equality is HEq because the objects
  of the existential U are specified by the preceding equalities. Every arrow
  has a representative. Specifying the action of one actual functor on all
  representatives simultaneously says the class is independent of enlarging F
  (and of replacing representatives); identities and composition are preserved
  by the functor structure itself, rather than assumed as extra conclusions.
- `ε : ∀ s, U s ⋙ U (!s) ≅ 𝟭 _` gives BOTH inverse identities. Its final
  component clause requires the class of precisely the supplied finite-stage
  `e s P.stage` under the existing stage inclusion. Thus these are descended
  evaluation classes, not merely the existence of unspecified inverse functors.
- The last phrase, invertibility of Qbar(m), is expressed by these two inverse
  tensor-twist identities. Since `_hobj` and `_hmap` specify tensor with the
  published signed coefficient line on integral representatives, their values
  on the coefficient unit are exactly the two ordered tensor inverse
  identifications of Qbar(m) with Qbar(-m). No extra monoidal category or
  replacement coefficient line is postulated.

Dependency declarations read and used:

- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `Pair`,
  `stageSystem`, `integralTransition`, `unitor`, `ofHom`, `representatives`, and
  `generalAlgebraicallyClosedConstructibleCategory`. In particular its literal
  pairs, actual Hom-colimit representatives and normalized scalar comparisons
  are retained.
- `Sheaf.Paper.IntegralTwistDerivedScalarCanonical`:
  `integralTwistCompletedBeta`, the completed witness specified by
  `integral_twist_derived_scalar` and its K-flat/counit characterization.
- `Sheaf.Paper.IntegralTwistScalarCoherence`: `integralTwistCoherenceObject`
  bundles the actual signed derived tensor with the existing membership proof;
  `integral_twist_scalar_coherence` supplies the assumed tower equation after
  rationalization and its scalar-associator normalization.
- `Sheaf.Paper.PbcCoefficientTwists` publicly preserves
  `CoefficientTwistsDetailed`: `integralSheafTwist`, `integralTwistLine`, the
  signed roots/powers/duals construction and its canonical scalar maps. Its
  different `pbcTateTwist` is not used on an intrinsic pair.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization` and the actual tensor Hom encoding
  (reexported through the common-stage module).
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarComp`,
  `sfRationalScalarUnit`, with their tensor normalization; imported for the proof.
- `Sheaf.Paper.IntegralTwistBaseChange`: `integral_twist_base_change` and
  `IsCanonicalTwistScalarMaps`, especially negative-power evaluation compatibility;
  imported for the proof.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, publicly
  available through the stated dependencies. The small site retains object
  universe u+1 and morphism universe u.
- `Sheaf.CategoryTheory.StageSystemFunctorDescent`: `pairFunctorCoherent` and
  the existing `coefficientPairFunctor_exists` proof tool; no second quotient
  or copy of common-stage category is introduced.

Edge cases checked before and after writing: m=0, either sign, negative m,
E=F, E=F=G, zero complexes and maps, the empty scheme, distinct source and
 target coefficient stages, different choices of common overfield, and
independent scheme/closure universes. The assumptions include repeated stages,
the unit normalization, all localized scalars (not just integral arrows), and
both inverse composites. There is no nonemptiness assumption on S and no
characteristic, finite-type, smoothness or finite-field hypothesis on it.

Searches for existing statements and notions:

- `msearch.py ... leansearch "Coherent scalar extension compatible autoequivalences
  descend to a filtered common finite coefficient stage category"`: returned
  `CommRingCat.moduleCatExtendScalarsPseudofunctor`, scalar adjunction and
  localization results, and filtered-equivalence results. None states this
  intrinsic completed-derived/common-stage twist and evaluation descent.
- `msearch.py ... leanfinder "A coherent family of Tate twist functors commuting
  with scalar extension descends to inverse functors on a common finite stage
  category"`: eight generic monoidal/derived/Tor/shift hits, no exact match.
- `msearch.py ... loogle "CategoryTheory.Functor, CategoryTheory.Equivalence"`:
  twelve generic equivalence projections and constructions. They encode
  equivalences, but not the prescribed representative formula or evaluation descent.
- `msearch.py ... grep "twist.*[Cc]ommon|[Cc]ommon.*twist|StageSystem"
  CategoryTheory`: zero Mathlib hits.
- `rg` over `WeilConjectures` and `lean/Sheaf/Paper` for common-stage twists,
  Qbar twists, `sfIntegral.*Twist|Twist.*sfIntegral`, `intrinsic.*Twist`,
  `pairFunctorCoherent|coefficientPairFunctor_exists`, and evaluation names:
  existing legacy `coefficientTwistStageFunctor`, `algebraicClosureComplexTwistFunctor`
  and its map formula have the older finite-field coefficient category; the
  intrinsic functor uses a tensor-product presentation whose object stage need
  not literally stay at E. Neither states this conditional, beta-normalized
  descent of both evaluations on the actual intrinsic pair category.
  `StageSystem.coefficientPairFunctor_exists` supplies the existing general
  functor descent tool but not this node's prescribed finite twists and evaluations.
- `grep -rn "lem-weil-qbar-twist-common-stage"` in the source repository:
  no matches. The new declaration names also have no existing matches.

No statement correction, new nodes, dependency repairs, or statement dispute.
The module compiled cleanly through the prescribed `scompile.py`, as both the
sandbox and library-named file; no warnings were printed.

## Author self-check before delivery

This is the author's second pass, not an independent review; the dispatcher brief
requires direct delivery and the maintainer supplies the independent reading.
I reopened the node and file. The first compile exposed an orientation mistake:
Lean's `T ⋙ B` has value B(T C), so beta is b.hom, not b.inv. I corrected the
beta normalization, both factors of the evaluation compatibility equation, and
both endpoint factors in the representative formula. The recompile is clean.
I checked every correspondence above against the final signature, especially
both signs at m=0, the canonical pure-morphism and beta normalizations, the actual
intrinsic category, repeated stages, and the final component equation which
identifies ε with the same finite evaluations. The module has one postponed
named theorem, with the node's seven-step proof in its docstring; both helpers
are actual full-subcategory maps. The node copy changes only its lean record.

## Second reading by Q25

Independent maintainer reading, 2026-10-18, of immutable delivery
6546e68fa8508d04fe6ede238bcbb0d1c3de999f. This reader did not author the
module or its earlier self-check. The original self-check is preserved above
under its own heading. No Lean or node change was needed.

I read the item node and its seven proof steps, all eight statement-dependency
statements and bindings, the delivered module and report, and the source
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/prop-weil-twist-preserves.md`
(Proof, final sentence), together with the corresponding
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-existence/prop-weil-twist-preserves.proof.md`.
I opened the actual dependency declarations and docstrings in the read-only Q25
side clone, rather than using the older finite-field or PBC category by name.

Clause-by-clause reading:

- Prime and scheme: `l`, `Fact l.Prime`, `S : Scheme.{u}` and residue-field
  invertibility give exactly the stated coefficient condition. There is no
  finite-field structure, finite-type, smoothness or nonempty-scheme hypothesis.
- Algebraic closure and finite fields: `Ω : Type v` with `IsAlgClosure`, and
  `Index l Ω`, are the recorded closure and finite-subextension index. The
  existing `Coefficient.{u}` is the algebra-equivalent small model, obtained
  through `Shrink.algEquiv`; it imposes no equality between u and v.
- Category: `Stage` is the intrinsic raw rationalization and `Pair` is the
  existing `StageSystem.PairCategory`. The category has the recorded eventual
  equality of finite-stage representatives, not a Karoubi completion.
- Integer and both signs: `m : ℤ`, `if s then m else -m`, and `!s` specify the
  two twists. Both signs are required by the node's two inverse identities.
- Prescribed rational twist: `_hobj` fixes the actual derived twist object;
  `_hmap` fixes every localized pure morphism to the existing derived tensor
  map. In a scalar localization every morphism can be put over one denominator,
  so these normalizations determine the intended map on all morphisms; an
  additional additive-functor assumption is unnecessary here.
- Canonical scalar comparison: `b` has source `T_E ⋙ B` and target `B ⋙ T_F`.
  Thus `b.hom` is B(T_E C) to T_F(B C). `_hbeta` fixes its value on every
  unchanged integral object to the rational image of
  `integralTwistCompletedBeta`. The helper wraps that component in the existing
  full subcategory; it does not choose an arbitrary map or comparison.
- Identity and towers: `_hunit` is the scalar unitor on T(C) followed by T of
  the inverse unitor on C. `_htower` unfolds to B(beta) followed by beta and
  T(associator), equal to the source associator followed by beta. This is
  precisely the node's tower equation with Lean's composition convention.
- Finite inverse identities and their compatibility: `e s E` supplies both
  natural inverse isomorphisms assumed by the node. `_heval` is the composite
  comparison gamma followed by the finite evaluation, equal to the scalar
  extension of that evaluation. The theorem descends the supplied isomorphisms;
  it does not construct line evaluations from an uncharacterized choice.
- Object conclusion: the first conjunct for U keeps the stage E literally and
  applies the prescribed twist to its object.
- Morphism conclusion: the second conjunct quantifies over every pair, common
  stage, lower-bound witnesses and representative. Its order is
  beta_source.hom, T_F.map f, beta_target.inv, exactly the displayed node
  formula. Because U is a functor on the actual quotient, the same formula
  simultaneously asserts representative independence, enlargement independence,
  identity preservation and composition preservation.
- Inverse conclusion: epsilon supplies both natural inverse identities, and
  its component clause is the class of the very same finite-stage e under
  stage inclusion. This retains descent of the supplied evaluations rather
  than merely asserting that some equivalence exists.
- Line invertibility: the two specified tensor-twist inverses, applied to the
  coefficient unit, give the two ordered inverse tensor identifications for
  the signed line, as in node proof step 7. No separate monoidal structure is
  assumed by the delivery.

Dependency interfaces checked: `GeneralAlgebraicallyClosedCoefficients.Stage`,
`transition`, `integralTransition`, `associator`, `unitor`, `stageSystem`,
`Pair`, `transport`, `homCoordinates_existsUnique`, `ofHom` and representative
calculus; `sfRationalConstructibleCategory` and its localization; normalized
`sfIntegralScalarComp`, `sfRationalScalarComp` and scalar units;
`integralTwistCoherenceObject`; `integral_twist_derived_scalar` and its named
ordinary/completed beta projections; `integral_twist_scalar_coherence`;
`integralSheafTwist`, `coefficientTwistPower`, `coefficientTwistLine`,
`integralTwistLine`, `IsCanonicalTwistScalarMaps` and
`integral_twist_base_change`; and `StageSystem.pairFunctorCoherent` and
`coefficientPairFunctor_exists`. These are the interfaces described by the
recorded dependency nodes. `PbcCoefficientTwists` reexports the original
integral declarations; the different `pbcTateTwist` is not substituted.
`Scheme.ProEt` is the actual weakly-etale-over-S small site, retaining object
universe u+1 and morphism universe u, not an etale or discrete replacement.

Independent searches used `rg` over Q25's `lean/Sheaf`, upstream
`WeilConjectures`, and Mathlib with common/twist, intrinsic twist, the new
names, and stage-functor names. I opened the matches:
`algebraicClosureComplexTwistFunctor` and its map theorem concern the legacy
finite-field stage category; `intrinsicQbarComplexTwistFunctor` uses the
common-stage tensor bifunctor and has a different literal object/stage
presentation. Neither states the present conditional, normalized descent of
both evaluation isomorphisms. The generic stage-descent tool is reused, not
redefined. Both delivered helpers have genuine full-subcategory map data.
The worker's LeanSearch, LeanFinder, Loogle and grep searches are recorded.

Edge cases checked: m=0, m<0, either sign, repeated fields E=F=G and identity
embeddings, ramified extensions, different source and target coefficient
fields, alternative common overfields and further enlargements, zero
complexes/maps, empty schemes, and independent scheme/closure universes.
No branch assumes m nonzero, a nonzero object, a rational point, or a
nonempty scheme. All variables and universes are bound. The node's
`lean.statement` equals the module signature verbatim. All three declarations
are recorded. Source/blueprint docstrings are present, the theorem docstring
retains all seven proof steps, all lines are at most 100 characters, and the
only theorem proof is `sorry`. No new node or dependency repair was required.

Route-pivot audit: none of the item's statement/proof dependencies occurs in
`origin/newtargets-dag:coord/route-pivot-dropped.txt`. No repair note exists at
`coord/repair-notes/lem-weil-qbar-twist-common-stage.json` on that ref. The
module introduces none of the dropped infinity/dg/model-category machinery.
Its use of ordinary derived tensor and K-flat comparisons agrees with the
ordinary derived route.

Reproducibility: ran the prescribed wrapper against the immutable file:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q25 lem-weil-qbar-twist-common-stage snapshot/lean/Sheaf/Paper/QbarTwistCommonStage.lean`.
Exit 0, no errors or warnings: sandbox `Sheaf/Stage2/Sandbox0.lean` 18.5 s;
library `Sheaf/Paper/QbarTwistCommonStage.lean` 28.3 s. The installed wrapper
currently requests a server-side overlay; its output identifies temporary
compiled modules under `/dev/shm/nt-tmp/nt-local-compile-0rw07d7v/.lbuild`.
This is fresh overlay/compiler evidence, not an assertion that a separate
local `lcompile.py` run occurred. No global build, direct SSH command, live
Lean write, project-clone edit, or Git mutation was performed by this reader.

Finding and repair: H11, the original second-reading section explicitly
identified itself as the author's self-check. Preserve it as such and add
this independent reading. This complete replacement report is the only fix.
The mathematics, Lean module and node record are accepted without change.
