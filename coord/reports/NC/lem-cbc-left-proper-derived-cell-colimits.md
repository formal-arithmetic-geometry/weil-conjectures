## Worker report

This delivery states `HomotopicalAlgebra.leftProperDerivedCellColimits` in
`Sheaf.CategoryTheory.LeftProperDerivedCellColimits`. Its sole postponed theorem has
proof `sorry`; the docstring supplies all eight proof steps from the current DAG.
The three helpers contain real data and only package the comparison maps and conclusions
of this node. No new nodes or dependency modules are needed, and the statement is unchanged.

The route note concerned the stage-1 split. The available sandbox contained only four brief
markers, not a retained Lean candidate. I independently read the current split (including
all eight steps), all statement dependencies and their recorded modules and docstrings,
and wrote this stage-2 candidate. I do not claim a second reading of my own work.

### Hypothesis and clause correspondence

- The size convention is explicit in `universe u v w z t`: `M : Type u` has
  `Category.{v} M`, small ordinal diagrams have `J : Type v`, and the coherent localization
  lives in `SSet.{max u v t}`. These are the same index-size conventions as
  `modelColimitLocalizationComparison`; `t` allows enlarging the localization universe.
- A complete and cocomplete model category is `[ModelCategory M] [HasLimits M]
  [HasColimits M]`, with the existing model classes and weak factorization systems.
- Combinatorial, including functorial factorizations, is exactly
  `_hM : CombinatorialModelCategory.{u, v, w} M`. I read its five fields in the recorded
  module: local presentability, the two set-generated lifting classes and the two
  functorial factorizations. No new combinatorial predicate or extra choice is used.
- Left properness is `_leftProper`: for every weak equivalence `e : A ⟶ B` and cofibration
  `i : A ⟶ X`, `pushout.inr e i : X ⟶ pushout e i` is weak. This is exactly pushout of
  a weak equivalence along a cofibration, with arbitrary original objects.
- The chosen coherent localization is `(C, q, _hq)`, using the recorded
  `FiniteReedy.IsLocalization`. Its definition includes quasicategory structure,
  inversion of weak equivalences and the universal property on full functor infinity
  categories. These parameters specify the meaning of `Map^h` rather than impose a
  mathematical extra assumption: the projective comparison dependency gives their
  existence and the conclusion applies to any such presentation.
- Clause (a) uses `span i j` for the displayed `B ← A → X`, with only `Cofibration i`.
  The other leg `j` is arbitrary. An arbitrary cocone `s` with `IsColimit s` is its
  ordinary pushout with its actual legs. This includes the chosen `pushout i j` and
  is equivalent to using that choice, by uniqueness of colimits.
- Clause (a), ordinary versus model homotopy pushout: `CellColimitComparison (span i j) s`.
  This quantifies over every projective `S`, whose weak equivalences and fibrations
  are the actual objectwise classes, and every objectwise weak replacement `a : Q ⟶ D`
  whose source is projectively cofibrant. The cofibrancy condition is the recorded
  `S.categoryWithCofibrations.cofibrations (initial.to Q)`. For every colimit cocone `c`
  and proof `hc`, it concludes `WeakEquivalence (cellColimitComparison a s c hc)`.
  This comparison is constructed by `hc.desc` on the genuine composite cocone
  `a ≫ s.ι`; thus its equations are `c.ι.app i ≫ comparison = a.app i ≫ s.ι.app i`.
  It is never an arbitrary weak equivalence of the two apices. The replacement is
  permitted to be objectwise weak with cofibrant source, exactly as in the dependency;
  requiring it to be a trivial fibration would be an unnecessary restriction.
- Clause (a), mapping spaces: `CellMappingComparison q (span i j) s`. This is the
  canonical coherent-cocone formulation of the displayed homotopy-pullback comparison.
  Its witness `μ` lies in the actual `coconeCategory (FiniteReedy.diagram q D)`.
  The two equations fix its apex to `q(s.pt)` and its ENTIRE arrow simplex to the
  nerve image of `s.ι`. Every restriction map and its coherence is thereby retained.
  The final universal quantifier is `∀ Z : M, IsFibrant Z → ...`, in the original model.
  There is no cofibrancy assumption on any of `A`, `B`, `X`, `s.pt` or `Z`.
- More explicitly, the existing cocone mapping-space formula represents precomposition
  along `μ` by a canonical span `Map_C(q(s.pt),qZ) ← T → R`. The left arrow is the
  canonical weak equivalence of `CalculusTransportFormula`, using the recorded pinch
  comparison, and the right arrow is exactly the existing `calculusTransportValue`
  used in `CellMappingComparison`. `CalculusCommaFiberIdentification` canonically
  identifies `R` with `Map_Fun(N(I),C)(qD,const(qZ))`. This is the space of coherent
  compatible maps, namely `lim_(I.op) Map_C(qD(i),qZ)`. Hence asserting that this right
  leg is weak is exactly asserting that the canonical comparison is an equivalence
  of spaces. It does not assert merely an abstract equivalence between some objects.
  For `WalkingSpan.op` that limit is the displayed homotopy pullback. The recorded
  cosimplicial-frame mapping theorem identifies these localization mapping spaces
  naturally with the node's homotopy function complexes, including for noncofibrant
  inputs after replacement. This representation uses the original canonical cocone,
  so it also fixes the canonical comparison, not just its homotopy type.
- Clause (b), small nonzero limit ordinal: `(J : Type v) [LinearOrder J]
  [WellFoundedLT J] [Nonempty J] [NoMaxOrder J]`. A small linearly well-ordered type
  has an ordinal order type; it is nonzero precisely when nonempty, and is a limit
  precisely when it has no greatest element. Conversely every small nonzero limit
  ordinal has such a small order presentation. Thus this representation is exact,
  without a countability or regular-cofinality assumption and without choosing an
  order isomorphism inside the statement.
- The diagram is `D : J ⥤ M`. Its maps are cofibrations via
  `∀ (a b : J) (h : a ≤ b), Cofibration (D.map (homOfLE h))`. Identities add no
  restriction since they are always cofibrations. There is no condition on `X_0`.
- Continuity is precisely Mathlib's `D.IsWellOrderContinuous`. I read its definition:
  at every `Order.IsSuccLimit m`, the GIVEN cocone from the strict initial segment
  has an `IsColimit`. Here `IsSuccLimit` excludes the least element, so this does not
  impose an initial-object condition on `X_0`.
- Clause (b), ordinary colimit computes model homotopy colimit: for every actual
  colimit cocone `s`, the conclusion is the same `CellColimitComparison D s`, with
  the same replacement-to-cocone map. The projective model structure exists by the
  recorded dependency, so the quantifier over it is not vacuous.
- Clause (b), homotopy limit of mapping spaces: `CellMappingComparison q D s` is the
  same canonical mapping-space assertion described above, now with the genuine
  coherent ordinal diagram. The space of compatible maps is the limit over `J.op`;
  it retains restrictions and all their coherent compositions, not just the product
  of mapping spaces. The test objects again satisfy the original `IsFibrant Z` only.
- No `SimplicialCategory M`, tensor, cotensor or other enrichment is a binder.

### Dependency declarations

- `def-weil-size-convention`: its recorded `convention: true` has no Lean declaration;
  it is rendered through the explicit universe parameters above.
- `lem-coef-model-colimit-localization-comparison`:
  `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`,
  `HomotopicalAlgebra.CombinatorialModelCategory` and
  `HomotopicalAlgebra.modelColimitLocalizationComparison`. The full recorded signature
  and docstring were read. It provides projective structures and coherent localization;
  its `FiniteReedy` imports provide `largeNerve`, `IsLocalization`, `diagram`,
  `transformation` and `object`, read in the owning source.
- `lem-coef-combinatorial-localization-presentability`:
  `Sheaf.CategoryTheory.CombinatorialLocalizationPresentability`,
  `HomotopicalAlgebra.ModelLocalization.combinatorialLocalizationPresentability`.
  The statement uses the exact shared `CombinatorialModelCategory` imported there;
  it does not repeat or assume this theorem's presentability conclusion.
- `lem-coef-cosimplicial-frame-mapping`:
  `Sheaf.CategoryTheory.CosimplicialFrameMapping`,
  `CategoryTheory.cosimplicial_frame_mapping` and `CosimplicialFrameMappingData`.
  I read the comparison and naturality fields as well as the full theorem signature;
  these identify the coherent mapping spaces with `Map^h` without enrichment.
- Added already-landed statement dependency `lem-cbc-enhanced-functor-cone-calculus`:
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`,
  `SSet.Enhanced.calculusApex`, `calculusTransportValue`, `calculusTransport`,
  `CalculusTransportFormula`, `CalculusCommaFiberIdentification` and
  `enhanced_functor_cone_calculus`. These are the canonical comparison span and its
  endpoint normalization, not a private replacement for that interface.
- Proof dependency `def-weil-pbc-category-colimit`:
  `Mathlib.CategoryTheory.Limits.HasLimits`, `Cocone`, `IsColimit` and `IsColimit.desc`.
  Imported explicitly. The helpers use this actual universal property.
- Proof dependency `lem-coef-lifting-class-closure`: its status is `mathlib` and its
  `mathlib_match` records `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`,
  `llp_isStableUnderRetracts`, `rlp_isStableUnderRetracts`,
  `llp_isStableUnderCobaseChange` and `llp_isMultiplicative`. Read and imported.
- `Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous` supplies the
  existing `CategoryTheory.Functor.IsWellOrderContinuous`; no duplicate is introduced.
- `lem-coef-infinity-yoneda-presheaf-limits` is only a proof dependency and has no
  recorded declaration on the current base, so it contributes no import. Its full
  statement was read and its mapping-out formula is recorded in proof step 8.
  No unstated prerequisite is used as data by this signature.

### Edge cases and mathematical checks

Checked the identity cofibration `A → A`: the pushout is `X`, and the mapping comparison
reduces to the identity pullback formula. Checked initial `A`: coproducts are computed
by the same statement without asserting `B` or `X` cofibrant. The arbitrary second leg
includes noncofibrations. Noncofibrant initial objects are explicitly permitted.

For the chain checked order type omega, omega+omega (including the inner limit at omega),
a constant chain on a noncofibrant object, and a small limit of uncountable cofinality.
Continuity uses the actual strict-initial-segment cocone. The empty order is excluded
by `Nonempty`, and successor ordinals by `NoMaxOrder`, exactly as the statement requires.
No zero-stage colimit is demanded. Fibrant test objects can have empty mapping spaces;
no vertex or chosen basepoint is introduced.

Checked relative Brown in the proof plan: the map `(w,1)` is defined under `K`, both
coprojections are cofibrations, and the split identity `p s=1` gives the colimit weak
equivalence of `p` before using `p i=w`. Both uses of left properness in step 4 are along
cofibrations. Transfinite lifting uses continuity of `D` at limits, never a false claim
that arbitrary transfinite colimits preserve weak equivalences.

Read Barwick's actual online PDF, Theorem 4.7 proof on printed pp. 43--44. It supplies
the left-proper pushout observation and the transfinite-composition input. The current
node expands the latter into the stronger precise continuous-cell comparison via its
eight-step argument; this expansion, rather than an assertion of a verbatim theorem
in the PDF, is followed in the Lean docstring. No statement fault or dispute found.

### Searches made

- `msearch.py`, LeanSearch: “A continuous transfinite composition of cofibrations
  in a left proper model category computes a homotopy colimit without cofibrant
  initial objects”. Eight hits concerning ordinary relative cell complexes and
  transfinite compositions, their colimit cocones and morphism-property closure.
  None states the derived comparison or the mapping-space formula.
- `msearch.py`, LeanFinder: “In a left proper model category pushouts along cofibrations
  and continuous transfinite cofibration chains are homotopy colimits without cofibrant
  initial objects”. Eight hits: Joyal trick, finite colimits, cylinder composition,
  cobase change of trivial cofibrations, coproduct lifting and cofibrant objects.
  None is the homotopy-colimit or mapping-space comparison.
- `msearch.py`, Loogle: `HomotopicalAlgebra.ModelCategory, pushout` returned no hits and
  reported an unqualified-name diagnostic. Retried with `"HomotopicalAlgebra", "pushout"`:
  two hits, `AttachCells.pushouts_coproducts` and `AttachCells.isPushout`, both ordinary
  cell-pushout statements, not this result.
- `msearch.py`, grep: `homotopy[Cc]olimit|homotopy[Pp]ushout|[Ll]eft[Pp]roper`:
  zero Mathlib hits.
- `rg` over the upstream `WeilConjectures` and project `lean/Sheaf` for
  `left.proper.*(colimit|pushout)|homotopy.*colimit.*cofibration|leftProperDerivedCell`:
  only the project Bergner left-properness module and a caller mentioning it; no
  general derived-cell-colimit statement. A literal item-id search upstream returned
  no hit. Broader project colimit/mapping searches led to the reused interfaces above.
- Exact-name search over Mathlib, upstream and project for `CellColimitComparison`,
  `CellMappingComparison`, `cellColimitComparison`, `leftProperDerivedCellColimits`:
  no collision. The helpers package this node's conclusions and are listed in
  `lean.declarations`; they are not independent new mathematical notions.
- `scompile.py --source Sheaf.CategoryTheory.LeftProperDerivedCellColimits` confirmed
  that no preexisting candidate source was available in the live library.

### Validation

`scompile.py NC lem-cbc-left-proper-derived-cell-colimits` compiled the sandbox and
library form of the module successfully, in 2.3 and 1.9 seconds respectively, without
errors or warnings. An explicit proof-only colimit import was subsequently added;
the delivery dry run recompiled the final module and passed server preflight.
The successful dry run printed `OK` for commit `8e9d816145`, with exactly the module,
item node and report staged. The final report also records the additional LeanSearch
query above; the prescribed dry run is repeated before delivery.

## Second reading by NC

No second reading by a worker: the current brief requires direct delivery followed by
the maintainer's independent review. This author does not manufacture another reader's
signature. The Q130 second reading in the route note belongs to the earlier stage-1 split.
