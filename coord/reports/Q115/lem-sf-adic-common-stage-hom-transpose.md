## Worker report

The delivery states `WeilConjectures.adicCommonStageHomTranspose` in
`Sheaf.Paper.AdicCommonStageHomTranspose`. It contains one theorem, with proof
`sorry`, and no definitions. The natural-language statement, source, proof plan,
and all pre-existing node metadata are unchanged. The item cites the already landed normalized closed and braiding interfaces,
the partial-closed definition owner, and the rational Verdier definition owner.
The rational Verdier and closed-reindexing definition records have lean-only
ownership repairs under section 1(B); no new node or Lean construction is added. All work was written in the assigned sandbox.

Hypotheses and clauses, with the node and Lean read together:

- The global finite-field datum, geometric base field, and prime different from
  its characteristic are `D : FiniteFieldDatum.{u}`, `l : ℕ`, `[Fact l.Prime]`,
  and `hl : l ≠ D.p`. `Ω : Type v` has `Field`, `Algebra (Padic l)`, and
  `IsAlgClosure (Padic l)` instances. The coefficient closure has an independent
  universe. Finite subextensions are `Index l Ω`, with their specified equivalent
  small field models `Coefficient.{u} l Ω E`; no subextensions are excluded.
- The separated finite-type k-scheme is `X : Scheme.{u}` with `X.Over (Spec
  (.of D.k))`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on its
  structure map. `RationalVerdier.units D l hl X` derives invertibility of l
  in every residue field from the base; it is supplied explicitly to tensor and
  closed operations, not imposed as another hypothesis.
- The coefficient paragraph fixes the background, rather than asserting a new
  comparison of ambient categories. The completed sheaf is the existing inverse
  limit from `CompletedIntegralConstantMapOfUniverses`; `CompletedCondensedCoefficients`
  supplies its comparison with pulled-back condensed coefficients and rational
  and algebraic-closure coefficients. The finite-subextension-valued condensed
  ring is the existing `Profinite.padicAlgClCondensedRing`, not all continuous
  functions into the algebraic closure. `ringedSiteModules` and `DerivedCategory`
  supply the stated ambient module categories. Those ambient categories do not
  occur in the claimed source Hom bijection, so no extra ambient equivalence or
  site-perfectness predicate is introduced.
- The finite categories are exactly `sfRationalConstructibleCategory`, the raw
  localization with unchanged integral objects. The source category is exactly
  `generalAlgebraicallyClosedConstructibleCategory`, whose actual Hom groups are
  common-field directed colimits, with the specified completed scalar transitions.
- A permitted pair and its internal Hom are `(commonStageHomPairs l Ω X).FullSubcategory`
  and `(commonStageDerivedInternalHom l Ω X).obj P`. The first conjunct explicitly
  identifies the predicate on arbitrary `M,N` with the existence of `E,hM,hN`
  such that `constructibleRationalHomPairs` holds for their extended objects.
  Thus the witness may lie at any later common field; it need not be the original
  compositum. The latter predicate is exactly constructibility of the completed
  integral Hom of the underlying integral objects, as read in its owning module.
  The converse detection uses finite faithfully flat scalar descent on reductions;
  it does not assume that rational Hom transition maps are injective.
- `S : PodPartialClosed ...` uses the recorded tensor, permitted pair category,
  and coefficient-passage Hom functor. `PodCommonTransposeNormalization ... S`
  fixes its inverse transpose on every common-field representative using the
  actual rational transpose, tensor comparison, Hom comparison, and `ofHom`.
  This is the directed-colimit clause, including its independence of eventual
  equality. It is the existing normalization predicate, not a new chosen map.
  Its owning `podCommonClosed_existsUnique` theorem makes this the already
  specified closed structure; the existential does not permit arbitrary evaluation.
- Right evaluation is `S.evaluation P`, whose source is `H ⊗ M`. The next
  conjunct identifies `(S.transpose L P).symm a` with the exact displayed map
  `tensor.map (Prod.mkHom a (𝟙 P.obj.1.unop)) ≫ S.evaluation P`. The following
  conjunct states `Function.Bijective` for that function itself, for every `L,P`.
- Naturality in `L` and both permitted-pair variables is the simultaneous equation
  for `f : L' ⟶ L` and `g : P ⟶ Q`. The map `g.hom.1.unop` is the contravariant
  input `M' ⟶ M`, while `g.hom.2` is `N ⟶ N'`; the middle map is the actual Hom
  functor's `map g`. Taking identities recovers each separate naturality equation.
- Signed left/right evaluation conversion is the subsequent equation with
  `pullbackTensorCommonBraiding`. This is the existing Koszul braiding, normalized
  to the rational signed braiding at every larger finite field, not an unsigned
  swap. It gives both conventions on every arrow.
- The final conjunct quantifies over every finite coefficient embedding
  `ι : E →ₐ[Padic l] F`. Its first equation is exactly
  `transpose_F (μ.inv ≫ S.map b) = S.map (transpose_E b) ≫ c.hom`, with
  `rationalTensorScalarComparison` and `rationalHomScalarComparison`. `W` is an
  arbitrary constructible target and only `(L,W)` is required to be permitted.
  Its second equation states that the same tensor scalar comparison commutes
  with the signed rational swap. The equations are the existing rational-scalar
  transpose theorem's precise normalization, included in this theorem's conclusion.
- Every test object, pair morphism, and finite pairing ranges over the actual raw
  rational or common-stage Hom type. No restriction to integral, lattice-preserving,
  denominator-free, dualizing-target, or perfect-source arrows appears.

Dependency declarations read and used (module names are the recorded ones):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  coefficient conventions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `ProEt.topology`, the small weakly-etale site and its fpqc covering topology.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the unchanged
  `completedIntegralCoefficientSheafUnrestricted` construction.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, its finite-field-valued subfunctor and
  pointwise ring presheaf.
- `Sheaf.Paper.CompletedCondensedCoefficients`:
  `AlgebraicGeometry.ProEtale.completedCondensedIntegral`,
  `completedCondensedRational`, `completedCondensedAlgebraicClosure`, and
  `completedCondensedPullback`, for the background coefficient identifications.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`;
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `ofHom`, and
  the actual stage-system transitions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory` (the background unbounded derived category).
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleRationalHomPairs`,
  `rationalDerivedTensor`, `rationalDerivedInternalHom`,
  `rationalHomScalarPair`, `rationalHomScalarComparison`,
  `rationalTensorScalarComparison`, `commonStageHomPairs`,
  `commonStageDerivedTensor`, `commonStageDerivedInternalHom`,
  `commonStageHomComparison`, and `commonStageTensorComparison`.
- Definition owner `def-sf-adic-closed-reindexing-maps`, module
  `Sheaf.Paper.DerivedAutomorphismHomEvaluation`:
  `PodCommonTransposeNormalization` and `podCommonClosed`. Its existing:true
  declaration list is extended by this delivery to own `podRationalClosed` and
  `podRationalClosed_existsUnique`, the uniquely characterized rational closed
  datum used in the common normalization. The source also supplies
  `podCommonClosed_existsUnique`, which pins the normalized common datum.
- Definition owner `def-sf-rational-common-tensor-symmetries`, module
  `Sheaf.Paper.DerivedPullbackTensorIso`: `pullbackTensorCommonBraiding`,
  `pullbackTensorRationalBraiding`, and their `_existsUnique` characterizations
  with the full representative normalizations. The two formerly cited theorem
  nodes are removed from statement dependencies.
- Repaired definition owner `def-sf-rational-verdier-data`, module
  `Sheaf.SixFunctors.RationalVerdier`: the existing `RationalVerdier.units`,
  `.tensor`, and `.scalar`, now explicitly included alongside `Datum` and
  `Conclusion` in its existing:true Lean record. The theorem node
  `thm-coef-rational-verdier` is not cited as a statement dependency. No duality
  theorem or dualizing object is assumed.
- Added landed definition owner `def-pod-partial-closed-interfaces`, module
  `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `PodPartialClosed` and
  `PodPartialClosed.evaluation`.
- Proof imports: `Sheaf.Paper.IntegralOperationsScalarComparisons`,
  `Sheaf.Paper.CompletedTensorHomTranspose` (`completedTensorHomTranspose`),
  and `Sheaf.Paper.RationalHomScalarTranspose` (`rationalHomScalar_transpose`).
  All original proof dependency modules are included. There is no dependency path
  back to this item from the cited interface nodes.

Sources checked: BS PDF page 22, Definition 3.4.10 and Lemma 3.4.11 (completed
adjunction for arbitrary first input and complete target); pages 61--62,
Proposition 6.8.14 and Remark 6.8.15 (raw rationalization, finite-field passage,
and the ambient operations). Also read the current blueprint unit
`sec-six-functors-basics/sk-prop-sf-biduality-general/_section.md` and the item's
six-step agent-written normalization argument, which is the source of the actual
common-stage comparison square. No statement correction is needed.

Edge cases checked: zero objects and zero arrows; the empty scheme; identity
coefficient embeddings and repeated fields; a witness strictly larger than the
original compositum; unequal original coefficient fields and the independent
closure universe; arbitrary constructible targets; rational arrows with arbitrary
denominators; equal common-stage arrows whose equality is witnessed only later;
and negative/odd cohomological degrees, where the Koszul sign is necessary.
There is no empty-tail issue: finite composita give a stage for every finite list
of fields. None of these cases adds a perfectness assumption.

Searches for an existing statement, 2026-10-24:

- `msearch.py leanfinder`, query “Evaluation tensor internal Hom transpose
  bijections descend to the directed common finite coefficient stage category”:
  eight results, including `LightCondensed.ihomPoints` and `ModuleCat.ihom_ev_app`;
  none states this completed/rational common-field normalization.
- `msearch.py loogle`, query `"MonoidalClosed", "colimit"`: zero hits.
- `msearch.py grep`, query `commonStage.*(Transpose|Evaluation)|common.stage.*transpose`:
  zero Mathlib hits.
- `msearch.py leansearch`, query “Tensor Hom adjunction evaluation bijections on
  a common stage filtered colimit category of constructible adic sheaves”:
  eight results, including `ModuleCat.monoidalClosedHomEquiv` and functor-category
  adjunctions; none is this statement on the raw rational/common-stage categories.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, for the item id and
  `commonStage.*(Transpose|Evaluation)|common.stage.*transpose`: the item is cited
  in consumers' proof docstrings. `DerivedAutomorphismHomEvaluation` already
  supplies partial closed data and its representative normalization, which are
  reused here. It does not bundle this item's arbitrary finite witness domain,
  all three naturalities and explicit arbitrary-target scalar/signed equations.
  Further source searches located and reused the existing signed braidings and
  normalized finite rational transpose; no private copy of a notion was needed.

Validation: the first `scompile.py` run accepted both sandbox and library module
modes, with only two long-line warnings. Those lines have been wrapped. The final
compile, server preflight, and delivery dry-run results are recorded below.

Final validation: `deliver2.py Q115 lem-sf-adic-common-stage-hom-transpose
--no-push` printed `OK (dry run): commit f9f6adb0e94 passes the preflight and
compiles; nothing pushed`. Its per-file sandbox and library compiles were clean,
with no warnings. The copied node's `lean.statement` was checked byte-for-byte
against the final theorem signature, every source line is at most 100 characters,
and the only postponed proof is the theorem's whole `by sorry` proof.


## Dependency modules

`def-sf-rational-verdier-data`: lean-only repair of an existing:true dependency
record, using the alternative explicitly authorized in the return. The previous
record listed only `WeilConjectures.RationalVerdier.Datum` and `.Conclusion`, so
it did not own the plain `.units`, `.tensor`, and `.scalar` definitions used in
the consumer statement. The extended record retains both original declarations
and adds exactly these three published helpers from the same module. The primary
structure signature stays verbatim. No dependency module is written or altered;
the original source declarations and their docstrings are reused. All other
fields of this dependency node are identical to current main.

`def-sf-adic-closed-reindexing-maps`: lean-only section 1(B) extension of its
existing:true declaration record. Its existing `PodCommonTransposeNormalization`
uses the choose-defined rational closed datum, but the record omitted ownership
of `WeilConjectures.podRationalClosed` and
`WeilConjectures.podRationalClosed_existsUnique`. Both published declarations
are now included, exactly as the return requests. I read their complete
signatures and docstrings at `DerivedAutomorphismHomEvaluation.lean:307-339`:
the existence-and-uniqueness theorem characterizes the inverse transpose of the
partial closed structure by the localized integral transpose on every pure
tensor representative. The definition chooses that unique structure. This is
not a choice from an undetermined existence assertion. All other dependency
fields and every Lean source file are unchanged.

## Repair of returned head a97424933e00

H2 is repaired by replacing `thm-coef-rational-verdier` in the item's statement
dependencies with `def-sf-rational-verdier-data` and extending that definition's
existing:true Lean declaration list as requested. `RationalVerdier.units` is the
actual residue-field inverse obtained by mapping `finiteFieldDatumPrimeUnit`
along the structure map, `.tensor` is the transparent abbreviation of the
specified `rationalDerivedTensor`, and `.scalar` is the transparent abbreviation
of `sfRationalScalarExtension` with characteristic parameter zero. I reread all
three full source definitions and docstrings. This changes their definition-node
ownership, not their meaning, hypotheses, or comparison maps. The optional
`def-pod-partial-closed-interfaces` citation is also added; the two genuine
choose-object theorem dependencies were retained in that first repair and are
replaced by their definition owners in the repair below.

The retained sandbox was compared with the returned record and current main:
the item's natural-language statement is identical; the Lean source and signature
are byte-for-byte those reviewed at a97424933e00. The item copy was refreshed
from current main while preserving only its authorized `stmt_deps`/`lean` delta.
The dependency copy changes only `lean`. The delivery wrapper builds the repair
on current origin/sheaf-dag. All clause mappings and edge-case checks in the
worker report still apply. No independent second reader was started: the brief
requires direct worker delivery and maintainer independent review.

Repair validation, 2026-10-25: `scompile.py` accepted the retained statement in
sandbox and library module modes without warnings. `deliver2.py --no-push`
compiled both the statement and the exact existing-declaration probe for the
extended definition owner, then printed `OK (dry run): commit 437c8a53ebd passes
the preflight and compiles; nothing pushed`. Checks confirm that the dependency
copy changes only `lean`, the item changes only `stmt_deps` and `lean`, its
recorded signature exactly matches the Lean file, and neither added definition
dependency introduces a path back to this item.


## Repair of returned head 706ac052572a

1. Replaced `lem-pod-derived-automorphism-hom-evaluation` in `stmt_deps` with
   `def-sf-adic-closed-reindexing-maps`, the existing definition owner of the
   normalized common closed interface.
2. Replaced `lem-pur-derived-pullback-tensor-iso` with the landed definition
   owner `def-sf-rational-common-tensor-symmetries`; its existing record owns
   both rational/common braidings and their unique characterizations.
3. Extended the existing:true record of `def-sf-adic-closed-reindexing-maps`
   under section 1(B) with `WeilConjectures.podRationalClosed` and
   `WeilConjectures.podRationalClosed_existsUnique`. The dependency copy changes
   only `lean`. No new module or duplicate construction is introduced.
4. The Lean source is byte-for-byte unchanged from the reviewed delivery,
   SHA256 `6ef7d16d3031ad408b373e78034bce60f74dacfbef5b73a92f3878395a58e4a6`.
   The dependency list above now records the definition owners actually cited.

The retained item and dependency records were refreshed against current main.
The item changes only `stmt_deps` and `lean`; both dependency copies change only
`lean`. The natural-language statement, proof plan, and every mathematical clause
are unchanged. Neither replacement dependency has a path back to the item in
the locally available DAG. `scompile.py` accepted the unchanged statement in
sandbox and library module modes without warnings (132.0 s and 17.9 s).

Repair validation for returned head 706ac052572a: `deliver2.py --no-push`
compiled both the unchanged statement and the existing-declaration probe for
both extended definition records without warnings. It printed
`OK (dry run): commit d9529aa98a1 passes the preflight and compiles; nothing pushed`.
All three node JSON files retain indent 1, ensure_ascii false, and final newlines.

## Second reading by Q115

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
