## Worker report

The module `Sheaf.Paper.LisseCohomologyDerivedDual` states the evaluation-normalized
cohomology-duality assertion on the literal raw rationalized and common-stage categories.
No statement correction, dependency repair, or new independent notion/node is needed.
The two postponed theorems are `WeilConjectures.LisseCohomologyDual.lisseCohomologyDerivedDual`
and its explicit final Weil-equation clause `WeilConjectures.LisseCohomologyDual.weil_equation`.
Both belong to this node; every other declaration constructs actual composites or packages
this node's clauses. Both docstrings contain the natural-language proof.

Hypotheses and conclusions, one by one:

- The finite field, algebraic closure k, and q are the existing `FiniteFieldDatum D`.
  The prime is `l : ℕ` with `[Fact l.Prime]`, and unequal characteristic is `hl : l ≠ D.p`.
- A finite coefficient field is `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]`. This permits every finite subfield of the fixed closure,
  as well as an isomorphic coefficient model. No global lattice, basis, or integral
  splitting is assumed. The common-stage clause permits `Ω : Type v` independently,
  with `[Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`.
- `X : LisseRealization.Base D l hl` carries exactly a finite-type k-scheme: its
  `scheme`, `over`, `finiteType`, and `quasiCompact` fields. The separate
  `[IsSeparated (X.scheme ↘ Spec (.of D.k))]` retains the node's separation condition.
  The recorded `baseInvertible` supplies coefficient invertibility; no new assumption
  about residue characteristic or universe equality is imposed.
- `rational D l hl E X` uses `sfRationalConstructibleCategory`,
  `sfRationalStandardTStructure`, `rationalDerivedTensor`,
  `constructibleRationalHomPairs`, `rationalDerivedInternalHom`, `podRationalClosed`,
  `pullbackTensorRationalUnit`, and `rationalLisseHeartProperty` literally.
  `common D l hl Ω X` uses the existing general finite-stage pair carrier,
  `sfCommonStageStandardTStructure`, the common-stage tensor/Hom/pair predicate,
  `podCommonClosed`, the existing common-stage unit, and the intersection of
  `sfCommonStageHeartProperty` with `IsCommonStageLisse`. No envelope is taken.
  The carrier is the same one reexported by `intrinsicPbcQbarCategory`; no arbitrary
  category or discrete rational coefficient sheaf is substituted.
- For any object K, `LisseCohomology A K` is the universal integer-degree condition
  that its cohomology is in the recorded lisse heart. The only other premise of
  `Family.comparison` is `hK : A.permitted (op K,A.unit)`, exactly constructibility
  of its actual coefficient dual. Boundedness is inherent in the category.
- Write Q_i K = tau GE i (tau LE i K). `piece A i` is precisely this composite,
  with Q_i K = H^i(K)[-i]. `Comparison.iso i` asserts the derived isomorphism
  Q_{-i}(D K) ≅ D(Q_i K). Its `target_bounds` puts the latter in the single degree -i.
  Both sides shifted by -i give H^{-i}(D K) ≅ D(H^i K), concentrated in degree zero;
  finite-projective heart calculation and the recorded lisse realization identify
  this with the ordinary sheaf Hom in the node. `Comparison.sheafIso` is explicitly
  the image of this derived isomorphism under that shift. This is an isomorphism of
  derived objects, not merely an assertion about groups or stalks. The ordinary
  dual is expressed intrinsically by the actual RHom of the single-degree object,
  with its degree bound, rather than defining a second sheaf dual.
- `Comparison.evaluation` fixes the actual arrow: restrict DK⊗K evaluation along
  tau LE(-i)DK and tau LE i K, then factor through the two canonical tau GE quotients.
  The resulting pairing is evaluation after `Comparison.iso`. `Comparison.unique`
  makes this the unique map with that equation. Thus an arbitrary endpoint
  isomorphism or an arbitrary family of pairings cannot satisfy the package.
- `Family.naturality` is the contravariant square for every morphism K→L satisfying
  the two domain conditions at its endpoints, including arbitrary fractional and
  common-stage morphisms. `dualMap` is the actual Hom functor on `(f.op,1)`.
- The first and third conjuncts of the main theorem quantify over every scheme
  isomorphism X≅Y, without a k-linearity premise. `Transport` fixes the cohomology
  comparisons through the canonical truncation unit/counit equations, and fixes
  dual transport through the evaluation equation with the actual
  `canonicalRationalPullbackTensor` or `canonicalCommonStagePullbackTensor`.
  Its `dual_naturality` is the full square for every map between permitted dual inputs.
  Its unit comparison is a conclusion and normalized by the left-unitor square.
  `Compatible` is the full commuting duality/cohomology square, including the dual
  of the cohomology comparison on its target side.
- The second conjunct uses exactly `sfRationalScalarExtension`,
  `rationalTensorScalarComparison`, and `pullbackTensorRationalScalarUnit` for any
  finite coefficient extension `ι : E →ₐ[ℚ_[l]] L`. Identity and tower cases are
  included. The normalized transport equations determine its dual comparison as
  the evaluation transpose, so it is the specified comparison of
  `lem-zl-specified-hom-scalar-evaluation`, not an unrelated isomorphism.
- The fourth conjunct gives the same square under each actual finite-stage
  inclusion into the common-stage category. Its tensor/unit comparisons are
  natural, unit-normalized conclusion data, and its Hom comparison is fixed by
  evaluation. The normalization of the actual common-stage operations ensures
  these are their common-stage comparisons. This explicitly relates the finite
  and common families rather than selecting unrelated comparisons on them.
- `weil_equation` writes the exact square for a fixed-pair structure theta:F K≅K.
  Substituting either recorded Frobenius pullback functor specializes it to
  `sfWeilComplex` or `sfCommonStageWeilComplex`. The source structure is induced by
  D(theta^{-1}) after pullback-of-dual transport; on cohomology the target structure
  is the dual of the inverse of Q_i(theta) composed with the canonical cohomology
  pullback comparison. This is explicitly the contragredient convention. `hp`
  is the compatibility conclusion of the main theorem; the auxiliary theorem
  states the formal final clause on that conclusion, with no new mathematical
  hypothesis on a Weil complex. No derived category of Weil sheaves is used.

Dependency declarations read and used:

- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory` and its
  inherited raw-localization category, shift, preadditive, and triangulated instances.
- `Sheaf.Paper.IntrinsicQbarCategory`: `intrinsicPbcQbarCategory`, reexporting the
  literal `generalAlgebraicallyClosedConstructibleCategory` and its finite stages.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the rational/common-stage pair predicates,
  tensors, Hom and pullback functors, rational tensor-scalar comparison.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors` give the ordinary
  representative interpretation of the standard cohomology sheaves.
- `Sheaf.Paper.LisseRationalRealization`: `lisse_rational_realization`, with the
  published `LisseRealization.Base`, `rationalLisseHeartProperty`, and
  `IsCommonStageLisse` interfaces reexported by its data modules.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfCommonStageWeilComplex` and
  their actual Frobenius-pullback functors, read as fixed pairs in the above carriers.
- `Sheaf.Paper.ConstructibleTruncations`: canonical truncation-cohomology convention;
  `sfRationalStandardTStructure` and `sfCommonStageStandardTStructure` are the unique
  standard choices reexported there.
- `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `PodPartialClosed`,
  `podRationalClosed`, `podCommonClosed`, and their `evaluation`; the tensor/unit
  operations and canonical comparisons are reexported by its dependency closure.
- Every recorded proof dependency is imported, with plain imports when it serves
  only the eventual proof (including `SpecifiedHomScalarEvaluation`).

Edge cases checked before and during writing: K=0; a zero cohomology sheaf; rank zero;
the empty scheme; varying local ranks; i=0; negative i; i outside either end of the
finite support; identity isomorphism; non-k-linear isomorphisms such as geometric
Frobenius; identity finite coefficient extension; arbitrary finite extension and tower;
objects with local rational free models but no global integral lisse lattice. The
truncation/shift convention gives Q_i K=H^i(K)[-i], so the target dual is in degree
-i and shifting by -i places it in the heart, including i negative. The common-stage
closure has an independent universe v; no scheme/coefficient universe equality is added.

Searches made:

- msearch LeanFinder, "cohomology of derived dual of a complex with locally free
  cohomology sheaves": eight sheaf-cohomology / Hom-complex hits, no matching theorem.
- msearch Loogle, `DerivedCategory.homologyFunctor, SheafOfModules.homObj`: no hits;
  Loogle reported unknown identifier for the project-specific sheaf Hom.
- msearch grep of Mathlib Algebra/Homology,
  `homology.*[Dd]ual|[Dd]ual.*homology|[Cc]ohomology.*[Dd]ual`: four documentation
  hits about dualizing homology constructions, no coefficient-dual theorem.
- msearch LeanSearch, "cohomology sheaves of derived internal Hom dual of a bounded
  complex with locally free cohomology": eight generic sheaf Hom, free-module Hom,
  Ext and Hom-complex hits; no matching assertion.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for lisse/dual/cohomology combinations,
  the node ID, and chosen declaration names. Found finite-field internal Hom with
  a degree-zero lisse first argument, scheme O_X homology evaluation, and Verdier
  duality in a different category; none supplies this node's two coefficient
  conventions and normalized naturality clauses. The final names have no collision.

Validation: prescribed scompile.py compiled the complete module in both sandbox and
library module modes, cleanly (only expected sorry warnings are suppressed by the tool),
with the final major version taking 25.3 / 20.0 seconds, below the fixed 60-second limit.
No local/global build or direct repository/git mutation was run.

## Second reading by Q32

This is a second self-reading, not an independent-agent review: the dispatch brief
explicitly prohibits starting another agent and assigns independent review to the
maintainer. I reopened the node and the complete delivered module. The main check was
the degree convention: using the truncation piece without its shift would not literally
name the degree-zero sheaf. The module therefore states the derived piece isomorphism,
records its degree bounds, and supplies `Comparison.sheafIso` by shifting both sides by
-i. The evaluation quotient equation ensures this is the canonical comparison. I checked
that hK is exactly membership of the actual Hom pair and that lisse is checked on every
shifted piece, not on the original complex only. I replaced a quantified arbitrary unit
isomorphism by an existential conclusion with its unit-normalization equation, so pullback
compatibility has no added premise. I included the finite-stage inclusion square so the
common-stage family is related to the finite-stage family. The final equation uses
theta.inv in the coefficient dual and the inverse of Q_i(theta) on the ordinary-dual side;
using theta.hom there would reverse the Weil variance. Every hypothesis and clause is
mapped above; no disputed statement or source correction was found.

Final transport audit: made the dual comparison natural explicitly in `Transport.dual_naturality`,
so the formal Weil equation uses only recorded structure fields, even at its abstract level.
