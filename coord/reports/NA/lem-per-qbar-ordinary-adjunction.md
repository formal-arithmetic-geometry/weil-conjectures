## Worker report

Repair of the returned immutable head e5b4e9e8157e, retaining the saved Lean work
and completing its normalization and records. The sole delivered module is
`Sheaf.Paper.QbarOrdinaryAdjunction`; its sole theorem is
`AlgebraicGeometry.Scheme.PerAdic.qbarOrdinaryAdjunction`, with proof `sorry`.
The mathematical statement, proof, proof_deps and other non-Lean item fields
are unchanged. The item gains only the two definition dependencies described below.

The initial required dry run of the saved packet failed at `adj.CommShift ℤ`:
it could not synthesize a shift instance for `pbcQbarCompletedPull`. The saved
shift repair bound its witness to `(pbcQbarPullFamily l Ω f).functor`. The repaired
signature consistently uses that functor, which is exactly the body of the
recorded `pbcQbarCompletedPull`, with the same category instances. The resulting
file passed both sandbox and library compilation through scompile.py.

Returned points:

- R1: dropped the change to `def-weil-pbc-qbar-category` entirely. No copy of that
  node is delivered. NM's landed `Sheaf.Paper.IntrinsicQbarCategory` record and
  its eight declarations remain owned exactly as on current main. The theorem
  publicly imports that module, whose public imports retain the literal legacy
  `pbcQbarCategory` interface used by the completed-pullback dependency.
- R2: replaced the two extra theorem statement dependencies by new existing:true
  definition nodes `def-per-adic-base-stages` and
  `def-per-rational-direct-image-family`. They record definitions in the unchanged
  `AdicHeartPullbackFibres` and `PbcDescentFunctors` modules. No theorem about an
  adic heart or about exact descent is used as a definition dependency. In
  particular, the comparison choice in `PbcDirectImageBetaSpec` belongs to
  `pbcScalarDirectImage_rational`, not to `pbcDescentFunctors`.
- R3: the shift witnesses are now pinned by a chain of specified comparisons.
  `ip` and `ir` equal the actual integral restrictions. `ep` and `er` identify
  them with the actual ambient operations, and `qp` and `qr` identify their
  raw localizations with the finite-stage operations. Their components are
  required to be heterogeneous identities, so these are the canonical comparisons,
  not freely chosen isomorphisms. All four must commute with shifts. Finally,
  the canonical `ιCompFunctorIso E` comparisons must commute with shifts and
  `(a E).CommShift ℤ` is required at every finite stage. Thus the finite shifts
  are fixed by the ambient shifts, and the descended shifts by those finite shifts.
  Choosing a right-adjoint shift structure freely cannot discharge these clauses.
- Advisory: also normalized `a E`. The integral adjunction `ai E` satisfies the
  transpose formula with `pbcActualDerivedAdjunction` and the actual completed
  pullback unit; a second equation identifies `a E` with its localization via
  `qp` and `qr`. This is the normalization of the recorded rational direct-image
  realization, rather than an arbitrary adjunction structure on the same functors.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

1. A field is `(k : Type u) [Field k]`. The coefficient prime and its invertibility
   are `(l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]`. Characteristic zero remains
   allowed. `(Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]` is
   the chosen algebraic closure, in an independent coefficient universe.
2. `X Y : Base k` supplies schemes over Spec k with separated, locally finite-type
   and quasi-compact structure maps, exactly separated finite-type k-schemes.
   `f : X.scheme ⟶ Y.scheme`, `f.IsOver`, `IsSeparated`, `LocallyOfFiniteType` and
   `QuasiCompact` impose exactly the stated separated finite-type k-morphism.
   There is no properness, smoothness, finite-field or nonemptiness hypothesis.
3. The categories are the recorded raw finite coefficient stages and their actual
   pair-category quotient, through `stages` and `inclusion`. The completed pullback
   is `(pbcQbarPullFamily l Ω f).functor`, definitionally the recorded
   `pbcQbarCompletedPull`. No replacement category or Karoubi envelope is introduced.
4. The existential `pres` concludes that the actual integral direct image preserves
   bounded constructible complete objects. It is a conclusion, not an extra
   assumption. `Rf : StageSystem.Morphism ...` gives its descent. The equations
   `Rf.Φ E = pbcDescentDirectImage ...` fix each finite operation to the actual
   integral restriction followed by raw rationalization. `PbcDirectImageBetaSpec`
   fixes its scalar comparisons to the canonical localized mate on integral objects.
5. `a E` and `adj` give the finite-stage and pair-category natural Hom bijections.
   Naturality in both arguments is part of Mathlib's `Adjunction`. The integral
   transpose and localization equations above pin their canonical normalization.
6. The first displayed equation with `E F h A B w` says precisely
   `h_F(betaPull.inv ≫ T_X(w)) = T_Y(h_E(w)) ≫ betaPush.hom`.
   All finite field extensions, repeated fields and towers are included. The
   inverse formula follows from these bijections. Units and counits are adjuncts
   of identities, so this also gives their scalar compatibility.
7. The next equation says that `adj.homEquiv` is the inclusion of each finite
   `a E`. Every Hom class has a common-stage representative, so this is the
   descended bijection on the whole pair category.
8. `Additive` for both functors and `IsTriangulated` with the normalized `sP` and
   `sR` state exactness for the recorded common-stage distinguished triangles.
   `NatTrans.CommShift` of `ep`, `er`, `qp`, `qr` and the two inclusion comparisons
   pins those shift structures to the actual finite operations. `(a E).CommShift`
   and `adj.CommShift ℤ` state compatibility of the adjunctions' unit and counit
   with every integer shift using those structures. These clauses render the
   source's shift compatibility, without choosing the right shift from `adj`.

Declarations and signatures inspected and reused:

- `Sheaf.Paper.AdicHeartPullbackFibres`: `PerAdic.Base`, `baseNoetherian`,
  `baseDimension`, `basePrimeUnit`, `stages`, `inclusion`; now explicitly recorded
  by `def-per-adic-base-stages`.
- `Sheaf.Paper.PbcDescentFunctors`: `pbcDescentDirectImage`,
  `PbcDirectImageBetaSpec`; now explicitly recorded by
  `def-per-rational-direct-image-family`. Its definitions are unchanged.
- `Sheaf.Paper.PbcQbarCompletedPullback`: `pbcQbarIntegralPull_mem`,
  `pbcQbarPullFamily_existsUnique`, `pbcQbarPullFamily`, `pbcQbarCompletedPull`.
- `Sheaf.Paper.IntrinsicQbarCategory`: its public retention of
  `Sheaf.Paper.PbcQbarCategory`, including `pbcQbarCategory`, its scalar action,
  linear structure and common-stage triangulation. Its record is not overwritten.
- `Sheaf.Paper.SfCommonStageDirectImage`: the recorded finite-field model is not
  used on arbitrary k. Its retained integral construction and the actual
  `pbcActualDerivedPush` supply the integral part used here, with the rational
  realization node identifying the resulting ordinary operation.
- `Sheaf.Paper.PbcCompletedPullbackActual`: the actual derived adjunction,
  completed pullback, completed unit, and canonical ambient shift instances.
- `Sheaf.Paper.RationalDirectImageRealization`: `Comparison.integral_transpose`
  and the localized unit/counit specifications justify the canonical normalization.
- `WeilConjectures.CategoryTheory.StageSystem.Functor`: `Morphism`, `functor`,
  `β`, `ιCompFunctorIso`; the beta-conjugated representative maps are the actual
  pair-category quotient maps. The framework source was read in the side checkout.
- `Mathlib.CategoryTheory.Shift.Adjunction`: `Adjunction.CommShift`;
  `Mathlib.CategoryTheory.Shift.CommShift`: `NatTrans.CommShift`.
- The scheme-morphism-properties dependency is a convention node; the binders use
  its specified Mathlib notions `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact` and `IsOver` directly.

The theorem retains the node's full eight-step natural-language proof in its
docstring. Proof-dependency modules are ordinary imports, while the interfaces
needed in the signature are public imports. No new theorem or definition is
invented for the extra normalization comparisons: they are existential conclusions
inside this node's statement. No proof is supplied beyond `sorry`.

Sources and edge cases:

Read the local Bhatt--Scholze PDF text at Lemma 6.7.2, Proposition 6.8.14 and
Remark 6.8.15. The pushforward lemma assumes finitely presented qcqs maps with
quasi-excellent ell-coprime target; the separated finite-type field hypotheses
supply these. Proposition 6.8.14 gives raw rationalization and the filtered
finite-coefficient passage; Remark 6.8.15 fixes the ordinary derived direct image.
The normalization follows the same actual adjunction used by the realization node.

Checked empty X (and empty Y when a morphism exists), zero objects, f=id,
E=F, successive extensions, ramified finite coefficient extensions, characteristic
zero, and every positive and negative integer shift. No finite-field model is
applied to arbitrary k. In the identity case `ep`, `er`, `qp`, `qr` have their
identity components and their ordinary shift comparisons, so the pinned shift
conditions have their intended meaning. Twisting a free right-adjoint shift
comparison would break the normalized comparisons or the finite adjunction clause.
No false statement or statement correction was found.

Searches (new searches are also in the new nodes' mathlib_searches):

- Earlier `msearch.py leanfinder` for the complete arbitrary-field adjunction:
  eight ordinary module/sheaf adjunction hits, no match; Loogle for Adjunction
  and CommShift found generic shift interfaces; grep found no adic statement.
- New LeanSearch for a bundled separated finite-type base with adic stages:
  eight scheme/finite-type hits, no such interface. LeanFinder for the same
  notion found AffineScheme, Scheme and finite-type infrastructure only.
- New LeanSearch for rationalized adic direct image with its canonical scalar
  mate: eight generic adjunction/scalar hits. LeanFinder for the same notion:
  eight condensed/derived-functor hits, no exact statement.
- Loogle `CategoryTheory.StageSystem, AlgebraicGeometry.Scheme.PerAdic.Base`:
  zero hits, unknown StageSystem identifier in the Mathlib index.
- Mathlib grep `pbcDescentDirectImage|PbcDirectImageBetaSpec|PerAdic|structure Base`
  under CategoryTheory: three unrelated BasedCategory/BasedFunctor hits.
- `rg` in the upstream WeilConjectures tree found neither the item id nor these
  PerAdic/direct-image definitions. `rg` in lean/Sheaf found exactly the reused
  definitions in AdicHeartPullbackFibres and PbcDescentFunctors. Other Base types
  have different coefficient inputs or hypotheses and are not copied.
- DAG definition-node search found no node recording these interfaces.
  `blueprint_refs.py search` for finite type scheme found only the dimension
  lemmas; searches for separated finite type base / rational direct image /
  descent direct image found no blueprint definition. Hence the two new nodes
  bind existing project definitions, with no new Lean module or duplicate notion.

## New nodes

`def-per-adic-base-stages` records the unchanged `PerAdic.Base` bundle and its
actual scalar system and stage inclusions in `Sheaf.Paper.AdicHeartPullbackFibres`.
Its existing:true declaration list includes the base instances used to elaborate
those constructions. It is a definition interface, not the adic-heart theorem.
Its source is BS Section 6.8 and the common-finite-stage passage of 6.8.14.
The searches above found the existing declaration but no definition node for it.

`def-per-rational-direct-image-family` records the unchanged
`pbcDescentDirectImage` and `PbcDirectImageBetaSpec` in
`Sheaf.Paper.PbcDescentFunctors`. It defines the actual rational restriction and
its canonical comparison predicate, rather than asserting exact descent.
Its source is BS 6.8.14 and 6.8.15 and the explicit common-stage construction.
The searches above found these existing declarations but no definition node.

## Second reading by NA

Final worker self-check under the dispatcher brief (no other agents were started;
the independent mathematical review is the maintainer's). Read the final node
and signature together. Every source hypothesis and clause is matched above.
R1 leaves NM's record and module ownership intact; R2 adds only the two existing
definition interfaces and removes the two extra theorem dependencies from the
saved packet. R3 now checks finite-stage adjunctions against normalized ambient
shifts and checks descent through the actual inclusion comparisons. The advisory
is addressed by the integral and localized transpose equations. The theorem's
pullback is literally the body of the recorded completed-pullback definition.
The item is refreshed from current shared main; apart from lean, its only delta
is adding those two new definition ids to stmt_deps. The new node records use
existing:true, and all searched definitions are reused unchanged. No mathematical
node statement, dependency module, or live source file was modified.
