## Worker report

The module `Sheaf.AlgebraicGeometry.FlatTraitGroupFiniteComponentOpens` states
`AlgebraicGeometry.flatTraitGroup_finite_component_opens`. It also defines the real-data
helpers `traitPieceRestriction` (restriction of a subfunctor along a base change) and
`traitPieceNormalizationMap` (the canonical map from the spectrum of the integral closure).
The theorem uses the existing `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`
predicate for open scheme-test subfunctors.

The binders render the node as follows. `R` is a commutative domain with
`IsDiscreteValuationRing` and the recorded strictly henselian class. `F` is a contravariant
`GrpCat`-valued functor on schemes over `Spec R`, with an fpqc sheaf condition. `p : T → Spec R`
is the fpqc representing cover, expressed by
`hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage (Spec (.of R))`. `P : Over T`
is separated, flat, and locally of finite presentation, and `e` identifies the pulled-back
underlying functor with the Yoneda functor of `P`. The conclusion gives an open subgroup
`H` and a Type-indexed family of open subfunctors `U a`; the first conjunct identifies each
section of `H` with a subgroup, the next three conjuncts make `H` and every `U a`
representable by open immersions and make the family cover after Zariski sheafification.
The action clause states H-invariance on every scheme test. The next two clauses give separated,
flat, locally finitely presented, quasi-compact, quasi-separated representing schemes over T
for H and each U a. For every a, the final clause supplies a finite field extension L of the
fraction field, the integral-closure spectrum map with integral, surjective, flat and
quasi-compact properties, finite underlying fibres, and a semilocal Noetherian normal
one-dimensional integral closure. It then gives finitely many invariant open pieces V j over
that normalization, covering the pulled-back U a, and a scheme-test fppf cover on which the
(h,x) action map has local lifts. The final universal scheme-test quantifiers express
persistence under every further base change.

Dependencies used: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`, and
`CategoryTheory.Limits.pullback` are Mathlib leaves; the fpqc/fppf covering is
`AlgebraicGeometry.Scheme.fpqcTopology`/`fppfPrecoverage` from
`Mathlib.AlgebraicGeometry.Sites.Fpqc`; `CategoryTheory.Subfunctor` is from
`Mathlib.CategoryTheory.Subfunctor.Basic`; `AlgebraicGeometry.IsOpenImmersion`,
`AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.IsIntegralHom`,
`AlgebraicGeometry.Flat`, `AlgebraicGeometry.LocallyOfFinitePresentation`,
and `IsDiscreteValuationRing` are the recorded Mathlib declarations. The strictly henselian
class is `IsStrictlyHenselianLocalRing` from
`WeilConjectures.Mathlib.RingTheory.Henselian`.
The finite-base splitting theorem is
`AlgebraicGeometry.finite_base_splits_etale` from
`Sheaf.TraceFormula.FiniteBaseSplitsEtale`; the
integral-closure theorem is
`AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres` from
`WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`.
The chartwise etale permanence and algebraic-space locality declarations are imported from
`Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence` and
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality`; the latter is a proof dependency
only. The item cites `def-trf-algebraic-space` because its `IsRepresentableWith` declaration
is used directly. It now also cites `def-weil-pbc-krull-dimension-ring`, the recorded owner of
`ringKrullDim` in `Mathlib.RingTheory.KrullDimension.Basic`, used directly in the conclusion.

Edge cases checked: the index type `A` is `Type (u+1)`, so empty and arbitrary set-indexed
covers are admitted; the finite piece index is `Fin n`, including `n = 0`; no etaleness or
unramifiedness is imposed on L; ramification is allowed; finite underlying fibres are stated
separately from finite module hypotheses; H need not be commutative; and no representability
on the original base is asserted. The fppf local-lift quantifier permits empty test schemes
and all further base changes.

Searches: `msearch.py ... leanfinder` with query “Flat fpqc group sheaf over a strictly
henselian discrete valuation ring admits finitely presented open subgroup and invariant open
cover homogeneous after normalization in finite extensions” returned only generic
finite-presentation and universally-open results; `msearch.py ... leansearch` with query
“Open invariant finite presentation pieces of a flat fpqc group sheaf over a trait” returned
only generic sheaf finite-presentation declarations; `msearch.py ... loogle` with
`AlgebraicGeometry.IsOpenImmersion, CategoryTheory.Subfunctor` returned no exact theorem;
`msearch.py ... grep` for `GroupSheaf|finite.component.opens|openSubgroup` in AlgebraicGeometry
returned no hits; repository `rg` found no declaration of this item. The existing notion
`AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith` was found in
`lean/Sheaf/AlgebraicGeometry/AlgebraicSpace.lean` and is reused.

The source is Anantharaman, *Schémas en groupes*, §4.2, Lemma 4.2.4 and the action argument,
printed pp.59–61 (the source PDF is `literature/anantharaman-groupes-dimension-un.pdf`; the
public scan is Numdam, pp.55–61). The proof docstring records the seven source-based proof
steps, including the strictly henselian neutral-product correction and the ramified
normalization construction.

## Second reading by Q57

I reread the node, its statement, and the module. This was a self-check, not an independent review. The conclusion audit covered
each clause: subgroup and open-subfunctor data, covering and invariance,
representability and finite-presentation properties after T, normalization data, finite fibres,
semilocal normal one-dimensional closure, finite invariant pieces, and fppf-local action lifts
with arbitrary further base change. The later independent review found the stronger quasi-compactness assumption on p;
it is repaired in this version as recorded below. The original self-check found no added etaleness,
commutativity, unramifiedness, or representability over S. The helper definitions have actual
data and no `sorry`; only the theorem proof is `sorry`.


## Repair of returned delivery 61a2caa4705b

The sole return entry reports rejection of a reviewer-side `--apply-fixes` path:
`dag/nodes/sec-six-functors-basics/lem-sfb-flat-trait-group-finite-component-opens.json`.
That is not a permitted stage-2 reviewer fix file. The merger accepts a flat
`lem-sfb-flat-trait-group-finite-component-opens.lean-record.json` for record overrides,
`FlatTraitGroupFiniteComponentOpens.lean` for module fixes, and
`lem-sfb-flat-trait-group-finite-component-opens.report.md` for the report. A whole existing
item node is not a reviewer fix-file format. Normal worker deliveries, in contrast, require
the sandbox node at its DAG path; `deliver2.py` reads it and constructs the permitted delivery.

The retained sandbox was compared with current main: only `lean` and the addition of
`def-trf-algebraic-space` to `stmt_deps` differed. Main still has no Lean record or module for
this item. The terse return entry hid the actual mathematical fix. I recovered and read
`local/verdicts/2/61a2caa4705b9e5b55e129b1ba80b2403ddb12eb/review.md` on the project server,
its FIX verdict, and both saved fix files. The independent reader found one substantive
fault: the three classes `[Flat p] [Surjective p] [QuasiCompact p]` were stronger than the
node's singleton-fpqc-cover hypothesis. The saved fix could not land because its full item
node was passed through the reviewer's unsupported `--apply-fixes` path.

The module now applies that exact fix:
`(hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage (Spec (.of R)))`.
The `lean.statement` signature is regenerated verbatim from the changed module, and
`lean.note` records the repaired hypothesis. The natural-language statement needs no
correction, since it already specified an fpqc cover. All conclusion clauses are retained.

The edge case distinguishing the old and repaired signatures is the infinite disjoint
union of copies of S mapping to S. It is a singleton fpqc covering (one component already
covers S) but its structure morphism is not quasi-compact. The theorem now includes it.
Shrinking T is not a replacement for the fix, because the conclusion asks for the same
existential H and U_a with their finite-presentation properties over the given T.

The replacement delivery also makes the direct Krull-dimension dependency explicit in
`stmt_deps` and records its declaration and module above. It corrects three namespace/module
conflations in the report: the henselian class and the finite-splitting and integral-closure
theorems have the declaration names listed above, without module names prepended as namespaces.
All updates are delivered in the normal worker packet, so no reviewer-side patch is needed.
No repository tool or launcher script was modified.

The repaired source is compiled with `scompile.py`, then checked with
`deliver2.py --no-push` and delivered with `deliver2.py`.

## Clause audit for the repair

- The hypotheses `R`, `CommRing`, `IsDomain`, `IsDiscreteValuationRing`, and
  `IsStrictlyHenselianLocalRing` encode the strictly henselian DVR; `Spec (.of R)` is S.
- `F : (Over S)ᵒᵖ ⥤ GrpCat` and `hF` give a group sheaf, without commutativity. The hypothesis hp
  asserts that the singleton p belongs to the recorded fpqc precoverage. The iso e is a natural identification of its restriction with the
  functor of points of P. Yoneda transports the group operations on that functor to P;
  no arbitrary group law or stronger representability hypothesis is used.
- The first conjunct says `H.obj W` is the carrier of a subgroup for every test W.
  Subfunctor naturality supplies closure under restriction.
- `IsRepresentableWith (fun _ _ i ↦ IsOpenImmersion i.left)` on each inclusion expresses
  precisely representability of each inverse image by an open subscheme of the test.
- The Zariski sheafification of the union equals top exactly when the testwise inverse-image
  opens cover. It does not require any test section to lie globally in a single piece.
- `h * x ∈ (U a).obj W` is the given left H-action invariance, for every a and W.
- Each representation of H or U after T has the classes `IsSeparated`, `Flat`,
  `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`; the last three are
  finite presentation. These conclusions impose no representability on S.
- L is a field with a compatible R/FractionRing R algebra tower and `FiniteDimensional`.
  `integralClosure R L` is the actual integral closure and `traitPieceNormalizationMap`
  is its canonical spectrum map. Its four morphism-property conjuncts and finite set fibres
  express every normalization-map assertion, including fpqc as their consequence.
- `IsDomain`, `IsNoetherianRing`, `IsIntegrallyClosed`, `ringKrullDim = 1`, and
  `Finite (MaximalSpectrum ...)` give every semi-trait condition. Dimension one permits
  no strict prime chain of length two and requires a length-one chain.
- The finite index `Fin n` permits zero pieces for an empty U. Each V is contained in the
  restricted U, is open by the same scheme-test predicate, and is H-invariant. Zariski-local
  union equality means the V cover precisely that restricted U.
- For every B-scheme W and x,y in V, the final clause gives an fppf covering of W and
  h in H with h times the restriction of y equal to the restriction of x. This is exactly
  local surjectivity of (h,y) ↦ (hy,y). An arbitrary W over any further B-scheme is still
  among these test schemes, and each covering map has the induced structure map to that
  further base. Thus the same clause includes arbitrary base change, without requiring
  a global lift or a globally transitive action on sections.

The section headed "Second reading by Q57" above records a self-check of the earlier packet,
not an independent agent review. The independent review saved with the returned head verified all conclusion clauses
and identified the p-hypothesis fault now repaired. This worker checked that fix against the
recorded fpqc precoverage; the replacement delivery remains subject to maintainer review.
