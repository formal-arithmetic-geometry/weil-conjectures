## Worker report

This delivery binds `lem-fd-realness-pushforward` to the exact existing declaration
`AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_snd_one` in
`WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` (branch `slopmaster2`).
No Lean module is introduced, no proof is changed, and only the item's `lean` field changes.
The current source was obtained by
`python3 /home/ubuntu/weil-launcher-nt/scompile.py --source WeilConjectures.DeligneLaumon.AffineLine.RealPushforward`.
The older local slopmaster2 checkout lacks this file; the authorized source wrapper returns
its complete published source, including the declaration and its enclosing variables.
There is no repair-note file for this item in the shared repository.

The statement was compared with the whole DAG statement and with
`literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-some-weight/lem-fd-realness-pushforward.md`.
The current blueprint has the same mathematical statement. Its proof now follows the trace
formula on the residue-field fibre, with the corrected exponent, as recorded by the DAG.
Binding the existing declaration does not certify its transitive axioms or close stage 3.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite field `k₀ = F_q` is the implicit `{k₀ : Type u} [Field k₀] [Finite k₀]`.
  Every finite field occurs; naming its cardinality `q` adds no mathematical datum here.
  The coefficient conventions are `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`,
  inherited from the node's Weil-sheaf dependencies. These impose exactly the distinct
  coefficient prime required by those notions.
- `X₀ = A¹ ×_{k₀} A¹` is `affinePlane k₀`. In
  `WeilConjectures.WeilSheaf.Fourier`, `affinePlane` is literally the pullback of the two
  structure maps of `affineLine k₀` to `Spec k₀`.
- The second projection `p₂` is `affinePlane.snd k₀`; its definition is `pullback.snd _ _`.
  The same file supplies its over-base, separated, quasi-compact and locally-finite-type
  instances. Those are properties of this specified map, not additional user hypotheses.
- The constructible Weil sheaf `K` is `{K : WeilSheaf k₀ l (affinePlane k₀)}`.
  `WeilConjectures.WeilSheaf.Category` defines `WeilSheaf` as the full subcategory of
  Frobenius fixed pairs of adic sheaves whose underlying sheaf is constructible.
  Constructibility is built into this type; lissity and positive rank are not required.
- The realization is `{ι : PadicAlgCl l →+* ℂ}`, the coefficient-embedding interface of
  the recorded reality definition. The field ring homomorphism is injective, and the
  statement applies in particular to the fixed realization of the node. No continuity
  or additional reality hypothesis on the embedding occurs.
- The assumed reality is `(hK : K.IsReal ι)`. The definition in
  `WeilConjectures.WeilSheaf.Stalk` is pointwise reality of the stalk Frobenius module
  at every finite (closed) point. `FrobeniusModule.IsReal` in
  `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule` says each coefficient of
  `det(1 - T F)` is fixed by complex conjugation after applying `ι`, precisely membership
  in `R[T]`. The dependency's primary recorded name `IsRealizable` is a different
  clause of the same source module; this theorem uses its existing `IsReal` definition.
- The entire vanishing hypothesis is
  `(hvan : ∀ ν : ℕ, ν ≠ 1 → IsZero
    ((higherLowerShriek k₀ l (affinePlane.snd k₀) ν).obj K))`.
  `WeilSheaf.higherLowerShriek` is the degree-ν cohomology sheaf of compact-support
  direct image of the sheaf placed in degree zero. This is shriek, not ordinary star.
  The natural-number index includes degree zero. Negative degrees vanish automatically
  for this right-derived direct image of a sheaf; they impose no additional condition.
- The conclusion is exactly
  `((higherLowerShriek k₀ l (affinePlane.snd k₀) 1).obj K).IsReal ι`.
  Its type is a constructible Weil sheaf, so both constructibility and the induced
  Frobenius structure are retained. There is no assertion that it is lisse.

All six statement-dependency records and their declarations/docstrings were read:

1. `def-fd-transform`: `WeilConjectures.FourierTransform.Defs`,
   `AlgebraicGeometry.Etale.fourierTransform`. Its signature uses `pullback.snd π π'`
   and its docstring specifies `Rp₂,!(p₁* K ⊗ᴸ kernel)[r]`. This item uses only the
   specified projection, not a normalization or shift of the Fourier functor.
2. `def-wf-iota-real`: `WeilConjectures.WeilSheaf.Stalk`,
   `AlgebraicGeometry.WeilSheaf.IsRealizable`, and the immediately preceding
   `AlgebraicGeometry.WeilSheaf.IsReal`. The latter supplies the reality clause needed
   here; the former states the direct-summand/lisse realizability clause of that node.
3. `def-weil-constructible-heart`: `Sheaf.Paper.SfConstructibleHeart`,
   `WeilConjectures.sfRationalHeart`, `sfCommonStageHeart` and their defining properties.
   They express the standard degree-zero heart in the rational/common-stage categories.
4. `def-weil-weil-sheaf-complex`: `Sheaf.Paper.SfWeilSheafComplex`,
   `WeilConjectures.sfWeilComplex`, `sfWeilSheaf`, `sfCommonStageWeilComplex`,
   `sfCommonStageWeilSheaf`. These are fixed pairs, with sheaves selected by their
   underlying heart property.
5. `def-weil-integral-rational-qbar-compact-support`:
   `Sheaf.Paper.QcqsCompactSupportRealization`,
   `WeilConjectures.sfQcqsCompactSupportRealization`, and its publicly imported integral,
   rational and common-stage value definitions in `IntegralRationalQbarCompactSupport`.
   These give compact-support direct image via integral finite-level realization.
6. `def-weil-derived-cohomology-sheaves`: `Sheaf.Paper.PbcQbarStandardCohomology`,
   `AlgebraicGeometry.Scheme.pbcQbarCohomology`, and the publicly imported
   `pbcStageCohomology`/`pbcRationalCohomology`. The ambient Mathlib match is
   `DerivedCategory.homologyFunctor`.

The exact existing statement is a statement about sheaves. Its definitions used directly
are `AlgebraicGeometry.WeilSheaf`, `WeilSheaf.IsReal`, `WeilSheaf.higherLowerShriek`,
`affinePlane` and `affinePlane.snd`. `higherLowerShriek` is defined in
`WeilConjectures.WeilSheaf.LowerShriek` as
`WeilSheaf.toComplex ⋙ WeilComplex.derivedLowerShriek ... ⋙ WeilComplex.homologySheaf ν`;
`homologySheaf` is the restriction of `DerivedCategory.homologyFunctor`.
The source calls its ambient derived-of-Weil-sheaves category `WeilComplex`, whereas
`sfCommonStageWeilComplex` is the fixed-pair category in the constructible derived category.
These ambient complex categories must not be identified. That distinction does not change
this existing theorem's input or output: both are constructible sheaves with their Weil
isomorphisms, and its operation is their higher compact-support direct image. No statement
about arbitrary objects or morphisms of the two complex categories is being rebound.
Accordingly this is an existing sheaf-level match under brief-stage2 §1; no private copy
or replacement of any recorded dependency is needed.

Edge cases checked from the signatures and definitions: the zero sheaf and zero output
stalks are allowed (`det(1 - T F) = 1`); rank need not be positive; degree-zero direct image
is included in `hvan`; all natural degrees other than one are covered, not only degrees
above one; no nonempty support, lissity, purity, semisimplicity, special characteristic,
or extra compactification choice is assumed. The fixed affine source and target are
nonempty, so replacing either by an empty scheme is not a case of this particular node.
The scheme and finite-field universe `u` is arbitrary.

Searches (all through the prescribed tooling or read-only source searches):

- `msearch.py ... leanfinder "An iota-real constructible Weil sheaf on the affine plane
  with compact support pushforward concentrated in degree one has real first higher
  direct image"`: eight Mathlib hits on affine transition limits and module pushforward;
  none is the statement.
- `msearch.py ... loogle "WeilSheaf.IsReal, WeilSheaf.higherLowerShriek"`: zero hits,
  unknown identifier `WeilSheaf.IsReal` in the Mathlib search environment.
- `msearch.py ... grep "WeilSheaf|higherLowerShriek|iota.real"`: zero Mathlib hits.
- `msearch.py ... leansearch "An iota-real Weil sheaf whose compactly supported direct
  image is concentrated in degree one has real first higher direct image"`: eight
  unrelated hits on sheaves, ideal sheaves and real infinite places; none is the statement.
- `rg` for `IsReal`, `IsRealizable`, real pushforward and `higherLowerShriek` in the named
  upstream and shared `lean/Sheaf` trees finds the upstream definitions and other
  general direct-image statements; it finds no side-project duplicate of this statement.
- The item id and `isReal_higherLowerShriek_snd_one` were searched in the upstream source,
  shared `lean/Sheaf`, and `dag/lean_names_upstream.json`. The name table explicitly maps
  this node to `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_snd_one`.
- `scompile.py --source` returned the missing current module. Its specialized theorem,
  including its enclosing field/prime binders, is the exact match selected above.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED is required.
As prescribed for an existing declaration, there is no delivered Lean file to compile.
The delivery dry run checks the recorded declaration and the delivery shape.

## Second reading by N6

Independent reading (maintainer reviewer, 2026-10-18). The section delivered under this heading
was the author's own self-check and said so; it is replaced by this independent reading of the
node, the source place and the published declaration.

Node statement as a list, with the Lean that renders it and the verdict:

1. `k₀ = F_q`: `{k₀ : Type u} [Field k₀] [Finite k₀]` (section variables, line 44 of
   `WeilConjectures/DeligneLaumon/AffineLine/RealPushforward.lean`). Every finite field, any
   universe. Correct.
2. The prime `ℓ ≠ p` and `Q̄_ℓ` of the Weil-sheaf dependencies: `{l : ℕ} [Fact l.Prime]
   [Fact (ringChar k₀ ≠ l)]`, coefficients `PadicAlgCl l`. Exactly the dependency convention.
   Correct.
3. `X₀ = A¹ ×_{k₀} A¹`: `affinePlane k₀`, defined (`WeilSheaf/Fourier.lean:1297`) as
   `pullback (affineLine k₀ ↘ Spec k₀) (affineLine k₀ ↘ Spec k₀)`, `affineLine` being Mathlib's
   `𝔸(PUnit; Spec k₀)`. Correct.
4. `p₂ : X₀ → A¹`: `affinePlane.snd k₀ := pullback.snd _ _` (line 1316), the same second
   projection that the upstream Fourier transform uses (`fourierTransform`, line 1363). Its
   `IsOver`, separated, quasi-compact, locally-finite-type instances are derived, not assumed.
   Correct.
5. `𝒦` a constructible Weil sheaf on `X₀`: `{K : WeilSheaf k₀ l (affinePlane k₀)}`;
   `WeilSheaf` (`WeilSheaf/Category.lean:168`, tagged `def-weil-weil-sheaf-complex`) is the full
   subcategory of constructible adic pro-étale sheaves on `X̄` with `Fr^*F ≅ F`. No lissity or
   rank condition. Correct.
6. `ι`: `{ι : PadicAlgCl l →+* ℂ}`; the node fixes a field isomorphism, the Lean allows any ring
   homomorphism, which includes it. Not stronger as a hypothesis. Correct.
7. `𝒦` is `ι`-real: `(hK : K.IsReal ι)`, `WeilSheaf.IsReal` (`WeilSheaf/Stalk.lean:371`) =
   `∀ x : X.finitePoints, (F.stalk x).IsReal ι`, and `FrobeniusModule.IsReal`
   (`ZetaLinearAlgebra/FrobeniusModule.lean:195`) = every coefficient of `ι(det(1 - T F))` is
   fixed by complex conjugation, i.e. lies in `ℝ`. `finitePoints` (finite residue field) are the
   closed points for a scheme of finite type over `k₀`
   (`AlgebraicGeometry.Scheme.Hom.finitePoints_eq_closedPoints`). This is
   the ι-real clause of `def-wf-iota-real` (the record's `IsRealizable` is the other clause of the
   same node, in the same module, defined in terms of `IsReal`). Correct.
8. `R^ν p_{2,!}𝒦 = 0` for `ν ≠ 1`: `(hvan : ∀ ν : ℕ, ν ≠ 1 → IsZero ((higherLowerShriek k₀ l
   (affinePlane.snd k₀) ν).obj K))`. `WeilSheaf.higherLowerShriek`
   (`WeilSheaf/LowerShriek.lean:168`) is
   `toComplex ⋙ WeilComplex.derivedLowerShriek ⋙ homologySheaf r`, with `derivedLowerShriek`
   the genuine `Rḡ_* ∘ i_!` on pro-étale Weil sheaves for the chosen Nagata compactification
   (lines 86-160; no `sorry` in the file). Compact support, not `Rf_*`. Degree 0 is included;
   negative degrees vanish for a sheaf
   (`WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg`), so
   indexing by `ℕ` loses no case. Correct.
9. Conclusion `R¹p_{2,!}𝒦` is `ι`-real: `((higherLowerShriek k₀ l (affinePlane.snd k₀) 1).obj
   K).IsReal ι`. Same notion as in 7, on the target `A¹`. Neither weaker nor stronger. Correct.

The `R^ν f_!` computed in the derived category of pro-étale Weil sheaves agrees with the
cohomology sheaf of `Rf_!` of the underlying sheaf with its induced Frobenius (forgetting the Weil
structure is exact with an exact left adjoint, so it preserves injectives and commutes with
`Rḡ_*`); the project already binds `prop-functor-package` and several sec-deligne-laumon-general
nodes to this upstream `derivedLowerShriek`/`higherLowerShriek` API, and binds other upstream
`WeilSheaf` theorems (e.g. `lem-a1-affine-hc0`, `lem-zl-constant-sheaf-weight-zero`), so this is
the project's one notion, not a second definition.

Edge cases: zero sheaf and zero stalks (local polynomial 1, real); no positive rank, lissity,
purity or nonempty support assumed; degree 0 included in the vanishing; `ι` arbitrary ring map;
one universe `u` for `k₀` and the schemes, any finite field occurring in some universe; the
source and target are the fixed nonempty affine schemes of the node.

Declaration and searches: the declaration carries `(blueprint: lem-fd-realness-pushforward)`;
`dag/lean_names_upstream.json` and the blueprint snapshot main-20261017 list it for this node.
No `lean/Sheaf` declaration states the same thing (grep of `isReal_higherLowerShriek` and
`lem-fd-realness-pushforward` on the side tree). The record's `statement` is verbatim lines
128-131 of the published source up to `:=`; the delivery commit changes only the item's `lean`
and adds this report. The published module compiles with
`tools/nt_compile.py WeilConjectures/DeligneLaumon/AffineLine/RealPushforward.lean`: exit 0,
2.6 s, no diagnostics.

Mismatches found: none in the statement. Changed: only this section (the delivered one was an
author self-check, not a second reading).
