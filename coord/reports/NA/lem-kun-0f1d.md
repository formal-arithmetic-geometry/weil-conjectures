## Worker report

The module `Sheaf.AlgebraicGeometry.KunnethBaseChangeFailure` states
`AlgebraicGeometry.Etale.exists_kunnethBaseChangeFailure_functionField` with proof `sorry`.
It is Stacks Project, Tag [0F1D](https://stacks.math.columbia.edu/tag/0F1D), with the
cumulative universal condition from `def-kun-bc-property`, as in
[0F02](https://stacks.math.columbia.edu/tag/0F02). No statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause comparison:

| Node text | Lean rendering |
| --- | --- |
| A morphism of schemes `f : X → S` | `{X S : Scheme.{u}} (f : X ⟶ S)`; no finiteness, smoothness, separation or nonemptiness assumption on either scheme |
| An integer `n ≥ 1` | `(n : ℕ) (hn : 0 < n)`; positive integers are exactly positive naturals |
| `n` invertible on `S` | `(hinv : IsUnit (n : Γ(S, ⊤)))` |
| Some integer `q ≥ 1` | `(q : ℕ) (hq : 1 ≤ q)`; the theorem holds for every such `q`, hence can be applied to any witness |
| `BC(f,n,q-1)` holds | `hprev : UnboundedCumulativeUniversalBaseChangeProperty f n hn (q - 1)`; since `hq` holds, natural subtraction is ordinary integer subtraction here |
| `BC(f,n,q)` fails | `hfail : ¬ UnboundedCumulativeUniversalBaseChangeProperty f n hn q` |
| First square, commutative and Cartesian | Existential `S' X'`, arrows `a : S' ⟶ S`, `b : X' ⟶ X`, `f' : X' ⟶ S'`, and `ChosenCartesianSquare b f' f a`; its inherited `CommSq` gives commutativity and its chosen pullback identification gives Cartesianity |
| `S'` affine | `IsAffine S'` |
| `S'` integral | `IsIntegral S'`, which includes nonemptiness, reducedness and irreducibility |
| `S'` normal | `∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x)`; the stalks are already domains by integrality |
| Algebraically closed function field `K = k(S')` | `IsAlgClosed S'.functionField`; Mathlib's `Scheme.functionField` is precisely the stalk at the generic point, with its existing field instance |
| Generic-point morphism `Spec K → S'` | `S'.fromSpecStalk (genericPoint S')`; `K` is the function field itself, not a further extension or an independently chosen field |
| Second square, commutative and Cartesian | Existential `Y`, `e : Y ⟶ Spec S'.functionField`, `h : Y ⟶ X'`, and `ChosenCartesianSquare h e f' (S'.fromSpecStalk (genericPoint S'))` |
| Integer `d` dividing `n` | `(d : ℕ)` with `d ∣ n`; a negative divisor gives the same subgroup of `ℤ` and constant cyclic sheaf as its absolute value, so this parametrizes the same possible witnesses. `d = 0` is already impossible since `n > 0`. No extra positivity condition is added. |
| Constant cyclic abelian sheaf on `Y` | `(constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod d)))`; the lift is only the common small-site coefficient size convention |
| `R^q h_*` of that sheaf is nonzero | `¬ IsZero` of its image under `Plus.singleFunctor _ 0`, `(Etale.lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus`, and `Plus.homologyFunctor _ (q : ℤ)`; this is an abelian sheaf on `X'`, not a module-valued or arbitrary derived object |

Dependency declarations read and used:

- `def-kun-bc-property`: `AlgebraicGeometry.Etale.UnboundedCumulativeUniversalBaseChangeProperty`, module `Sheaf.AlgebraicGeometry.UnboundedCumulativeUniversalBaseChangeProperty`. The shared node had no Lean record. The published-source query found no module, but the server delivery branch `deliver/NK/def-kun-bc-property` supplies this exact definition. Its source is reused verbatim as a dependency module, without defining another predicate.
- `def-weil-pbc-cartesian-square`: `AlgebraicGeometry.ChosenCartesianSquare`, module `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`; read the complete structure, including both projection equations.
- `def-sc-function-field`: imported module `Sheaf.AlgebraicGeometry.FunctionField`. Its docstring explicitly directs the arbitrary integral-scheme clause to Mathlib's `AlgebraicGeometry.Scheme.functionField`, module `Mathlib.AlgebraicGeometry.FunctionField`; read that abbreviation and its generic-stalk and field-instance declarations. The component-product declaration is for reducible curves and is not used for integral `S'`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`, module `Mathlib.AlgebraicGeometry.Properties`; the class and domain/nonemptiness instances were read.
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf`, module `Mathlib.CategoryTheory.Sites.ConstantSheaf`; read its signature, sheafification body and docstring.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar`, module `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, module `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; read both full signatures and docstrings. The displayed `.rightDerivedFunctorPlus` is definitionally the latter.

The module imports the recorded modules of all stated proof dependencies, plus the Mathlib modules for affine/qcqs permanence, etale morphisms, fibre products and locally bijective sheafification. In particular the witness theorem `exists_universalBaseChangeFailure_cyclic_datum` has an extra algebraically closed extension of the function field; it does not already state this item. Its source and complete conclusion were read. The theorem docstring records the node's five proof steps, including the affine-object cohomology-presheaf descent that removes that extension; every theorem proof remains `sorry`.

Edge cases checked: `q = 1` invokes the degree-zero cumulative hypothesis and retains negative degrees in its unbounded definition. `n = 1` is allowed (its failure hypothesis is impossible), without adding `1 < n`. The initial schemes may be empty; the antecedent then cannot produce a false nonempty conclusion. Only the existential integral base is required nonempty. Divisor `d = 1` remains allowed syntactically, although the nonzero-sheaf clause rules it out; `d = 0` cannot divide positive `n`. Normality is not weakened to normality at the generic point. No qcqs assumption is imposed on `f`, `S' → S`, `X'` or the generic fibre. All schemes have the ambient scheme universe `u`; the function field is in that same universe and abelian coefficients are lifted to `u + 1`. Every variable and universe is explicitly bound.

Searches for an existing statement (real `msearch.py` calls, recorded in `searches.jsonl`):

- LeanFinder: “Failure of universal etale base change produces a normal integral affine base with algebraically closed function field and nonzero higher direct image of a constant cyclic sheaf”: eight results concerning etale morphisms, affine-space integrality and etale subalgebras; none states this higher-direct-image witness.
- Loogle: `"higherDirectImage", "baseChange"`: zero results.
- Mathlib grep in `AlgebraicGeometry`: `0F1D|exists.*isPullback.*isZero|CumulativeUniversal`: zero results.
- LeanSearch: “cumulative universal base change property in all degrees below q for etale sheaves”: service unavailable (`Internal Server Error`); this is not evidence of absence.
- Source and side-library `rg`: `BaseChange|baseChange|IsBaseChange|BC\(`, then `0f1d|FailureOf|failure.*base.change|integral.*normal.*function`, and then `theorem .*Failure|cyclic_datum|functionField.*IsAlgClosed|ChosenCartesianSquare.*IsAffine`. Found upstream `CurveTestDatum`, `exists_isPullback_not_isZero_higherDirectImage`, and side `UniversalBaseChangeFailureDatum`; they allow a further algebraically closed extension. None supplies the function field itself with exactly the present hypothesis. Read their signatures before rejecting an existing attachment.
- Source `grep -rn lem-kun-0f1d`: no results. Exact new declaration name searched in upstream source, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration.
- For the missing dependency, searched `blueprint: def-kun-bc-property|def .*Cumulative|def .*BaseChangeProperty` in side and upstream sources. The bounded/nonnegative cumulative predicate is not the exact unbounded definition. Checked the server's live node/source and its delivery branches; reused NK's exact source as described below.

No `STATEMENT-DISPUTED` flag or source fault was found. No new notion or new DAG node is introduced.

## Dependency modules

`def-kun-bc-property`: the shared/live node has no recorded declaration, so the human's “Unstated dependencies are yours to state” instruction applies. The exact module already delivered by group NK is included verbatim from `deliver/NK/def-kun-bc-property`, under its original module and declaration names. Only the dependency node's `lean` field is set, with a note recording this provenance. The definition quantifies over all base changes, every qcqs horizontal morphism, every `ULift (ZMod n)`-module sheaf and every integer degree at most the bound. It applies without an invertibility hypothesis and uses the already recorded canonical exact unbounded exchange; no comparison map, cohomology predicate or coefficient category is replaced. If NK's delivery lands before the second reading, the reader can omit this redundant dependency module and node record and import that published module directly.

Validation: every delivery module is compiled separately through `scompile.py` in dependency order; the required `deliver2.py --no-push` dry run follows. The sole theorem in the main module has proof `sorry`; the dependency definition has actual data and contains no postponed theorem.

## Second reading by NA

I independently read the item node, both sandbox modules and their node records,
all six statement-dependency nodes and their declaration signatures. I also read
`etale-cohomology.tex` at `remark-base-change-holds` (0F02),
`lemma-base-change-does-not-hold` (0F08),
`lemma-smooth-base-change-separably-closed` (0F0B), and
`lemma-base-change-does-not-hold-post` (0F1D). The source's surrounding section
adds no quasi-compactness, quasi-separatedness, Noetherianity, smoothness or
separation hypothesis on `f`. Its qcqs condition concerns the test map `g` in
BC. The 0F1D diagram labels the horizontal projection by `h`, and uses the
function field itself after descending the 0F08 extension witness. These agree
with the current node and the Lean, so no statement correction is required.

My object/hypothesis/conclusion checklist, each entry with verdict **pass**:

| Node object or clause | Lean rendering and independent verdict |
| --- | --- |
| Arbitrary schemes and their morphism | `{X S : Scheme.{u}} (f : X ⟶ S)`; no extra instance is imposed on either scheme or `f`. |
| Positive integer `n` | `(n : ℕ) (hn : 0 < n)`; exactly parametrizes the source's positive integers. |
| `n` invertible on `S` | `IsUnit (n : Γ(S, ⊤))`; being a unit is local and local inverses glue, so this is invertibility on the whole scheme, including the empty scheme. |
| Positive failure degree `q` | `(q : ℕ) (hq : 1 ≤ q)`; the theorem applies to each `q` satisfying the antecedent, as required by the source's “for some q”. |
| Cumulative universal BC through `q-1` | `hprev : UnboundedCumulativeUniversalBaseChangeProperty f n hn (q - 1)`; natural subtraction is the source's subtraction because `q ≥ 1`. |
| Failure of cumulative universal BC through `q` | `hfail : ¬ UnboundedCumulativeUniversalBaseChangeProperty f n hn q`; it is not merely a failure for one chosen test square or one coefficient sheaf. |
| Base-changed schemes and arrows | Existential `S' X'`, `a : S' ⟶ S`, `b : X' ⟶ X`, `f' : X' ⟶ S'`. |
| First commutative Cartesian square | `ChosenCartesianSquare b f' f a`; its inherited `CommSq`, `isoPullback`, `hom_fst` and `hom_snd` identify this exact square with the pullback square. |
| Affineness | Existential `IsAffine S'`, with no affineness requirement on `X'`. |
| Integrality | Existential `IsIntegral S'`; the Mathlib class supplies nonemptiness and domains of nonempty open sections, hence irreducibility and domain stalks. |
| Normality | `∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x)`; read Mathlib's fraction-ring definition. Together with integrality this says every local ring is an integrally closed domain, without a Noetherian assumption. |
| Algebraically closed function field | `IsAlgClosed S'.functionField`; read Mathlib's `Scheme.functionField`, literally the generic stalk, and its field instance for integral schemes. The project dependency explicitly delegates this arbitrary-integral-scheme clause to that declaration, rather than its curve component-product construction. |
| Canonical generic-point arrow | `S'.fromSpecStalk (genericPoint S')`; read the stalk-map definition. Its source is `Spec S'.functionField`, so this is not a separately chosen algebraically closed extension. |
| Generic fibre and its projections | Existential `Y`, `e : Y ⟶ Spec S'.functionField`, `h : Y ⟶ X'`. |
| Second commutative Cartesian square | `ChosenCartesianSquare h e f' (S'.fromSpecStalk (genericPoint S'))`; the ordering makes `h` horizontal and `e` vertical, and includes the same two projection equations. |
| Divisor | Existential `(d : ℕ)` and `d ∣ n`; integer divisors are represented up to sign, which gives the same quotient cyclic group. Since `n > 0`, zero cannot be a witness. No prime or strict-positivity hypothesis is added to the conclusion. |
| Constant cyclic abelian sheaf on `Y` | `(constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod d)))`; this is the recorded sheafification construction with the standard coefficient lift. |
| Nonzero `R^q h_*` on `X'` | `¬ IsZero` after `Plus.singleFunctor _ 0`, `(Etale.lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus` and `Plus.homologyFunctor _ (q : ℤ)`. I read the upstream `lowerStar` and `rightDerivedLowerStarPlus` bodies and Mathlib's two Plus functors: this is precisely the bounded-below derived direct image followed by degree-q cohomology in abelian sheaves on `X'`, not cohomology on `Spec K`. |

Dependency-module reading (H13): `def-kun-bc-property` still has no published
module under `scompile.py --source`. Its supplied module was therefore retained.
It has real definition data, no `sorry`, and introduces exactly the existing
DAG node's notion. It quantifies over every `S'`, `a`, `T`, qcqs `g`, module
sheaf `F`, and integer `q ≤ q₀`. The coefficient category is the recorded
six-functor encoding `Sheaf T.smallEtaleTopology (ModuleCat (ULift (ZMod n)))`;
these are exactly abelian sheaves annihilated by `n`. There is no invertibility
premise. I read `exactDerivedBaseChangeMap`: the flipped canonical pullback
square gives inverse image along `pullback.snd f a` of `Rg_* F[0]` as source,
and direct image along the other pullback projection of inverse image along
`Y → T` as target. Thus its orientation and its unbounded cohomology agree with
the dependency node. The older `CumulativeUniversalBaseChangeProperty` has a
different degree domain and invertibility argument; it is not an exact
replacement. The dependency record explains this and reuses NK's module name,
without a private copy or an additional notion. There are no new DAG nodes to
review under H12.

Edge cases: `q = 1` retains the degree-zero and all negative-degree conditions
in the unbounded premise. The item intentionally excludes `q = 0` and `n = 0`,
as does the node. `n = 1` and `d = 1` remain allowed, though a genuine failure
or the final nonzero image cannot arise with zero coefficients. Empty `X` or
`S` is permitted in the initial binders; its impossible failure premise does
not require an existential integral empty base. The output integral scheme is
necessarily nonempty, as the source requires. There is no index family, so no
nonempty-index or finite-index restriction. In positive characteristic the
unit hypothesis excludes precisely the orders not invertible on `S`; no
characteristic-zero hypothesis is present. `u` is arbitrary; all schemes and
the generic stalk have that universe, while the small-site abelian/module
coefficient convention is `u+1`. No extra universe equality or hidden field
parameter is introduced.

Independent duplicate searches, using different wording from the first reader:

- LeanFinder: “A nonzero higher direct image of a constant finite cyclic sheaf
  at the generic point detects failure of universal cohomological base change”.
  Eight hits, including `Sheaf.H`, cohomology-presheaf functors and generic
  derived-category vanishing criteria; no function-field failure witness.
- Loogle: `"functionField", "IsAlgClosed"`: no hits.
- Mathlib grep: `0F1D|base.change.does.not.hold.post|kunnethBaseChangeFailure`
  in AlgebraicGeometry: no hits. The real tool calls are in `searches.jsonl`.
- Direct `rg` in the source repository, `lean/Sheaf`, and the upstream-name
  index for `0f1d`, `base.change.does.not.hold.post`,
  `kunnethBaseChangeFailure`, and both orders of `IsAlgClosed`/`functionField`.
  I opened `Etale.exists_isPullback_not_isZero_higherDirectImage` in upstream
  `SmoothBaseChange/CurveTestDatum.lean` and
  `exists_universalBaseChangeFailure_cyclic_datum` in the side-library module.
  Both permit a further field extension `K` and hence do not already state the
  required function-field conclusion. The other hits concern normalization,
  curve-test data or its vanishing. No exact existing statement was found.

H5/H6/H8/H9 checks: the dependency is an actual Prop-valued construction and
the main theorem has exactly `by sorry`; no theorem was proved. The source and
blueprint docstrings are present, and the main theorem's five proof steps
match all five steps of the DAG, including the affine-etale-object descent
which avoids an extra qcqs hypothesis. All module lines are at most 100
characters. There is no local notation, local instance, private construction,
unbound variable or unbound universe. Both node signatures are verbatim
substrings of their files from the declaration keyword to `:=`.

Mismatches found: none in the Lean statements, definitions or node records.
Changes: appended this independent second-reading report; preserved the two
Lean modules and the node statements. Both sibling modules compiled cleanly,
separately and in dependency order, through the prescribed `scompile.py`
wrapper, with no errors or warnings. Delivery dry run and final delivery are
performed after this report.
