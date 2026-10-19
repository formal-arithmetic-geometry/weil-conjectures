## Worker report

The delivery states `AlgebraicGeometry.Etale.isZero_higherDirectImage_constant_genericFibre`
in `Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing`. Its only theorem has proof
`sorry`; no definitions or additional assumptions are introduced. The node is copied from
the shared repository with only `lean` set. No repair note was present for this item.

Read the current main-20261015 blueprint's `lem-kun-0f1i-normal.md`, the complete DAG
statement and seven proof steps, all ten statement-dependency nodes and their declaration
sources, and Stacks `etale-cohomology.tex`, the final reduction and final paragraph of
Tag 0F1I (approximately lines 20650–20703). The blueprint explicitly names the
algebraically closed function field L; the Stacks paragraph's reference to function field
K is a typographical slip in view of its diagram and the following Frac(B)=L sentence.
The statement agrees with the current blueprint. Its proof docstring records all seven
DAG steps, including the repeated-base colimit, the four inverse limits, the compatible
constant coefficients, cohomological exchange, the 0EZT limit, and 0EZP vanishing.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| K is a field | `{K : Type u} [Field K]` |
| n is positive and invertible in K | `n : invertibleTorsionOrders K`, whose definition is `{n : ℕ | 0 < n ∧ (n : K) ≠ 0}`; a nonzero element of a field is a unit |
| X and S' are K-schemes | `(X S' : Scheme.{u})` with `[X.Over (Spec (.of K))]` and `[S'.Over (Spec (.of K))]` |
| X is finite type over K | `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and `[QuasiCompact (X ↘ Spec (.of K))]`, the recorded finite-type convention |
| S' is affine | `[IsAffine S']` |
| S' is integral | `[IsIntegral S']`; in particular it is nonempty |
| S' is normal | `_hnormal : IsNormalScheme S'`; this is the recorded conjunction of integrality and integrally closed domain stalks |
| L is the function field of S', algebraically closed | `S'.functionField` with `[IsAlgClosed S'.functionField]`; Mathlib defines it as `S'.presheaf.stalk (genericPoint S')` and gives its field instance from integrality |
| X'=X×_K S' | `pullback (X ↘ Spec (.of K)) (S' ↘ Spec (.of K))` |
| Spec L→S' is the canonical generic-point map | `S'.fromSpecStalk (genericPoint S')`; its domain is definitionally `Spec S'.functionField` |
| Y=X'×_{S'}Spec L | `pullback (pullback.snd (X ↘ Spec (.of K)) (S' ↘ Spec (.of K))) (S'.fromSpecStalk (genericPoint S'))` |
| h:Y→X' is the projection | `pullback.fst` of the preceding two arrows |
| all q>0 | `(q : ℤ) (_hq : 0 < q)` |
| all d dividing n | `(d : ℕ) (_hd : d ∣ n.val)` |
| constant abelian sheaf Z/dZ on Y | `(constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod d)))`, with Y expanded in the file |
| R^q h_* | degree-`q` `DerivedCategory.Plus.homologyFunctor` applied to `(lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus` of `DerivedCategory.Plus.singleFunctor _ 0` applied to that sheaf |
| vanishes | `CategoryTheory.Limits.IsZero` of that cohomology sheaf |

Dependency declarations used, with their sources read:

- `Field`, `Mathlib.Algebra.Field.Defs` (def-weil-field).
- `AlgebraicGeometry.Scheme`, `IsAffine`, `LocallyOfFiniteType`, and `QuasiCompact`,
  Mathlib algebraic-geometry scheme/affine and morphism files, per the convention-only
  def-weil-pbc-scheme-conventions; the finite-type convention is the conjunction above.
- `AlgebraicGeometry.IsIntegral`, `Mathlib.AlgebraicGeometry.Properties`
  (def-pc-integral-scheme).
- `AlgebraicGeometry.IsNormalScheme`, `Sheaf.AlgebraicGeometry.NormalScheme`
  (def-sbc-normal-dominant-galois).
- `AlgebraicGeometry.Scheme.functionField`, `Mathlib.AlgebraicGeometry.FunctionField`,
  imported through the recorded `Sheaf.AlgebraicGeometry.FunctionField`. The integral
  scheme clause of def-sc-function-field explicitly uses this existing generic stalk;
  its component-product declaration is unnecessary in this integral case.
- `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`, imported through the recorded
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` (def-weil-algebraic-closure).
- `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (def-pc-fibre-product).
- `CategoryTheory.constantSheaf`, `Mathlib.CategoryTheory.Sites.ConstantSheaf`, as
  specified by def-kun-constant-sheaf's recorded specialization. Its recorded
  `Mathlib.Algebra.Homology.Additive` is imported too; no arbitrary complex is needed
  because the node uses a sheaf in degree zero.
- `AlgebraicGeometry.Etale.invertibleTorsionOrders`,
  `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders` (def-kun-torsion-invertible).
- `AlgebraicGeometry.Etale.lowerStar`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
  (def-weil-pbc-direct-image), with Mathlib's `Functor.rightDerivedFunctorPlus`,
  `DerivedCategory.Plus.singleFunctor`, and `DerivedCategory.Plus.homologyFunctor`.
  The current source uses the generic derived-functor API; the older recorded alias
  `rightDerivedLowerStarPlus` is not needed. Enough injectives is inferred from existing
  imports, with no extra assumption in the signature.

All recorded proof-dependency modules are imported when stated. `lem-kun-0f1h` and
`sk-def-exchange` have no Lean record yet and therefore no import to add. To retain the
required import of the recorded `Sheaf.RingTheory.ColimOfLocalizations`, this file uses
Lean's legacy import format, matching that dependency: a `module` file fails with
“cannot import non-`module` Sheaf.RingTheory.ColimOfLocalizations from `module`”, even
with `import all`. The compiling file keeps the full proof import plan, uses ordinary
`import` lines, and sets `autoImplicit false` explicitly. This compatibility issue is
reported for the maintainer; no live dependency was modified or restated.

Edge cases checked before accepting the statement:

- `d=1`, including `n=1`, gives the zero cyclic coefficient sheaf and is included.
- `d=0` cannot divide the positive `n.val`; there is no missing Z-coefficient case.
  Divisors are positive natural orders, as the DAG proof specifies. Negative integer
  divisors give the same cyclic groups via absolute value.
- Empty X is allowed; both fibre products and the sheaf on the empty scheme remain
  defined. Empty S' is correctly excluded by the node's integrality hypothesis.
- `q=0` is deliberately excluded: a generic direct image need not vanish in degree zero.
  Every positive integer degree is included without an upper bound.
- If S' is already an algebraically closed field spectrum, its canonical generic map
  and the same pullback expression are still defined; the assertion is consistent
  with positive cohomology of the identity projection vanishing.
- Characteristic zero and positive characteristic are both allowed. In characteristic
  p the subtype excludes precisely the n divisible by p; no perfectness or algebraic
  closedness of K is imposed.
- S' need not be Noetherian or finite type, and X need not be separated or reduced.
- The explicit `universe u` works at every scheme universe. Coefficients are lifted to
  `AddCommGrpCat.{u+1}`, the existing small-etale-site convention, without requiring an
  equality of object and morphism universes or a new site definition.

Searches made through the prescribed launcher tool (actual results in searches.jsonl):

- LeanFinder: “Higher direct images of constant cyclic etale sheaves vanish under
  generic fibre projection over affine normal integral scheme with algebraically
  closed function field”. Eight hits on affine-transition-limit sections, etale
  algebras, and scheme module categories; none states this vanishing.
- Loogle: `"functionField"`. Twelve hits, including `Scheme.functionField`, its field
  instance and the affine fraction-field theorem. These provide the canonical notion,
  not an exact match for the item.
- Mathlib grep: `higherDirectImage|punctual_base_change|normal.*functionField`,
  subdirectory AlgebraicGeometry. Zero hits.
- LeanSearch: “Vanishing positive higher direct images of constant finite cyclic etale
  sheaves along generic fibre projection over normal integral scheme with algebraically
  closed function field”. Eight hits on group cohomology, affine sections, constant
  sheaves and etale objects; none states this lemma.
- Direct rg of WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `lem-kun-0f1i-normal|isZero_higherDirectImage_constant_genericFibre|normal.*functionField|punctual_base_change`.
  The only item-id hit is its downstream proof docstring in BaseChangeTowardsFields;
  function-field hits concern normalization and curves. No exact existing statement.

Validation: `scompile.py Q06 lem-kun-0f1i-normal
lean/Sheaf/AlgebraicGeometry/NormalGenericFibreVanishing.lean` passed both its sandbox
and library-file checks cleanly under the prescribed 60-second limits. The original
attempt was repaired for legacy-module compatibility and the imports exposing derived
homology, the derived functor, and existing enough-injectives instances. All variables
and universes are explicit; no local notation, local instance, `let`, new axiom, private
copy, or theorem proof beyond `sorry` occurs. No statement correction, new node, or
dependency-interface replacement is required.

## Second reading by Q06

I independently read the sandbox node and module, the current main-20261015 blueprint
statement, Stacks `etale-cohomology.tex` Tag 0F1I (especially lines 20596–20703),
the ten statement dependencies, and their actual declaration sources. No repair note
exists for this item. There is no `statement_change`, new definition node, or dependency
module in the packet. The following is my inventory of the statement, with its Lean
counterpart and verdict; abbreviations in this table are explanatory, not new Lean data.

| Object, hypothesis, or conclusion in the node | Lean counterpart and verdict |
| --- | --- |
| Ground field K | `{K : Type u} [Field K]`. Exact: a field, without an algebraic-closedness or characteristic restriction. |
| Positive integer n invertible in K | `(n : invertibleTorsionOrders K)`. Exact: the opened definition is the subtype of naturals with `0 < n` and `(n : K) ≠ 0`; in a field nonzero means invertible. |
| K-schemes X and S' | `(X S' : Scheme.{u})` and their two `Over (Spec (.of K))` instances. Exact: the structure maps are `X ↘ Spec (.of K)` and `S' ↘ Spec (.of K)`. |
| X of finite type over K | `LocallyOfFiniteType` and `QuasiCompact` on its structure map. Exact: both are required by the recorded scheme conventions; this adds neither separatedness nor reducedness. |
| S' affine | `[IsAffine S']`. Exact: Mathlib's canonical global-sections spectrum map is an isomorphism. |
| S' integral | `[IsIntegral S']`. Exact: nonempty and domain sections on nonempty opens, equivalent to the dependency's affine-open formulation. |
| S' normal | `_hnormal : IsNormalScheme S'`. Exact: the opened definition is integrality together with every stalk an integrally closed domain. Repeating integrality as an instance adds no mathematical hypothesis. |
| Algebraically closed function field L of S' | `[IsAlgClosed S'.functionField]`. Exact: `Scheme.functionField` is the generic stalk, with its field instance supplied by integrality. The function-field dependency explicitly records this general integral-scheme clause; its component-product construction is not used instead. |
| X' = X times_K S' | `pullback (X ↘ Spec (.of K)) (S' ↘ Spec (.of K))`. Exact chosen fibre product. |
| Canonical Spec L to S' | `S'.fromSpecStalk (genericPoint S')`. Exact: its source is definitionally `Spec S'.functionField`; it is the canonical stalk morphism, not an arbitrary field-valued point. |
| Y = X' times_{S'} Spec L | The second `pullback`, of `pullback.snd` and the preceding canonical stalk morphism. Exact. |
| Projection h : Y to X' | `pullback.fst` for that second pullback. Exact orientation and target. |
| Every q > 0 | `(q : ℤ) (_hq : 0 < q)`. Exact, all positive cohomological degrees. |
| Every divisor d of n | `(d : ℕ) (_hd : d ∣ n.val)`. Exact positive orders: zero cannot divide positive n, and a negative integer divisor defines the identical quotient group as its absolute value. |
| Constant abelian sheaf Z/dZ on Y | `constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}` at `AddCommGrpCat.of (ULift.{u + 1} (ZMod d))`, with Y expanded. Exact sheafification of the constant presheaf, in the abelian coefficient category. |
| Higher direct image R^q h_* | `DerivedCategory.Plus.homologyFunctor` in degree q of `(lowerStar ... h).rightDerivedFunctorPlus` applied to `DerivedCategory.Plus.singleFunctor _ 0` of the constant sheaf. Exact derived direct image of a degree-zero sheaf. |
| Vanishes | `CategoryTheory.Limits.IsZero` in the category of abelian sheaves on X'. Exact zero-object assertion, without a stalk-only or global-cohomology weakening. |

The source's final reduction writes function field K, but its displayed diagram uses
Spec L and the next paragraph states that L is Frac B. The current blueprint and node
consistently use L; the Lean follows that meaning. Although the preceding Stacks
reduction replaces K by its algebraic closure, no such hypothesis is needed for this
isolated lemma: Tag 0F1H, whose statement I also read at lines 20402–20417, assumes
only that K is a field. The node's approximation argument applies that general lemma.
Thus imposing `[IsAlgClosed K]` here would be an extra hypothesis.

I opened `NormalScheme`, `FunctionField`, `InvertibleTorsionOrders`, Mathlib's
`IsIntegral`, `IsAffine`, finite-type and quasi-compact definitions, the chosen
pullback/projections, `IsAlgClosed`, and `constantSheaf`. I also read the upstream
`Etale.lowerStar` signature and construction: sections are evaluated on the etale
base change, precisely as the direct-image dependency says. The Mathlib derived
functor, single functor, and homology functor supply the dependency's bounded-below
interpretation; enough injectives and sheafification instances are inferred, with no
extra binders. The coefficient lift is an isomorphic copy of Z/dZ, not a new notion.
The recorded obsolete derived alias is not a reason to duplicate this usable API.

Edge cases: empty X is permitted, so both products may be empty. Empty S' is excluded
by the source's integral hypothesis, not by an added assumption. For d=1 (and n=1)
the coefficients are zero and the statement still applies. The subtype excludes n=0;
divisibility excludes d=0. Degree q=0 is deliberately outside the conclusion. If
S'=Spec L, the same canonical generic-stalk map is defined and positive higher images
are consistent with the identity case. Characteristic zero and every positive
characteristic are allowed; in characteristic p precisely orders divisible by p are
excluded. There is no index-set binder or nonemptiness hypothesis to check. The theorem
is polymorphic in u; the small-etale coefficients use the established u+1 convention,
without an extra universe equality. S' need not be Noetherian or of finite type.

Independent searches, recorded by `msearch.py` in `searches.jsonl`:

- LeanFinder: “Positive degree derived pushforward of a cyclic constant sheaf vanishes
  for the generic point inclusion after product with a finite type scheme”. Eight hits
  about sections and affine transition limits; no matching higher-image theorem.
- Loogle: `"constantSheaf", "IsZero"`. Zero hits.
- LeanSearch: “Higher direct image vanishing for the constant finite abelian group sheaf
  over the algebraically closed generic stalk of an affine normal integral scheme”.
  Eight hits about affine sections, stalks and finite morphisms; no exact match.
- Direct `rg` in Mathlib algebraic geometry, upstream `WeilConjectures`, shared
  `lean/Sheaf`, and `dag/lean_names_upstream.json` used `generic[Ff]ibre`,
  `generic[Ff]iber`, `isZero.*constant`, `constant.*isZero`, and normal/direct-image
  combinations. I opened the nearby upstream curve-test vanishing and
  `isZero_higherDirectImage_constantModSheaf_of_forall_exists` signatures: one is a
  smooth-curve datum, the other requires local killing of all cohomology classes.
  Neither states this product/generic-stalk vanishing. The shared finite-submodule
  vanishing lemma assumes vanishing for every finite submodule and is likewise not
  this result. The exact proposed name has no existing declaration; the item id
  occurs only in the downstream `BaseChangeTowardsFields` proof docstring.

No mathematical mismatch was found, so I kept the Lean and node unchanged and added
only this second-reading report. The module and theorem docstrings name the source
and blueprint id; the theorem's seven numbered proof steps match the node, including
the repeated-base colimit, construction of all four limits, compatible coefficients,
cohomological exchange, limit passage, and final field-spectrum vanishing. Its only
theorem proof is `sorry`; it defines no hollow object or private copy. All recorded
statement/proof modules are present as imports; `lem-kun-0f1h` and `sk-def-exchange`
still have no recorded modules. I retained the documented legacy import format
required by `ColimOfLocalizations`. Every variable and universe is bound explicitly,
`autoImplicit` is false, and every Lean line is at most 100 characters.

Verification: the signature extracted from the theorem keyword through the conclusion
is verbatim equal to `lean.statement`. Independently reran `scompile.py Q06
lem-kun-0f1i-normal lean/Sheaf/AlgebraicGeometry/NormalGenericFibreVanishing.lean` from
the sandbox: sandbox and library-file checks both passed, with no errors or warnings
(3.9 s and 6.0 s respectively), under the wrapper's unchanged 60-second limits.
