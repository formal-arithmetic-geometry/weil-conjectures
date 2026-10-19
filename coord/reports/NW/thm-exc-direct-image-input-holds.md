## Worker report

The delivery states the existing prerequisite `def-exc-direct-image-input` and then
states `thm-exc-direct-image-input-holds`.

## Dependency modules

`def-exc-direct-image-input` had no Lean declaration or Mathlib match in the shared
DAG. Its copied node changes only the `lean` record, with the note recording this
§1(A) repair. `DirectImageFinitenessInput.lean` defines
`AlgebraicGeometry.Scheme.HasDirectImageFinitenessInput` with the two clauses from the
node. Clause (1) quantifies over finite-type morphisms of finite-type schemes over
`k`, a constructible sheaf of `Λ`-modules, and every natural degree; it uses the
canonical `Etale.rightDerivedLowerStar`, `DerivedCategory.singleFunctor`, and
`DerivedCategory.homologyFunctor`, and requires the resulting sheaf to be
`Scheme.IsConstructibleEtaleModuleSheaf`. Clause (2) quantifies over a separably
closed field `K` with `N` invertible, finite-type `K`-schemes of dimension at most
`d`, and states `HasTorsionEtaleCohomologicalDimensionLE W (2 * d)`, which expands to
vanishing for every torsion étale sheaf in degrees above `2*d`.

The item module states
`AlgebraicGeometry.Scheme.hasDirectImageFinitenessInput_of_isSepClosed` with a
separably closed `k`, an integer `N` represented by `IsUnit (N : k)`, and a finite
commutative ring `Λ` annihilated by `N`. Its conclusion is exactly the prerequisite
predicate. The proof is `sorry`, as required for stage 2. The docstring records the
planned use of `isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field`,
`hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`, and
`hasTorsionEtaleCohomologicalDimensionLE_of_finiteType`.

## Dependencies used

- `def-weil-pbc-etale-sheaves`: `CategoryTheory.Sheaf.IsTorsion` and the étale sheaf
  conventions used by the torsion cohomological-dimension predicate.
- `def-weil-pbc-scheme-conventions`: the scheme and finite-type morphism conventions.
- `def-sc-etale-torsion-cd`: `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
- `def-weil-pbc-constructible-complexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `thm-dg-finite-type-constructibility`:
  `AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field`.
- `lem-sf-separably-closed-torsion-cd`:
  `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`.
- `thm-sc-finite-type-torsion-cd`:
  `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_finiteType`.

## Edge cases checked

The zero ring and zero sheaf satisfy the annihilation and constructibility clauses;
`q = 0` is included by the natural-degree quantifier; `d = 0` gives the expected
positive-degree vanishing; and the empty scheme is covered by the dimension inequality
and the torsion cohomological-dimension predicate. Characteristic zero is represented
correctly because `IsUnit (N : k)` holds for every positive `N` there, while in positive
characteristic it expresses primeness to the characteristic.

## Searches

- `msearch.py ... leanfinder "direct image finiteness input constructible higher direct image torsion cohomological dimension"`: 8 generic derived-category hits, no exact predicate.
- `msearch.py ... loogle "rightDerivedLowerStar, IsConstructibleEtaleModuleSheaf, HasTorsionEtaleCohomologicalDimensionLE"`: 0 hits; `rightDerivedLowerStar` unknown to Loogle.
- `msearch.py ... grep "direct.?image.?finiteness|HasDirectImageFinitenessInput" Mathlib/AlgebraicGeometry`: 0 hits.
- `rg` over `lean/Sheaf` and `WeilConjectures/` found no `HasDirectImageFinitenessInput` or item declaration.
- `tools/blueprint_refs.py search def-exc-direct-image-input` found only the existing definition node and this item; the existing node had no Lean record.

No `STATEMENT-DISPUTED` flag or statement correction is needed.

## Earlier second reading (a previous round; superseded)

I re-read the prerequisite definition and the theorem against the DAG statements.
Clause (1) retains the finite-type scheme and morphism hypotheses, the constructible
`Λ`-module sheaf, and every nonnegative degree. Clause (2) retains arbitrary torsion
abelian étale sheaves through `HasTorsionEtaleCohomologicalDimensionLE`, with the
`2*d` bound and the dimension-at-most hypothesis. The `IsUnit (N : k)` hypothesis is
the characteristic-prime condition, including characteristic zero. The dependency
repair is necessary because the existing DAG prerequisite had no Lean declaration;
its module uses the canonical derived direct image and does not weaken either clause.
Both delivered files were compiled with `scompile.py` and have no compiler warnings.

## Second reading by N8

I independently opened both copied node records, both delivered Lean modules, the
recorded dependency declarations and their bodies, and the original blueprint
`sk-prop-a1-kummer/thm-exc-direct-image-input-holds.md` and
`sk-prop-a1-kummer/def-exc-direct-image-input.md` on the project server (the
blueprint source files are absent from this machine's shared mirror). The source
has exactly the two ordinary-image clauses in the DAG. The unit section introduces
no extra separatedness or algebraic-closedness hypothesis for this general input.
I also read the source discussion and the Stacks TeX at Tag 0F0P
(`etale-cohomology-section-cd`), including Tag 0F0V
(`etale-cohomology-proposition-cd-affine`), and Tag 0GL0
(`more-etale-theorem-constructible-shriek`). The last is a compact-support theorem,
not the ordinary-direct-image theorem; I have not imported its separatedness
hypothesis into this item. The item's proof correctly uses the separately recorded
ordinary-image theorem `thm-dg-finite-type-constructibility`. Finite-type schemes over
a field are Noetherian, so the quasi-compact/quasi-separated conventions in the
cohomological-dimension source add no missing assumption here.

The object/hypothesis/conclusion checklist, against the final Lean, is:

| Node object or clause | Lean rendering and verdict |
| --- | --- |
| A separably closed field `k` | `(k : Type u) [Field k] [IsSepClosed k]`. Exact; no algebraically closed, perfect or finite-field assumption. The dependency predicate itself only assumes `[Field k]`, as its definition node requires. |
| An integer `N` prime to the characteristic | `(N : ℤ) (hN : IsUnit (N : k))`. Repaired from `ℕ`: signed integers, including negative annihilators, now have the source's domain. Invertibility is the intended characteristic condition in both the blueprint proof and the coefficient dependencies. |
| A finite commutative ring annihilated by `N` | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hΛ : ∀ a : Λ, N • a = 0)`. Exact; signed scalar multiplication is now integer scalar multiplication. No field or nontrivial-ring hypothesis on Λ. |
| Both clauses hold over `k` | `HasDirectImageFinitenessInput k N hN Λ hΛ`. Its actual body is the conjunction audited below; it does not assume either desired clause. |
| Clause 1: arbitrary finite-type `k`-schemes `S,T` | `{S T : Scheme.{u}}`, their structure maps `aS,aT`, and `[LocallyOfFiniteType aS] [QuasiCompact aS]` and the corresponding two instances for `aT`. Exactly the finite-type convention of `def-weil-pbc-scheme-conventions`. |
| A finite-type morphism `u : S → T` over `k` | `(uST : S ⟶ T) [LocallyOfFiniteType uST] [QuasiCompact uST] (_hu : uST ≫ aT = aS)`. Exact. The equality says it is a morphism of the specified `k`-schemes. No separatedness, properness or smoothness requirement. |
| Any constructible Λ-module sheaf on `S_et` | `(F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (_hF : IsConstructibleEtaleModuleSheaf F)`. Exact, using the recorded finite-stratification, finite-constant-module-value predicate; not the upstream, differently formulated stalk predicate. |
| Every degree `q ≥ 0` | `(q : ℕ)` and the cast `(q : ℤ)`. Exact, including zero. |
| Constructibility of `R^q u_* F` | `IsConstructibleEtaleModuleSheaf` of `DerivedCategory.homologyFunctor ... (q : ℤ)` applied to `Etale.rightDerivedLowerStar ... uST` of `DerivedCategory.singleFunctor ... 0` applied to `F`. Exact ordinary higher direct image of a sheaf in degree zero. |
| Clause 2: every separably closed field `K` with `N` invertible | `(K : Type u) [Field K] [IsSepClosed K] (_hK : IsUnit (N : K))`. Exact: `K` is quantified independently of `k`; no field extension or algebra structure is assumed. |
| Any nonnegative bound `d` and finite-type `K`-scheme `W` | `(d : ℕ) (W : Scheme.{u}) (aW : W ⟶ Spec (.of K))` with locally-finite-type and quasi-compact instances. Exact. |
| Dimension at most `d` | `topologicalKrullDim W ≤ (d : WithBot ℕ∞)`. Exact inequality, not an exact-dimension or nonempty hypothesis. |
| Vanishing for all torsion abelian sheaves and all `q > 2d` | `HasTorsionEtaleCohomologicalDimensionLE W (2 * d)`. Opening its definition gives `∀ F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u+1}, F.IsTorsion → ∀ q : ℕ, 2*d < q → Subsingleton (...)`. This is exactly zero cohomology of the abelian group; it neither restricts to constructible sheaves nor requires `N` or another common integer to annihilate `F`. |

Dependency and one-definition audit:

- `DirectImageFinitenessInput.lean` supplies the already existing DAG definition
  `def-exc-direct-image-input`, which has no published usable Lean record in the
  base. It is not a new definition node or a private duplicate of another node.
  Its only node delta is `lean`. I read its complete conjunction against both the
  source and the definition-node statement, as itemized above.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` defines
  `Scheme.IsConstructibleEtaleModuleSheaf` by a finite locally closed constructible
  stratification and étale local trivializations with finite module values. This is
  the notion used by `def-weil-pbc-constructible-complexes` and the delivered predicate.
  I read `BoundedConstructibleComplexes.lean`: its first conjunct is precisely this
  predicate on every `DerivedCategory.homologyFunctor` cohomology sheaf.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs.lowerStar` is objectwise
  evaluation on the base change of an étale object. Its canonical
  `Etale.rightDerivedLowerStar` in `Derived.UpperLowerStarCoherence` is the ordinary
  right-derived functor of that pushforward. The unbounded functor here is applied
  only to a sheaf in degree zero, so computes the same ordinary higher direct images
  as the bounded-below convention. The upstream `Etale.higherDirectImage` spelling
  uses the bounded-below version; it does not define the conjunction at issue.
- `Sites.CohomologicalDimension.HasTorsionEtaleCohomologicalDimensionLE` is a genuine
  universal vanishing predicate. I read `CategoryTheory.Sheaf.IsTorsion` in upstream
  `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic`: every section has locally
  finite additive order on a covering sieve. It does not demand torsion of the
  entire section group, finite stalks, or a fixed annihilator.
- I opened the three proof dependencies. The finite-type constructibility theorem
  uses the same `DerivedCategory.isBoundedConstructible` predicate and ordinary
  derived pushforward, and permits nonseparated morphisms. Its coefficient input
  `IsSmoothBaseChangeCoefficients` uses a positive natural annihilator. For signed
  `N`, its absolute value is positive, kills Λ and is invertible; the affine global
  sections identification of `Spec k` supplies its global-section unit condition.
  The separably closed-field theorem gives torsion cd at most zero without a fixed
  annihilator. The finite-type theorem requires exact dimension `e`; the node's
  empty-case and `e ≤ d` argument, now explicit in the theorem docstring, gives the
  required at-most bound. No dependency theorem is used as a hypothesis of this item.

Edge cases: the zero ring is admitted by `[CommRing Λ] [Finite Λ]`, and zero
sheaves are admitted by the genuine constructibility predicate. Empty `S`, `T`,
and `W` are not excluded. The dimension value of the empty scheme is covered by
`WithBot ℕ∞`; the proof docstring explicitly treats that case before selecting a
natural exact dimension. The finite stratification permits zero strata. `q = 0`
is included in clause 1, and `d = 0` in clause 2 requests vanishing only in positive
degrees. Both signs of `N`, and `N = 1` and `N = -1`, are now included. `N = 0`
cannot satisfy invertibility in a field, as intended. In positive characteristic,
`IsUnit (N : k)` excludes multiples of the characteristic; in characteristic zero
it permits exactly nonzero integers, the invertibility convention used by the
source proof. No index set with a nonempty assumption occurs. `u` is arbitrary,
not zero; `Scheme.{u}`, its small étale site, coefficients in `ModuleCat.{u+1} Λ`
and `AddCommGrpCat.{u+1}` follow the opened dependency interfaces and the recorded
coefficient-size convention. There is no additional universe equality assumption
or bound on cardinality. `autoImplicit false` and the successful elaboration leave
no unbound variables or universes.

Independent searches, with different terms from the original report:

- `msearch.py N8 thm-exc-direct-image-input-holds leanfinder
  "HasDirectImageFinitenessInput direct image input"`: eight generic functor/finite-set
  hits; no matching predicate or theorem.
- `msearch.py ... loogle '"constructible", "direct"'`: zero hits.
- `msearch.py ... leansearch "Constructibility of higher direct images over a
  separably closed field and torsion cohomological dimension bound"`: service
  unavailable (HTTP Internal Server Error), recorded as unavailable.
- `msearch.py ... grep
  'FinitenessInput|direct.?image.?finiteness|torsion.*cohomological.*dimension'
  AlgebraicGeometry`: zero Mathlib hits.
- Independent `rg` searches for `finitenessinput`, `finiteness_input`, higher direct
  images and torsion dimension in Mathlib, upstream `WeilConjectures/`, and shared
  `lean/Sheaf/` found no existing combined input or theorem. I inspected the actual
  closest upstream result `ProEtale.isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar`:
  it concerns prime-adic pro-étale coefficients over an algebraically closed field,
  not these finite-ring étale coefficients or the torsion-cd conjunction. The shared
  `ConstructibleHigherDirectImage.IsConstructibleHigherDirectImage` is a property of
  one morphism with coefficients on a specified base; it is not this universal
  two-clause input. Existing constructibility and cd notions are reused, not replaced.

Mismatches repaired: the natural-number-only annihilator in both signatures excluded
signed integers literally allowed by the node; changed both to `ℤ` and synchronized
both `lean.statement` strings verbatim. The original proof docstring omitted the empty
scheme, exact-dimension and monotonicity steps of the node's second proof paragraph;
added them, as well as the signed-annihilator reduction and global-section coefficient
check. Expanded the dependency definition's docstring to spell out its two clauses
and precise source. The informal node statements were already correct, so no
`statement_change` or new node is needed. The original worker report is preserved;
this section supersedes its natural-annihilator description.

Validation: compiled both delivered modules together through the required `scompile.py`
wrapper, which compiled each separately in dependency order. Both completed cleanly,
with no errors or warnings. The only theorem proof remains the stage-2 `sorry`, and
the definition is the explicit conjunction with no postponed data or proof inside it.
All Lean lines are at most 100 characters and every declaration has its owning-node
source/blueprint docstring.

## Second reading by NW

This is an independent reading of the current sandbox and current published sources.
The earlier Worker report and N8 reading remain above as history. The final NW
packet reuses an existing declaration and contains no Lean or dependency module.
Their previous descriptions of this packet as supplying a missing definition are
superseded: the exact definition and theorem are now already published.

I read the item and prerequisite node, both complete module sources, the recorded
statement/proof dependencies, the original blueprint theorem, definition, source
remark and enclosing unit on the project server. I also read the Stacks TeX for
Tags 0F0P and 0F0V, and the statement at Tag 0GL0. The first two use ordinary torsion
cohomology; the last is about Rf_!, so its separatedness assumption is not an
assumption of the ordinary-image theorem used here. Finite-type schemes over a
field are Noetherian and hence qcqs, satisfying the size/topology hypotheses of
the cohomological-dimension source. The unit's separate affine-line statements
about separated schemes do not restrict this explicitly general input theorem.

Object, hypothesis and conclusion checklist (each verdict is exact):

| Node object, hypothesis or clause | Lean rendering and verdict |
| --- | --- |
| Separably closed field k | `(k : Type u) [Field k] [IsSepClosed k]`; exact. |
| Signed integer N invertible in k | `(N : ℤ) (hN : IsUnit (N : k))`; exact characteristic condition used by the source proof. |
| Finite commutative coefficient ring | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`; exact, without a nontriviality or field assumption. |
| Every element annihilated by N | `(hΛ : ∀ a : Λ, N • a = 0)`; exact integer scalar multiplication. |
| Both direct-image input clauses | `HasDirectImageFinitenessInput k N hN Λ hΛ`; its complete conjunction was opened and checked below. |
| Clause 1: arbitrary finite-type k-schemes S,T | `{S T : Scheme.{u}}`, `aS`, `aT`, and `[LocallyOfFiniteType aS] [QuasiCompact aS]` and corresponding instances for `aT`; exact finite-type convention. |
| Finite-type k-morphism u:S→T | `uST`, `[LocallyOfFiniteType uST] [QuasiCompact uST]`, and `_hu : uST ≫ aT = aS`; exact, with no separation/properness hypothesis. |
| Constructible Λ-module sheaf F | `F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)` with `IsConstructibleEtaleModuleSheaf F`; exact recorded module-sheaf encoding and constructibility predicate. |
| Every nonnegative degree q | `(q : ℕ)` and `(q : ℤ)`; exact, including zero. |
| Constructibility of ordinary R^q u_*F | `IsConstructibleEtaleModuleSheaf` of homology degree q of `Etale.rightDerivedLowerStar ... uST` applied to `DerivedCategory.singleFunctor ... 0` of F; exact. |
| Clause 2: every separably closed field K with N invertible | `(K : Type u) [Field K] [IsSepClosed K] (_hK : IsUnit (N : K))`; independent of k, with no field-extension assumption. |
| Any nonnegative bound d and finite-type K-scheme W | `(d : ℕ)`, `(W : Scheme.{u})`, `aW` and its locally-finite-type/quasi-compact instances; exact. |
| Dimension at most d | `_hd : topologicalKrullDim W ≤ (d : WithBot ℕ∞)`; exact, not an exact-dimension or nonempty assumption. |
| All torsion abelian sheaves, all q>2d, zero cohomology | `HasTorsionEtaleCohomologicalDimensionLE W (2 * d)` expands to all `F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u+1}`, `F.IsTorsion`, all natural q with `2*d < q`, and `Subsingleton` of ordinary cohomology of F in degree zero; exact, without a uniform annihilator. |

Dependency audit: `Etale.lowerStar` is the sheaf pushforward defined by evaluation
on the base-changed etale object. `Etale.rightDerivedLowerStar` is its total right
derived functor; a degree-zero sheaf computes the same ordinary higher direct
images as the recorded bounded-below version. `IsConstructibleEtaleModuleSheaf`
uses the recorded finite locally closed constructible stratification and finite
constant module values. `DerivedCategory.isBoundedConstructible` uses exactly
that predicate on every homology sheaf and bounded vanishing. The torsion predicate
`CategoryTheory.Sheaf.IsTorsion` asks that sections have finite additive order
locally on a covering sieve, not that the entire sections group be torsion.
The dimension predicate uses ordinary derived sections and `Subsingleton` of
the resulting abelian group, which means zero.

I opened all three proof-dependency theorem signatures. The finite-type theorem
allows nonseparated morphisms and uses the same coefficient/sheaf categories.
Its positive natural annihilator is obtained from the absolute value of signed
N, with the unit transported to global sections of Spec k. The separably closed
base case has no uniform-annihilator assumption. The finite-type dimension bound
has an exact-dimension hypothesis; the item's docstring explicitly treats the
empty scheme first, then chooses finite dimension e≤d and uses 2e≤2d. These are
proof ingredients, never extra hypotheses of this item. The complete two-step
proof is retained in the existing theorem's source/blueprint docstring. Its
proof is still the required stage-2 `sorry`; the predicate contains real data
(the displayed conjunction), no `sorry` and no hollow construction.

Edge cases: zero coefficient ring and zero sheaf are admitted. Empty S,T,W are
not excluded; the empty W has bottom dimension and is handled before the proof
chooses an exact natural dimension. q=0 is included; d=0 requests only positive
cohomology vanishing. N may be positive or negative, including ±1. N=0 is excluded
by invertibility in a field. In positive characteristic, divisibility by that
characteristic is excluded; in characteristic zero, every nonzero integer is
invertible, as in the source proof. There is no nonempty index hypothesis. The
universe u is arbitrary, the small-etale sites use Scheme.{u}, and the module and
abelian coefficients use the existing u+1 interfaces. A finite coefficient ring
can be transported to this size; no additional universe equality or cardinality
hypothesis was introduced. Both files bind every variable under autoImplicit false.

Independent searches (NW, with terms different from the first worker's):

- `msearch.py ... leanfinder "HasDirectImageFinitenessInput direct image input"`:
  eight finite-set/subfunctor hits, no matching input theorem or predicate.
- `msearch.py ... loogle "rightDerivedLowerStar IsConstructibleEtaleModuleSheaf"`:
  zero hits; the service does not know rightDerivedLowerStar.
- `msearch.py ... grep 'direct.?image.?finiteness|HasDirectImageFinitenessInput'
  Mathlib/AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch "Constructible ordinary higher direct images and
  torsion etale cohomology dimension over a separably closed field"`: unavailable,
  HTTP Internal Server Error, not counted as a negative result.
- `rg` in Mathlib, upstream WeilConjectures and shared lean/Sheaf for
  `finitenessinput`, `finiteness_input`, `direct.image.finiteness`, higher direct
  image and torsion dimension found the EXACT two published Sheaf modules. I
  independently retrieved both with `scompile.py --source`; they match the
  sandbox copies. I also opened `IsConstructibleHigherDirectImage`, a condition
  on one morphism with positive coefficient conventions, not the conjunction.

Mismatch repaired: H4, duplicate delivery. The published theorem already has the
exact statement, and the published prerequisite already has the exact explicit
conjunction. Set the item lean record to `existing: true`, retained the canonical
module/declaration and newtargets-dag branch, synchronized lean.statement to the
literal multiline source signature, and removed both duplicate module copies and
the unnecessary dependency-node copy from the packet. There is no mathematical
statement change, no new node, and no dependency repair to land. No hypotheses,
quantifiers or conclusions needed repair. No statement_change or citer audit is
required because the informal and Lean statements retain their meaning.

Validation: both original sibling files were passed together to the required
scompile.py wrapper before removing their duplicate copies; each compiled
separately without errors or warnings. The existing declaration is additionally
checked through the delivery wrapper's importing #check probe. The final packet
contains the existing declaration record and this report only.
