## Worker report

The module `Sheaf.CategoryTheory.SmithSmallSaturatedIntersection` states
`CategoryTheory.MorphismProperty.exists_small_generators_intersection`.
The single theorem has proof `sorry`; no definitions, auxiliary theorems, new nodes,
dependency repairs, or statement corrections are needed. The node copy changes only `lean`.
There is no STATEMENT-DISPUTED flag.

I read the complete stage-2 brief, statement-stage rules, section H of delivery-errors,
the worker role, SETUP, GOAL, STATE, tools/README, and the CompactObject example and its
node record. No repair note exists for this item.

The source is Lurie's *Higher Topos Theory*, Lemma A.2.6.9, printed pp. 821–823;
the accessibility convention is Definition A.2.6.2, printed pp. 818–819. I opened the
Harvard PDF and read both statements. The source has exactly the four assumptions
rendered below. The item's completeness assumption is retained, although the source
only requires a presentable category and the proof input needs only cocompleteness.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed small universe and arbitrary ambient category with small Hom sets | `universe u v`, `{A : Type v} [Category.{u} A]`; no relation between object universe `v` and Hom universe `u` is imposed. |
| All small limits and colimits | `[HasLimits A] [HasColimits A]`, whose shape universe is the Hom universe `u`. |
| Locally presentable, as explicitly defined in the node | `[IsLocallyPresentable.{u} A]`; its existential regular cardinal and small cardinal-filtered generator are exactly the node's small set of objects with colimit-preserving Hom functors. |
| Two arbitrary arrow classes | `(C W : MorphismProperty A)`. |
| Arrow category, objects are arrows and maps are commuting squares | Mathlib's `Arrow A`, used by the smallness and colimit-generation predicates. |
| `C` contains all isomorphisms | First conjunct of `hC`, `isomorphisms A ≤ C`. |
| `C` is closed under pushouts | `C.IsStableUnderCobaseChange` in `hC`. |
| `C` is closed under small continuous transfinite compositions | `C.IsStableUnderTransfiniteComposition.{u}` in `hC`. Its shapes range over small well-orders with a first element, and its composites are maps to colimit cocones of well-order-continuous diagrams. |
| `C` is closed under arrow retracts | `C.IsStableUnderRetracts` in `hC`, using Mathlib's `RetractArrow` from the recorded lifting-class dependency. |
| A small subset `C₀ ⊆ C` generates `C` weakly | `hC₀` supplies a morphism property `C₀`, `C₀.IsSmall.{u}`, and `C₀ ≤ C`. Its last clause states `C ≤ D` for every class `D` satisfying all four closure conditions and containing `C₀`. Together with `hC`, this says exactly that `C` is the weakly saturated closure. |
| `C ∩ W` is weakly saturated | `hCW` lists the same four conditions on the infimum `C ⊓ W`, which is pointwise conjunction. |
| Two-out-of-three for composable arrows | `[W.HasTwoOutOfThreeProperty]`; this class combines composition closure, of-precomposition, and of-postcomposition. |
| Some infinite regular cardinal `λ` for the accessibility condition | `hW` supplies `(κ : Cardinal.{u}) (_ : Fact κ.IsRegular)`. The bound variable is named `κ` in Lean. Mathlib's `IsRegular` includes infinitude (`aleph0_le`), and `IsCardinalFiltered` uses the node's cocone condition on diagrams with fewer than `κ` arrows. |
| A small set of arrows in `W` | `hW` supplies `G : ObjectProperty (Arrow A)`, `ObjectProperty.Small.{u} G`, and `∀ f, G f → W f.hom`. A predicate on arrow objects represents a subset; smallness is smallness of its subtype. |
| The full subcategory on `W` is closed under small `κ`-filtered colimits in the ambient arrow category | For every `I : Type u` with `[SmallCategory I] [IsCardinalFiltered I κ]`, `hW` gives `ObjectProperty.IsClosedUnderColimitsOfShape (fun f : Arrow A ↦ W f.hom) I`. This uses arbitrary colimit cocones, including their isomorphic copies. |
| That subcategory is generated under those colimits by `G` | For each `f : Arrow A` with `W f.hom`, the last clause of `hW` supplies a small `κ`-filtered `I` and `G.colimitsOfShape I f`. By its definition this is a colimit presentation of `f` whose diagram objects all satisfy `G`. It imposes no additional presentability condition on `G`. |
| There exists a small subset `S ⊆ C ∩ W` | The conclusion supplies `(S : MorphismProperty A)`, `S.IsSmall.{u}`, and `S ≤ C ⊓ W`. |
| `S` generates the intersection as a weakly saturated class | The final universal clause puts `C ⊓ W` in every weakly saturated class `D` containing `S`. The intersection is itself weakly saturated by `hCW`, so this is precisely equality with the smallest such class. |

Dependency declarations read and used:

- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, `Cocone`, `IsColimit`, `colimit.desc`, and `IsFiltered`.
  I read the chosen-colimit dual declarations, the cocone structure, the full universal
  property, and the filtered-category definition. The statement uses the universal
  property through Mathlib's `ObjectProperty.colimitsOfShape` and colimit closure.
- `lem-coef-lifting-class-closure` is a Mathlib leaf with no `lean` record.
  Its `mathlib_match` names `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`:
  `llp_isStableUnderRetracts`, `rlp_isStableUnderRetracts`,
  `llp_isStableUnderCobaseChange`, and `llp_isMultiplicative`. I read their signatures,
  `llp`/`rlp`, and the imported `IsStableUnderRetracts` interface. The same Mathlib
  arrow-retract and pushout predicates occur in the statement; no copy is introduced.
- The proof dependency `lem-coef-accessible-intersection-generators` has neither a
  recorded declaration nor a Mathlib match in the shared snapshot. Its whole statement
  was read. It is not needed to type this item, and there is no stated module to import.
  The theorem docstring preserves all three DAG proof steps, including the verification
  of that input's additional repleteness hypothesis. No unrecorded postponed helper is
  introduced. If that proof dependency is stated later, its proof import can be added
  by the maintainer under the standard proof-import rule.

Other Mathlib interfaces inspected and reused are `MorphismProperty.IsSmall`
(`Mathlib.CategoryTheory.MorphismProperty.IsSmall`), continuous transfinite composition
(`Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition`), and
`IsLocallyPresentable`, `ObjectProperty.colimitsOfShape`, and
`ObjectProperty.IsClosedUnderColimitsOfShape` from the local-presentability import
closure. The module adds only the main theorem and binds every universe and variable
explicitly with `autoImplicit false`.

Edge cases checked mathematically:

- The terminal category allows an empty generating subset: the universal containment
  conditions correctly give the class of isomorphisms, and smallness requires no
  nonempty generator. The conclusion also permits `S` to be empty.
- For the isomorphism class in `Set`, the empty set again generates it by weak saturation.
  The hypotheses and conclusion impose no artificial generator nonemptiness.
- For the class of all maps in `Set`, the statement retains full arrow-colimit closure
  and unrestricted small sets of generators; no finiteness or countability restriction
  has been introduced.
- Zero-length transfinite compositions are isomorphisms and are included by the
  explicit isomorphism conjunct. All small successor and limit lengths are covered
  by Mathlib's transfinite-composition predicate.
- Empty filtered indexing categories do not slip through: `IsCardinalFiltered` for
  an infinite regular cardinal includes the empty-diagram cocone requirement and
  therefore nonemptiness. Neither small subset itself is assumed nonempty.
- The empty ambient category fails the required initial/terminal objects. No extra
  nonemptiness hypothesis is needed, and no supported case is excluded.
- All index categories and cardinals use the fixed small universe `u`; the object
  universe remains independent. Neither accessibility nor local presentability becomes
  a vacuous condition through an independent smaller index universe.
- No separate repleteness assumption is added to `W`: the proof plan derives it from
  weak saturation of the intersection and two-out-of-three, as the DAG specifies.

Searches for an existing statement and notions (all rerun for this delivery):

- `msearch.py`, LeanFinder: “A small generating set for a weakly saturated class
  intersected with an accessible class satisfying two out of three”. Eight hits,
  including `IsCardinalAccessibleCategory.toHasCardinalFilteredGenerator`,
  `ObjectProperty.IsCardinalFilteredGenerator`, and
  `HasCardinalFilteredGenerator.exists_small_generator`. I read the local generator
  and local-presentability source signatures; these define/generate accessible
  categories, not weakly saturated intersections, so none is this theorem.
- `msearch.py`, Loogle: `"IsLocallyPresentable", "HasSmallObjectArgument"`.
  Zero hits.
- `msearch.py`, grep of Mathlib `CategoryTheory`:
  `IsStableUnderTransfiniteComposition|WeaklySaturated`. Seventeen hits, identifying
  the reusable transfinite-composition interface. No weak-saturation intersection theorem.
- `msearch.py`, LeanSearch: “Weakly saturated intersection of accessible weak
  equivalences has a small generating set”. Eight hits, including the reusable
  `MorphismProperty.IsSmall.small_toSet`, filter intersection lemmas, a small weakly
  initial set, and model-category weak-equivalence interfaces. None supplies the
  intersection theorem; `IsSmall` was reused.
- Direct `rg` of Mathlib's CategoryTheory sources for definitions of weak saturation
  finds no general combined predicate. Direct searches for
  `Smith|saturated_intersection|small_generators_intersection` find no such theorem;
  Smith-normal-form hits are unrelated.
- Direct `rg` of `WeilConjectures/` for `Smith`, `weaklySaturated`, `WeaklySaturated`,
  and the exact item id finds no declaration. The upstream declaration-name index
  has no match for the proposed theorem name or item id.
- Direct `rg` of `lean/Sheaf/` for the same weak-saturation concepts finds
  `SSet.Enhanced.WeaklySaturated` in `PushoutJoinSaturation.lean`, whose full definition
  was read. It has domain `MorphismProperty SSet` and cannot represent an arbitrary
  `A`. The theorem writes its four existing Mathlib predicates directly instead of
  creating another combined definition. The Smith-normal-form occurrence is unrelated.
- Direct search in `dag/nodes/` finds the already recorded, replete formulation
  `lem-coef-accessible-intersection-generators`, which is the item's proof dependency;
  it has no Lean declaration. No exact existing declaration was found.

Validation: `scompile.py Q36 lem-coef-smith-small-saturated-intersection` compiled the
module successfully in both sandbox and library-path checks, with no errors or warnings.
The file has no lines over 100 columns. The node's `lean.statement` was extracted from
the theorem keyword through the signature immediately before `:= by`, preserving its
newlines verbatim. The required `deliver2.py --no-push` dry run is the final check;
the independent second reader will write the second-reading section and deliver.

## Second reading by Q36

I independently opened the item node, its Lean module, the recorded dependency nodes, and the
source at Lurie, *Higher Topos Theory*, Appendix A, Definition A.1.1.2 and Lemma A.2.6.9
(printed pp. 788--789 and 821--823). The source lists exactly four assumptions: (1) `C` is
weakly saturated and generated by a small subset `C₀`; (2) `C ∩ W` is weakly saturated;
(3) the full arrow subcategory on `W` is accessible; and (4) `W` has two-out-of-three. Its
conclusion is a small `S ⊆ C ∩ W` generating that intersection weakly saturatedly. The
node additionally spells out the fixed-universe, small-Hom, limits/colimits, regular-cardinal,
filteredness, arrow-category, and weak-saturation conventions, so I checked those explicit
clauses against the Lean signature rather than relying on the theorem name.

The Lean renders the node item by item as follows. The fixed universe and ambient category are
`universe u v`, `{A : Type v}`, and `[Category.{u} A]`, so Hom types are in the fixed small
universe while the object universe is independent. `[HasLimits A] [HasColimits A]` supplies the
node's all-small-limits/all-small-colimits hypothesis, and `[IsLocallyPresentable.{u} A]`
supplies the local-presentability hypothesis at the same universe. The arrow classes are
`(C W : MorphismProperty A)`, and `Arrow A` is used in the accessibility clauses, hence its
objects are arrows and its morphisms are commuting squares. The four weak-saturation clauses
for `C` are exactly the four conjuncts of `hC`: `isomorphisms A ≤ C`,
`C.IsStableUnderCobaseChange`, `C.IsStableUnderTransfiniteComposition.{u}`, and
`C.IsStableUnderRetracts`. The small generating subset and its universal weak-saturation
property are exactly `hC₀`: `C₀.IsSmall.{u}`, `C₀ ≤ C`, and containment of `C` in every
class `D` satisfying the same four closure clauses and containing `C₀`.

The intersection hypothesis is `hCW`, with the same four clauses applied pointwise to
`C ⊓ W`. The two-out-of-three assumption is the typeclass
`[W.HasTwoOutOfThreeProperty]`. The accessibility assumption is `hW`: it supplies a
cardinal `κ : Cardinal.{u}` with `Fact κ.IsRegular`, a small arrow-object property `G`,
`G ≤ W` expressed as `∀ f : Arrow A, G f → W f.hom`, closure of the full `W` property
under every `[SmallCategory I] [IsCardinalFiltered I κ]` colimit in `Arrow A`, and a
`G.colimitsOfShape I f` presentation for every `W` arrow. Thus the source's accessible
subcategory condition is represented without an extra presentability or nonemptiness
hypothesis. The conclusion is exactly a small `S : MorphismProperty A` with
`S.IsSmall.{u}`, `S ≤ C ⊓ W`, and the universal weak-saturation containment clause for
`C ⊓ W`.

I checked the recorded dependencies. `def-weil-pbc-category-colimit` is the Mathlib
`CategoryTheory.Limits` colimit interface used by the source convention; the lifting-class
closure dependency is the recorded Mathlib `LiftingProperty` interface, and the Lean file uses
its `IsStableUnderCobaseChange`, `IsStableUnderTransfiniteComposition`, and arrow-retract
notions directly. The proof dependency `lem-coef-accessible-intersection-generators` has no
Lean declaration on the base; it is a statement-only DAG input and is used only in the
postponed proof plan, so no private replacement or dependency module was introduced.

Edge cases checked: `S` and `C₀` may be empty; no `Nonempty` assumption is added. The terminal
category and the isomorphism class in `Set` admit empty generators. The all-maps class in `Set`
is permitted. Zero-length transfinite compositions are covered by the explicit isomorphism
clause. `IsCardinalFiltered` supplies the required cocone condition, including the empty
small-diagram case. The empty ambient category cannot satisfy the required colimit/local
presentability instances, so it is not spuriously admitted. The object universe `v` is not
identified with the Hom/index universe `u`, and the cardinal and filtered indexing types use
the fixed universe `u`; `n = 0` and characteristic cases are irrelevant to this categorical
statement.

I reran the existing-definition searches: LeanFinder/LeanSearch/Loogle queries for Smith or
weakly saturated accessible intersections, `rg` over Mathlib CategoryTheory, `rg` over the
upstream `WeilConjectures/`, and `rg` over the repository's `lean/Sheaf/`. They found only the
reusable Mathlib closure/accessibility interfaces and unrelated simplicial weak-saturation
material; no declaration states this theorem. The only DAG overlap is the statement-only
`lem-coef-accessible-intersection-generators` input, which is not an existing Lean declaration.

No mismatch was found between the node and the Lean signature. I made no source, statement,
dependency, or module changes. The module remains a single postponed theorem with the required
source and blueprint docstrings, explicit binders, and no local notation or private copy.
