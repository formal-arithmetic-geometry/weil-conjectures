## Worker report

The module `lean/Sheaf/CategoryTheory/CofibrantSimplicialInversion.lean` states
`CategoryTheory.CofibrantSimplicialInversion.cofibrant_simplicial_inversion`.
It takes the recorded `CoherentNerveComparisonStatement` and asserts existence of
`Statement N`: functorial degreewise total and relative inversions, their ordinary
pushout square, the Bergner homotopy-pushout assertion, and the specified derived-nerve
weak equivalence with Kan target. Its only postponed proof is this named theorem,
whose docstring gives all eight proof steps with their DAG inputs. The node changes
only in `lean`; its mathematical statement and dependencies are unchanged.

The helper definitions belong to this node's inversion-square notion. They give real
degreewise categories and evaluated functors, and explicit predicates for the three
properties used in the statement. The `Statement` structure records a fully specified
existence assertion, not an unconstrained choice: every inversion is required to have
Mathlib's strict localization universal property in every degree, with object-preserving
unit. The file does not extract any definition from the postponed theorem. The elementary
category/functor law fields are evaluations of existing enrichment equations, not new
postponed lemmas.

Clause-by-clause correspondence:

- Small simplicial categories are the recorded `CoherentNerve.SCat.{u}`, with Mathlib's
  enriched functors and category instance. `u` is explicit and arbitrary. `N` is the
  dependency's full comparison datum, retaining its Bergner model and its particular
  functorial object-preserving replacement.
- The fixed small set O is represented by the common underlying object type of
  `i.left` and `i.right`. `FixesObjects i.hom` requires equality of these types and
  `HEq (i.hom.obj x) x` for every object x, rather than mere essential surjectivity
  or bijectivity. This expresses identity on objects independently of the two
  enrichments on that same set. It also permits the empty set.
- A pair A → B is `i : Arrow SCat`. Cofibrancy of A and B is
  `IsBergnerCofibrant N.bergner i.left` and the corresponding condition on `i.right`.
  The definition tests the initial map against the actual Bergner cofibration class.
  Quantifying over all initial objects is equivalent to the initial-map condition,
  and does not choose an additional model structure. Cofibrancy of i is the explicit
  `N.bergner.model.categoryWithCofibrations.cofibrations i.hom` hypothesis.
- The ordinary category A_n has type `Degree A n`, Hom `(hom A x y).obj n`, identity
  `(eId ... x).app n PUnit.unit`, and composition `(eComp ... x y z).app n (f,g)`.
  `degreeFunctor F n` evaluates the actual enriched map `F.map`, so the localization
  tests refer to the specified enrichment, not an unrelated category in each degree.
- G(A) is `completion.obj A`, its inversion map is `unit.app A`.
  `completion_objects` fixes the object set, and `completion_localization` says that
  its degree-n functor is strict ordinary localization at all arrows (`⊤`). This is
  degreewise groupoid completion, with the strict universal property determining all
  formal inverse extensions. Quantification over all `T : Type u` with `Category.{u} T`
  includes both the constructed small localization and the proposed target itself,
  which suffice to compare strict localizations by unique inverse functors. It does
  not mean localization only against groupoids or only locally Kan targets.
- B[A⁻¹] is `inversion.obj i`, with lower edge `from_target.app i` and right edge
  `from_source.app i`. `inversion_localization` uses precisely
  `(⊤ : MorphismProperty (Degree i.left n)).strictMap (degreeFunctor i.hom n)`.
  This marks the image of every degreewise A-arrow and imposes no saturation or
  two-out-of-three hypothesis. `inversion_objects` fixes B's objects.
- `ordinary_pushout` is Mathlib's `IsPushout (unit.app i.left) i.hom
  (from_source.app i) (from_target.app i)`, with exactly the displayed four arrows.
  This is the pushout in all small simplicial categories, not just among maps fixing O.
- `homotopy_pushout` states `IsBergnerHomotopyPushout` for those same four arrows.
  The predicate supplies a span D', an objectwise Bergner weak equivalence to
  `span (unit.app i.left) i.hom`, a colimiting cocone on D', a cofibrant central
  object and cofibrant outgoing legs. Its canonical comparison
  `hc'.desc ((Cocone.precompose r).obj (PushoutCocone.mk ...))` is a Bergner weak
  equivalence. By `N.bergner.weak_iff_dwyer_kan`, this is exactly the required DK
  equivalence from the pushout of a cofibrant span to the displayed apex. This is the
  same criterion used by the dependency's `homotopy_pushout_preservation` field.
- The first conjunct of `total_inversion_nerve` is the weak homotopy equivalence of
  `CoherentNerve.nerveFunctor.map (N.replacement.R.map (unit.app i.left))`.
  The dependency's `derived_nerve_objects` and `derived_nerve_maps` identify this
  literally with RN_hc(A) → RN_hc(G(A)); no merely existential comparison map occurs.
  The second conjunct says that its actual target
  `nerveFunctor.obj (N.replacement.R.obj (completion.obj i.left))` is Kan.
- Naturality is part of the data: `completion` and `inversion` are functors on SCat
  and its arrow category, and `unit`, `from_source`, `from_target` are natural
  transformations. A morphism in the arrow category is precisely a commuting map
  of pairs. Their naturality equations give every square in the induced map of
  pushout squares; applying the recorded replacement and nerve functors gives the
  naturality square of total-inversion nerve maps. Restricting to cofibrant pairs
  retains this naturality. Cofibrant replacement witnesses verify the homotopy
  property without changing any of these specified natural arrows.
- No hypotheses assert that the marked image in B is saturated or has two-out-of-three.
  The model weak-equivalence class itself still has its required model-category laws.

Dependency declarations used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerveComparisonStatement`, `BergnerModelData`,
  and its imported `CoherentNerve.SCat`, `hom`, `nerveFunctor`,
  `LocallyKanReplacement`, and `SSet.Enhanced.IsWeakHomotopyEquivalence`.
  Read the full recorded theorem `CategoryTheory.coherent_nerve_comparison`,
  every comparison field, and the infrastructure definitions and docstrings.
- Mathlib: `Localization.StrictUniversalPropertyFixedTarget`,
  `MorphismProperty.strictMap`, `Arrow`, `Arrow.leftFunc`, `Arrow.rightFunc`,
  `IsPushout`, `PushoutCocone.mk`, `span`, `Cocone.precompose`, and `IsColimit.desc`.
  Read the strict localization signature/docstring in Localization/Predicate.lean
  and the degree-evaluation equations in Enriched/Basic.lean.
- Proof-only imports from recorded proof inputs:
  `Sheaf.AlgebraicTopology.BisimplicialDiagonalEquivalence`
  (`SSet.bisimplicial_diagonal_equivalence`),
  `Sheaf.CategoryTheory.ReedyModelStructure`
  (`HomotopicalAlgebra.Reedy.model_structure`), and
  `Mathlib.AlgebraicTopology.ExtraDegeneracy`
  (`SimplicialObject.Augmented.ExtraDegeneracy.section_`,
  `section_comp_hom`, and `homotopy`). Their signatures and docstrings were read.
  The coherent-nerve input is already a public import. The free-calculus,
  free-category-groupoid-nerve and diagonal/coherent-nerve comparison proof nodes
  presently have no Lean records, so no modules are invented for them. They are
  proof dependencies, not prerequisites needed to type this statement.

Edge cases checked before writing:

- O empty: all object and hom quantifiers still make sense; no Nonempty O is assumed.
  The empty localization and empty nerve target satisfy the intended conditions.
- The identity pair A → A: its inversion square has both horizontal maps the total
  inversion, with the expected identity comparison after identifying pushouts.
- Identity-only A on O: degreewise total completion leaves A unchanged and the
  relative pushout leaves B unchanged; no requirement forces extra arrows to invert.
- A one-object free monoid: groupoid completion is the free group and changes strict
  arrows. The statement only claims a weak homotopy equivalence of derived nerves,
  not an enriched DK equivalence A → G(A).
- The marked image is the image of an actual degreewise functor and hence includes
  identities and composites, but the statement never asks whether this image is
  saturated or has two-out-of-three. These are not extra structure fields.
- Degree zero is included because n ranges over all `SimplexCategoryᵒᵖ`, including
  `[0]`. No local Kan hypothesis is added on A, B or their ordinary degreewise
  inversions: Kan replacement is applied exactly where required for the nerve.
- All small object sets and mapping sets in the fixed arbitrary universe u are included;
  no finite-object, nonempty, discrete, or common object/morphism universe restriction
  beyond the dependency's small SCat convention is introduced.

Searches for existing declarations:

1. `msearch.py Q98 lem-coef-cofibrant-simplicial-inversion leanfinder
   "A cofibration of cofibrant simplicial categories computes localization as homotopy
   pushout along degreewise groupoid completion"`: eight hits, concerning ordinary
   model-category cofibrant-object localizations; none states the enriched inversion
   pushout or its total-inversion derived-nerve assertion.
2. `msearch.py ... loogle '"SimplicialCategory", "Localization"'`: OK, zero hits.
3. `msearch.py ... grep
   'Bergner|groupoidCompletion|simplicialLocalization|homotopyPushout'`: OK, zero hits.
4. `rg` in the specified upstream WeilConjectures and shared lean/Sheaf trees for
   groupoidCompletion, totalInversion, simplicialLocalization, homotopyPushout and
   the item's id: only an existing proof docstring in HammockInfinityLocalization
   mentions this item; it does not supply the statement. The prescribed
   `grep -rn 'lem-coef-cofibrant-simplicial-inversion' .../WeilConjectures` has no hits.
5. `rg` in Mathlib, upstream WeilConjectures and shared lean/Sheaf for the chosen
   namespace and IsDegreewiseLocalization/IsBergnerHomotopyPushout: no clashes.
   Inspected Mathlib's ordinary `FreeGroupoid` construction and localization APIs;
   these concern ordinary categories, not the present enriched homotopy theorem.
6. A parsed DAG search for degreewise inversion/groupoid completion found this item
   itself and its existing proof inputs, not a separately recorded usable definition
   of its inversion square. The actual search-wrapper results are in searches.jsonl.

Source checked: opened the primary Dwyer--Kan I PDF at
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf
and read Sections 7--10, especially 8.1--8.2, 9.1--9.2 and 10.1. The node's
unsaturated fixed-object formulation agrees with these definitions and hypotheses.
No source correction or STATEMENT-DISPUTED flag is needed.

Validation: the final module passed `scompile.py Q98
lem-coef-cofibrant-simplicial-inversion <module>` cleanly, with no diagnostics.
The initial degreeCategory elaboration failed because Lean tried to infer enrichment
on the degree-tagged alias; specifying `(C := A)` in the existing enrichment equations
fixed it without changing the statement or adding a hypothesis.

## Second reading by Q98

I independently opened the node, its Dwyer--Kan source place (Sections 7.2--10.3),
the dependency declaration `CategoryTheory.coherent_nerve_comparison`, and the complete
module. The node introduces: (1) small simplicial categories and the recorded Bergner
model, replacement, and derived coherent nerve; (2) a fixed small object set `O`; (3)
an arrow `i : A ⟶ B` that is a Bergner cofibration between cofibrant objects and is the
identity on `O`; (4) total degreewise groupoid completion `G(A)`; (5) relative degreewise
inversion `B[A⁻¹]`; (6) the displayed ordinary pushout square; (7) its Bergner homotopy
pushout/Dwyer--Kan comparison; (8) the total-inversion derived-nerve weak equivalence
with Kan target; (9) naturality for maps of cofibrant pairs; and (10) absence of a
saturation or two-out-of-three hypothesis.

The Lean rendering and verdict for each item is:

* Small simplicial categories and the fixed universe are `SCat.{u}` and
  `CoherentNerveComparisonStatement.{u}` in the theorem parameter. **Matches.**
* The common object set and identity-on-objects condition are `FixesObjects`, namely
  equality of the two object types together with `HEq (F.obj x) x` for every object.
  This allows the empty set and imposes no extra finiteness assumption. **Matches.**
* An arrow is `i : Arrow SCat.{u}`. Its endpoint cofibrancy is
  `IsBergnerCofibrant N.bergner`, and its cofibration hypothesis is the actual
  `N.bergner.model.categoryWithCofibrations.cofibrations i.hom`. **Matches.**
* Degreewise ordinary categories are `Degree A n` with hom, identity, and composition
  evaluated from the given enrichment; `degreeFunctor` evaluates the specified enriched
  map. **Matches.**
* Total completion is the functor `completion`, with `unit`, fixed objects, and strict
  localization at `(⊤ : MorphismProperty (Degree A n))` in every degree. **Matches.**
* Relative inversion is `inversion`, with `from_source` and `from_target`; its target
  fixes objects and is a strict localization at the strict image of all arrows from `A`
  in each degree. **Matches.**
* The ordinary square is exactly Mathlib `IsPushout` on the four displayed arrows.
  **Matches.**
* The homotopy assertion is `IsBergnerHomotopyPushout`: a span replacement with
  cofibrant centre and cofibrant legs, objectwise Bergner weak equivalence, a colimiting
  cocone, and weak-equivalence comparison to the displayed pushout. This is the stated
  cofibrant-span/Dwyer--Kan formulation. **Matches.**
* The derived nerve clause uses the actual map
  `nerveFunctor.map (N.replacement.R.map (unit.app i.left))` and requires its weak
  homotopy equivalence plus Kan target. **Matches.**
* Naturality is represented by the functors `completion` and `inversion` and natural
  transformations `unit`, `from_source`, and `from_target`; all asserted maps are their
  specified composites. **Matches.**
* There is no field requiring saturation or two-out-of-three for the marked image.
  **Matches.**

I checked edge cases: the object type may be empty; identity arrows and identity pairs
  are admitted; degree zero is included because `n` ranges over all
  `SimplexCategoryᵒᵖ`; the localization property has no nonemptiness or characteristic
  assumption; and all categories remain in the single arbitrary universe `u` used by
  `SCat`. No hypothesis is stronger than the node's fixed-object/cofibrant hypotheses.

Independent searches used a new LeanFinder query, "Functorial inversion of enriched
category arrows computes a derived pushout and groupoid completion preserves
classifying space of a cofibrant simplicial category" (eight hits, none the theorem),
Loogle `"FreeGroupoid"` (ordinary quiver free-groupoid results), and grep for
`groupoid|inversion|simplicial` in `CategoryTheory/Localization` (five ordinary
groupoid-localization hits). Direct `rg` searches for `groupoid.?completion`,
`degreewise.?inversion`, `classifying.?space`, and `homotopy.?pushout` in Mathlib,
upstream `WeilConjectures`, shared `lean/Sheaf`, and the chapter's DAG found no exact
existing inversion-square statement. The `FreeGroupoid` primitive constructs the free
groupoid of a quiver, not completion of a category respecting its existing compositions.

One H4 repair was found: `IsBergnerCofibrant` independently restated Mathlib's initial-map
test. It is now a `noncomputable abbrev` reusing `HomotopicalAlgebra.IsCofibrant`, with
the supplied `M.model` bound in the expression. The explicit import is
`Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant`. Mathlib's
`isCofibrant_iff_of_isInitial` identifies this with the former all-initial-objects test;
the Bergner model has finite colimits and cofibrations respecting isomorphisms, so no
additional hypothesis or excluded case is introduced. No mathematical mismatch, new
definition node, or dependency repair was required. The node copy changes only its
`lean` record, whose statement is verbatim the unchanged theorem signature.

Validation after the repair: `scompile.py Q98
lem-coef-cofibrant-simplicial-inversion
lean/Sheaf/CategoryTheory/CofibrantSimplicialInversion.lean` compiled both the sandbox
and library forms cleanly. The prescribed `deliver2.py --no-push` printed
`OK (dry run)` and passed the server preflight. The source has no line over 100
characters; all binders and universes are explicit; its only postponed proof is the
named theorem with the eight-step node proof in its docstring.
