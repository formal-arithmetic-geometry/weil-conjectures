## Worker report

Stage 2 statement of `lem-coef-presentable-small-object-factorization` in
`lean/Sheaf/CategoryTheory/PresentableSmallObjectFactorization.lean`.
The sole new declaration is
`CategoryTheory.MorphismProperty.hasFunctorialFactorization_of_isLocallyPresentable`.
Its proof is `sorry`; no theorem is proved and no definition is introduced.
The node copy differs from the shared node only in `lean`. The statement, dependencies,
proof plan, status, source and maintainer review are preserved.

The previous attempt apparently confused the already reviewed stage-1 split with a
stage-2 attachment and delivered an unchanged node. There was no Lean attachment or
module in the current node or sandbox. This delivery supplies the actual statement
and its binding, so the item is no longer unchanged.

Hypothesis and clause correspondence:

- A category with Hom sets in the fixed universe U is `{C : Type u} [Category.{v} C]`,
  with U represented by `v`. The object universe `u` remains independent; there is
  no smallness assumption on the collection of objects and no equality of object
  and Hom universes. Both universes and all variables are explicitly bound.
- All U-small colimits are `[Limits.HasColimitsOfSize.{v, v} C]`, using the colimit
  interface of `def-weil-pbc-category-colimit`. This includes the small coproducts,
  pushouts and small ordinal chains used by the proof.
- Local presentability is `[IsLocallyPresentable.{v} C]`. Its `exists_cardinal`
  supplies `κ : Cardinal.{v}`, `Fact κ.IsRegular`, and
  `IsCardinalLocallyPresentable C κ`. The latter extends
  `HasCardinalFilteredGenerator C κ` and `HasColimitsOfSize.{v, v} C`.
  The explicit colimit binder repeats the node's stated hypothesis; it adds no
  extra condition beyond local presentability.
- An infinite regular κ is Mathlib's `Cardinal.IsRegular`: it includes
  `aleph0_le` and equality with cofinality, equivalent to the regular-union
  formulation used in the node. No finite rank is allowed accidentally.
- The small family of κ-presentable generators is
  `HasCardinalFilteredGenerator.exists_generator`, whose essentially-small
  object property consists of κ-presentable objects and expresses every object
  as a κ-filtered colimit. The equivalent strictly small family is supplied by
  `HasCardinalFilteredGenerator.exists_small_generator`. Thus the use of an
  essentially-small property does not replace the node's small set by a class.
- Hom preservation is `IsCardinalPresentable`, defined from κ-accessibility of
  `coyoneda.obj (Opposite.op A)`. `IsCardinalFiltered` says that every functor from
  a category with `HasCardinalLT (Arrow A) κ` has a cocone: exactly the node's
  fewer-than-κ-morphisms criterion. These definitions use the same `v` as κ.
- The U-small set of morphisms is `(I : MorphismProperty C) [IsSmall.{v} I]`.
  `MorphismProperty.IsSmall` means `Small.{v} I.toSet`, where `I.toSet` is the
  subtype of arrows satisfying I. This is precisely a set of arrows, not an
  additional closure, finite-generation or small-domain hypothesis.
- The right lifting class R is `I.rlp`: for every generating arrow, it has
  `HasLiftingProperty` with that arrow on the left. This class quantifies over
  every commutative square and asserts existence of a diagonal filler, without
  requiring uniqueness or chosen fillers.
- The left lifting class L is `I.rlp.llp`, so no alternative cell-complex class
  or merely smaller left class replaces the node's L.
- Existence of one simultaneous functorial factorization is the conclusion
  `HasFunctorialFactorization I.rlp.llp I.rlp`. Its field is
  `Nonempty (FunctorialFactorizationData I.rlp.llp I.rlp)`, not a collection of
  independent pointwise choices. This is a proposition stating existence of
  the factorization data, not a definition choosing unspecified data.
- For each arrow f, those data have middle object `data.Z.obj f`, first map
  `data.i.app f`, second map `data.p.app f`, and
  `data.fac : data.i ≫ data.p = Arrow.leftToRight`. Componentwise this says
  `data.i.app f ≫ data.p.app f = f.hom`, the node's p_f i_f = f.
- `data.hi f` asserts `I.rlp.llp (data.i.app f)` and `data.hp f` asserts
  `I.rlp (data.p.app f)`, covering both membership clauses.
- Every commutative square φ : f → g is a morphism in `Arrow C`.
  The induced middle map is `data.Z.map φ`. Naturality of i gives
  `data.i.app f ≫ data.Z.map φ = φ.left ≫ data.i.app g`; naturality of p gives
  `data.Z.map φ ≫ data.p.app g = data.p.app f ≫ φ.right`. In ordinary function
  composition notation these are exactly both equations in the node.
- `data.Z.map_id` and `data.Z.map_comp` supply preservation of identities and
  composition for these same middle maps. Hence every functoriality clause is
  included in the conclusion.

Dependency declarations and sources read:

- `def-weil-pbc-category-colimit` is a Mathlib leaf. Read its complete node and
  recorded match: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit` (the dual of `limit` at lines 180-182), its
  cocone/coproj/desc interface, and `HasColimitsOfSize`. This module is publicly
  imported. There is no unusable statement dependency and no private copy.
- Proof leaf `lem-coef-object-presentability-rank` matches
  `CategoryTheory.instIsPresentableOfIsAccessibleCategory` in
  `Mathlib.CategoryTheory.Presentable.LocallyPresentable`, lines 93-103.
  This module is already a public statement import.
- Proof leaf `lem-coef-small-family-regular-bound` matches
  `HasCardinalLT.exists_regular_cardinal` in
  `Mathlib.SetTheory.Cardinal.HasCardinalLT`, lines 199-214; imported without
  `public` for the proof plan.
- Proof leaf `lem-coef-cardinal-small-object-factorization` matches
  `CategoryTheory.SmallObject.hasFunctorialFactorization` in
  `Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument`,
  lines 470-473. Read the full assumptions/class fields at lines 69-86 and
  the constructed functorial data at lines 460-468. Imported without `public`.
- Read the complete signatures/docstrings of `IsLocallyPresentable`,
  `IsCardinalLocallyPresentable`, `HasCardinalFilteredGenerator`, its small
  generator interface, `IsCardinalPresentable`, `IsCardinalFiltered`,
  `MorphismProperty.IsSmall`, `rlp`, `llp`, `HasLiftingProperty`,
  `FunctorialFactorizationData` and `HasFunctorialFactorization` in Mathlib.
  The theorem docstring reproduces all five DAG proof steps, including the
  fibre injection, empty ordinal-diagram case and both naturality equations.
- Read the blueprint `prop-coef-integral-exceptional-adjoint`, especially its
  second proof paragraph. It motivates the infrastructure but does not prove
  this generic theorem. The node correctly calls its reduction an agent proof;
  the unarchived Hovey and Adamek-Rosicky books are not presented as read sources.

Edge cases checked before writing:

- Empty I is allowed: `IsSmall` has no nonemptiness assumption; R is all maps,
  L is the isomorphisms, and the identity-then-f factorization is functorial.
- No finite or small-object hypothesis is placed on generating domains or
  codomains. Infinite domains can have larger presentability ranks; the proof
  chooses objectwise ranks and only then their common regular bound.
- The empty ordinal diagram is covered by vertex zero. The common bound is
  infinite, so its ordinal is nonempty. Empty generator families do not break
  the disjoint-union bound step.
- The terminal category satisfies all hypotheses and conclusions. An empty
  category fails cocompleteness (no initial object), as it should.
- In Set, empty-to-singleton as the sole generator gives surjections in R;
  the conclusion does not accidentally require unique lifts.
- All size conditions use `v`; arbitrary object universe `u` is allowed.
  There are no ring, characteristic, scheme or cohomological-degree parameters.

Searches for an existing statement (run with the prescribed msearch wrapper;
full results/digests are in the sandbox searches.jsonl):

- LeanFinder: "In a locally presentable category every small set of morphisms
  admits a functorial factorization with left class the left lifting property
  against the right lifting class". Eight hits, including
  `MorphismProperty.instHasFunctorialFactorizationLlpRlp`,
  `SmallObject.hasFunctorialFactorization` and `SmallObject.functorialFactorizationData`.
  The first requires `HasSmallObjectArgument`, the others require its regular
  cardinal interface. None derives this from the node's hypotheses.
- Loogle: `"HasFunctorialFactorization"`. Nine hits, including the same
  conditional declarations and the data class; no exact locally presentable
  arbitrary-set theorem.
- LeanSearch: "Any small set of arrows in a locally presentable category
  generates a functorial weak factorization". Eight hits, again conditional
  small-object/model-category results, not the required implication.
- msearch grep: `HasSmallObjectArgument|hasFunctorialFactorization|IsLocallyPresentable`
  in `CategoryTheory/Presentable`. Fourteen hits: definitions and local
  presentability of types/presheaves, no arbitrary-set factorization theorem.
- Direct rg on upstream WeilConjectures for the same notions found the Serpe
  generating-set and mono-quasi-isomorphism factorizations and Gabriel-Popescu
  local presentability. These require specialized abelian/cochain data.
  Direct rg on `lean/Sheaf` found the consumer SmallCotorsionModelRecognition,
  which cites this item in its proof plan; it does not state this general theorem.
- Direct rg by the full item id in upstream WeilConjectures found no declaration.
  Direct rg for `hasFunctorialFactorization_of_isLocallyPresentable` and
  `SmallObjectFactorization` across Mathlib, upstream and side sources found
  no competing declaration. The upstream name inventory likewise has no
  attachment for this item/name.

No node fault, missing notion, statement dispute, correction, new node or
additional dependency module is needed. The declaration is a genuine new
statement using existing notions throughout.

Validation: `scompile.py NC lem-coef-presentable-small-object-factorization`
compiled both the sandbox check and the library module cleanly (1.1 seconds each).
The required `deliver2.py NC lem-coef-presentable-small-object-factorization --no-push`
printed OK: compilation and preflight passed except for the independent second
reading, which the second reader writes. Nothing was pushed. A final source
check confirms exactly one sorry, no lines over 100 characters, an exact signature
record, and only `lean` changed in the node. No independent second-reading section
is written by this worker.

## Second reading by NC

I read the complete node record and its source place, the dependency record for
`def-weil-pbc-category-colimit`, and the Mathlib declarations used by the Lean
module. The source place is the generic small-object input identified in the
blueprint proof paragraph before the displayed derived inverse-limit argument;
the node explicitly records the small-object argument as an agent reduction.

The node's statement, item by item, is rendered as follows, with every verdict
being an exact match:

- The category is `{C : Type u} [Category.{v} C]`; `v` is the fixed Hom-set
  universe and `u` is independent. The Lean binders are exactly these, with no
  object/Hom universe equality or smallness of the object collection.
- All `U`-small colimits are `[Limits.HasColimitsOfSize.{v, v} C]`. This is the
  recorded Mathlib colimit interface and adds no condition beyond the node's
  all-small-colimits hypothesis.
- Local presentability is `[IsLocallyPresentable.{v} C]`. Its cardinal witness
  is an infinite regular cardinal in universe `v`, with a small presentable
  generating family and preservation of filtered colimits, exactly as in the
  node. The explicit colimit instance is the node's separate colimit
  hypothesis, not an extra finiteness or Noetherian condition.
- `I` is `(I : MorphismProperty C) [IsSmall.{v} I]`, exactly a `U`-small set of
  morphisms; no nonemptiness, finite-generation, or domain/codomain condition
  is added.
- The right class is `I.rlp`, Mathlib's lifting property against every arrow in
  `I`, and the left class is `I.rlp.llp`, the lifting property against every
  arrow in that right class. These are the node's `R = I^square` and
  `L = ^square R`, with no uniqueness of fillers.
- The conclusion is `HasFunctorialFactorization I.rlp.llp I.rlp`. Its data are
  a functor `Z : Arrow C ⥤ C`, natural maps `i` and `p`, the equation
  `i ≫ p = Arrow.leftToRight`, and membership of each component in `L` and
  `R`. Thus every arrow has `f = p_f i_f` with both membership clauses.
- For every arrow morphism `(a,b) : f ⟶ g`, the naturality of `i` and `p`
  gives `m(a,b) i_f = i_g a` and `p_g m(a,b) = b p_f`; `Z.map_id` and
  `Z.map_comp` give identity and composition preservation. All functoriality
  clauses and quantifier order are therefore present.

Edge cases were checked against the node: `I` may be empty; the zero and
terminal-category cases are not excluded; empty ordinal diagrams are covered;
the common regular cardinal is infinite; and arbitrary object universe `u` is
allowed independently of Hom universe `v`. No characteristic, ring, scheme,
degree, or `n = 0` parameter occurs in this node. The empty category correctly
fails the colimit hypothesis.

I searched Mathlib and the project with the prescribed LeanFinder, Loogle,
LeanSearch, and `rg` queries for locally presentable small-object
factorizations, `HasFunctorialFactorization`, and the exact declaration name.
The hits are conditional small-object interfaces requiring a regular-cardinal
small-object hypothesis; none states this locally-presentable arbitrary-small-set
implication. No upstream WeilConjectures or existing `lean/Sheaf` declaration
matches, so the new declaration is required. The dependency declaration is the
recorded Mathlib `CategoryTheory.Limits.colimit`/`HasColimitsOfSize` interface
and is usable as written.

No mismatch was found, so no statement, dependency, or source binding was
changed. The module has one postponed theorem proof (`sorry`), no hollow
definition, explicit universes, and docstrings carrying the source and all five
proof steps. `scompile.py` compiled the module and its sandbox check cleanly;
the node's `lean.statement` remains verbatim equal to the theorem signature.
