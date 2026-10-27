## Worker report

The delivery states all clauses of `lem-per-filtered-category-pseudococones`, without changing
its mathematical statement or its proof plan. Its module is
`Sheaf.CategoryTheory.FilteredColimitPseudococones`; the four declarations are:

- `CategoryTheory.filteredColimit_restriction_isEquivalence`;
- `CategoryTheory.pseudococone_restriction_naturality`;
- `CategoryTheory.filteredColimit_final_reindexing`;
- `CategoryTheory.filteredColimit_objectwise_equivalences`.

The missing general-category pseudococone notion and its canonical functor operations are
introduced by the new definition node `def-per-strict-diagram-pseudococones`, module
`Sheaf.CategoryTheory.StrictDiagramPseudococone`. All twenty declarations are listed in its
Lean record. There are no dependency repairs, no statement correction, and no disputed
statement. Every theorem has the entire proof `by sorry` and a source and natural-language
proof in its docstring. Definition data and functor actions are explicit, without `sorry`.

### Hypotheses and object presentation

- The small filtered category is `{J : Type z} [SmallCategory J] [IsFiltered J]`.
  No preorder assumption is imposed: multiple and parallel index morphisms are allowed.
- The strict diagram with small values is `D : J ⥤ Cat.{z, z}`. Strict identities and
  composition are the actual `D.map_id` and `D.map_comp` equalities, not additional
  pseudofunctor data. The common universe `z` contains the small index and stage sets.
- The set-presented category `C` and its strict structure functors are the bundled cocone
  `c : Cocone D`, with carrier `c.pt` and functors `(c.ι.app j).toFunctor`.
  `hobjects : IsColimit (Cat.objects.mapCocone c)` and
  `harrows : IsColimit (Cat.arrows.mapCocone c)` say precisely that its objects and complete
  arrows, including endpoints, are the two specified set colimits. The cocone already has
  functorial operations, and `c.w a` is the strict structure-functor equation. These are the
  presentation clauses of `exists_filteredColimit_category`, read in full in
  `WeilConjectures/CategoryTheory/FilteredColimitCategories.lean`. Its other finite-stage
  conclusions are consequences available for the proof, not extra hypotheses here.
  Using `IsColimit` admits the category constructed there and every choice of the specified
  set colimits; it does not replace it by an ordinary abstract Cat colimit lacking the set
  presentation. No arbitrary comparison map is an input.
- The vertex is `(A : Type u) [Category.{v} A]`, with both universes explicit and independent
  of `z`. Naturality also allows `(B : Type u') [Category.{v'} B]`. A common containing
  universe can always be taken; there is no local-smallness restriction beyond being a
  Lean category, and no equality imposed between these universe levels.

### Pseudococone objects, arrows, and restriction

- `StrictDiagramPseudococone.functor j : D.obj j ⥤ A` is the node's `A_j`.
- `comparison a : (D.map a).toFunctor ⋙ functor k ≅ functor j` is exactly
  `theta_a : A_k D(a) ≅ A_j`, with the direction retained.
- `identity` writes `theta_1 = 1`, transporting the source along `D.map_id` with `eqToHom`.
- `composition` writes `theta_(ba) = theta_a (theta_b D(a))`. In Lean's diagrammatic order
  the expression is the map of the strict composition equality, followed by
  `(comparison b).hom.app (D(a)x)`, then `(comparison a).hom.app x`. No extra associator
  choice or index coherence is assumed.
- `Hom.app j : P.functor j ⟶ Q.functor j` is `rho_j`. `Hom.compatibility` is
  `theta_a.hom.app x ≫ rho_j.app x = rho_k.app (D(a)x) ≫ eta_a.hom.app x`, precisely
  `rho_j theta_a = eta_a (rho_k D(a))` in the node's usual composition convention.
  The category instance uses exactly componentwise identities and vertical composition.
- `restriction c A` sends `F` to the actual functors `v_j ⋙ F`, and a transformation to
  its left whiskerings by `v_j`. The comparisons are
  `Functor.isoWhiskerRight (eqToIso (congrArg Cat.Hom.toFunctor (c.w a))) F`.
  These are the identity comparison isomorphisms for a strict cocone; equality-to-iso is
  necessary because the equal functors need not be definitionally equal in Lean.
- The first main theorem says this specified functor `.IsEquivalence`. This is the usual
  fully faithful, essentially surjective equivalence predicate, and `Functor.asEquivalence`
  supplies an equivalence with exactly this functor, so the node's functor is retained.

### Naturality in the vertex

`postcompose H` maps the functors, comparisons, and modification components by `H`.
`postcomposeMap t` has component `t.app (P.functor j |>.obj x)` and is a genuine natural
transformation between the postcomposition functors. The first conjunct of
`pseudococone_restriction_naturality` is equality of restriction followed by postcomposition
and postcomposition followed by restriction. The second conjunct is equality of the two
whiskered transformations for every `t : H ⟶ H'`, expressed as `HEq` because their source
and target functors are propositionally equal by the first conjunct. Thus naturality
includes 2-cells and the canonical comparison maps, not just objectwise equivalences.
This formal identity is stated for all strict cocones, which includes the filtered
set-colimit setup of the node; it adds no hypothesis to the restriction theorem.

### Final reindexing

- `K : Type z`, `[SmallCategory K]`, `[IsFiltered K]`, and `w : K ⥤ J` give the stated
  filtered reindexing. `[w.Final]` means every `StructuredArrow j w` is connected; Mathlib's
  `IsConnected` includes nonemptiness, so this is exactly the node's comma condition.
- `cK : Cocone (w ⋙ D)` with its two `IsColimit` witnesses gives the same object-and-arrow
  presentation for the reindexed diagram.
- The conclusion supplies `q : cK.pt ⥤ c.pt` with `q.IsEquivalence`. Its equations
  `(cK.ι.app k).toFunctor ⋙ q = (c.ι.app (w.obj k)).toFunctor` specify the canonical map
  on every stage object and arrow. Joint surjectivity of the two set-colimit cocones
  determines this functor uniquely: it is not an arbitrary map or an extra hypothesis.
- The last conjunct is equality of functors from `Fun(c.pt,A)` to `PCone(w ⋙ D,A)`:
  precompose with `q`, then restrict, equals restrict, then `reindex w`.
  This includes their action on modifications and comparisons. The vertex naturality
  theorem supplies compatibility with further postcomposition and its transformations.

### Objectwise diagram equivalences

- `E : J ⥤ Cat.{z,z}` and `cE`, `hEobjects`, `hEarrows` give the second strict diagram
  and its set-presented colimit.
- `e : ∀ j, D.obj j ≌ E.obj j` is the objectwise equivalence, including inverse data.
- `s a : (e j).functor ⋙ (E.map a).toFunctor ≅
  (D.map a).toFunctor ⋙ (e k).functor` is the node's invertible comparison
  `E(a)e_j ≅ e_kD(a)`. `hidentity` is its identity coherence, with both strict diagram
  identity transports; `hcomposition` is the composition square, with both strict
  composition transports. All comparisons are specified, not replaced by strict naturality.
- The conclusion gives `Q : c.pt ≌ cE.pt` and
  `t j : v_j ⋙ Q.functor ≅ (e j).functor ⋙ u_j`.
  The final equality compares the two maps from `Q(v_k D(a)x)` to `u_j(e_j x)`:
  first use the source cocone equation and `t_j`, or use `t_k`, then `u_k(s_a.inv)`, then
  the target cocone equation. This is exactly coherent compatibility with the supplied
  comparisons, including their inverses and their direction.

### Dependency declarations and sources read

- `def-nagata-category`: `CategoryTheory.Category`,
  `Mathlib.CategoryTheory.Category.Basic`, including `CategoryStruct`, identities and
  composition, and the laws at the full `Category` signature.
- `def-weil-size-convention`: a metatheoretic convention with no declaration; rendered
  by explicit universe levels. No data or hypothesis is invented for it.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, and its recorded `Cocone`, `IsColimit`, `colimit.desc`,
  `CategoryTheory.IsFiltered`. Full definitions of `Cocone`, `IsColimit`, `colimit`, and
  `IsFiltered` were read; the new definition module imports the recorded module.
- `lem-weil-pbc-filtered-colimit-categories`:
  `WeilConjectures.CategoryTheory.FilteredColimitCategories`,
  `CategoryTheory.exists_filteredColimit_category`. Its docstring and full signature,
  including set colimits, strict legs, finite lifting, eventual equality, Hom colimits,
  and invertible representatives, were read. The main module publicly imports it.
- Supporting set projections are the actual `CategoryTheory.Cat.objects` in
  `Mathlib.CategoryTheory.Category.Cat` and `CategoryTheory.Cat.arrows` in
  `WeilConjectures.CategoryTheory.ArrowsFunctor`, both read at their definitions.
- Proof dependencies already stated are imported by their owning modules:
  `Mathlib.CategoryTheory.Equivalence` (`Functor.asEquivalence`) and
  `Mathlib.CategoryTheory.Limits.Final` (the initial-functor/limit interface, also public
  because its `Functor.Final` occurs in the reindexing statement).
  `lem-per-filtered-pseudocone-representative-transport` has no recorded declaration yet;
  it remains a proof dependency and is named in the main proof docstring. It is not a
  prerequisite for stating these results and no invented import was added.
- Source text: `literature/stacks-project/categories.tex`, `section-directed-colimits`
  (04AX), `lemma-cofinal` (04E7), and `lemma-fibred-strict` (004A). The new statements
  correctly identify the pseudococone argument as an extension, not a verbatim Stacks
  theorem. The current `literature/blueprint/latest/` ancestor proof
  `lem-per-artin-gabber-affine-curve.proof.md` was also read, especially Step 3 and the
  completion-continuity ancestry already recorded in the item.

### Edge cases and mathematical checks

The empty index category is excluded exactly by `[IsFiltered J]`, as in the node. Empty
stage categories are allowed, including an entirely empty diagram of values and empty
colimit category; in that case both functor and pseudococone categories have the expected
single empty family. An empty vertex is allowed: a nonempty colimit admits neither a
functor into it nor a pseudococone into it. For a one-object identity index the unit
coherence forces the identity comparison, so PCone reduces to the functor category.
Parallel index arrows are not identified a priori: the supplied coherence and filteredness
are what the eventual-representative proof uses. Nonfaithful and noninjective transition
functors are allowed; only the set-colimit hypotheses occur. Reindexing by the identity
is included, as are final functors with multiple lifts. The objectwise comparison need
not be strict: the final equation retains the supplied nontrivial `s`. No comparison is
chosen from an uncharacterized existence result, and no definition chooses object data
from a sorried theorem.

### Searches

Prescribed `msearch.py` searches, logged in `searches.jsonl`, were run:

- LeanFinder: “Restriction functors from a filtered colimit of categories form an equivalence
  with coherent pseudococones”: eight hits on filtered set relations and ordinary cocone
  equivalences; none states this theorem.
- Loogle: `CategoryTheory.Pseudocone, CategoryTheory.Cat, CategoryTheory.Functor.Final`:
  no hits; `CategoryTheory.Pseudocone` was reported unknown, so this query alone was not
  treated as evidence of absence.
- Mathlib grep: `Pseudo[Cc]ocone|pseudococone|pseudocolimit` in CategoryTheory: no hits.
- LeanSearch: “Category of coherent pseudococones of functors on a strict diagram of small
  categories with modifications and postcomposition”: eight ordinary cocone/diagram hits.
- LeanFinder: “Pseudococones on a strict diagram of categories and compatible natural
  transformations”: eight ordinary cocone/diagram hits.
- Mathlib grep: `Pseudococone|pseudoCocone|pseudococone` in CategoryTheory: no hits.

The same exact-name grep was run on `lean/WeilConjectures` and `lean/Sheaf`: no hits.
Broader searches for coherent cocones and two-colimits found the directed-poset
`CoherentCategoryCocone`/`FilteredTwoColimit` files and additive common-stage pair descent;
their full interfaces assume a preorder/directed order or additive data and do not give
PCone for a general filtered category. No private replacement of their notions was made.
Searching the new declaration names in `dag/lean_names_upstream.json`, upstream sources,
and `lean/Sheaf` found none. Searching the item id in upstream sources also found none.
`tools/blueprint_refs.py search pseudococone` found zero blueprint nodes; a DAG grep found
only this item, its transport proof dependency, and its topos consumer. None is a definition
node for the general PCone category. The ancestor command returned
`lem-per-artin-gabber-affine-curve`.

### Validation

Both modules were compiled separately in dependency order through the prescribed
`scompile.py`. Final output contained no error and no warning. Compilation was repeated
when imports were reduced to their owning dependencies. The main source has no diagnostic
commands, local notation, private helpers, or auto-bound variables. The new-node definition
uses ten named elementary law theorems (all listed in its record); they match the coherence,
modification and extensionality laws in its statement and carry complete proof docstrings.
The prescribed `deliver2.py --no-push` returned `OK (dry run)`: commit
`498ad06b877` passed the maintainer preflight and per-file compiles. Final delivery uses
the same prescribed wrapper.

## New nodes

`def-per-strict-diagram-pseudococones` defines exactly the missing PCone category for strict
small-category diagrams: functors, normalized coherent invertible comparisons, modifications,
componentwise category operations, and the canonical restriction, postcomposition (including
transformations), and reindexing operations used by the item. Its statement also names the
elementary compatibility and coherence obligations, whose named postponed proofs appear in
its owning module. It has no filteredness assumption because the definition itself needs
none. Its source is the explicit coherent-family construction in the item's finite-
representative extension of Stacks 04AX and the reindexing in 04E7; 004A is not used as a
substitute for that universal property. LeanSearch, LeanFinder, Mathlib grep, upstream and
project grep, DAG grep and the full blueprint search found no existing exact definition;
ordinary cocones and directed-poset two-colimit models do not supply this notion. All
search records are actual tool results. This node is cited by the item's added stmt_dep.

## Second reading by Q74

Independent reading by the maintainer's second reader (NT-cc review service), which replaces the
worker's self-check. It was done with the node, `def-per-strict-diagram-pseudococones`, both Lean
files, the signature of `CategoryTheory.exists_filteredColimit_category` and `Cat.arrows`, and
Stacks categories.tex 04AX/04E7/004A open.

Node clauses and their Lean:

1. J is small and filtered: `{J : Type z} [SmallCategory J] [IsFiltered J]`. Correct; parallel arrows
   are allowed and there is no preorder assumption.
2. D : J → Cat is strict with small values: `D : J ⥤ Cat.{z, z}`. Correct (size convention, common
   universe z).
3. C is the object/arrow set colimit with its structure functors v_j: `c : Cocone D` with
   `IsColimit (Cat.objects.mapCocone c)` and `IsColimit (Cat.arrows.mapCocone c)`. Correct. The category
   built by `exists_filteredColimit_category` has `Category.{z}` on a `Type z` colimit, so it is a
   `Cat.{z,z}` cocone and meets both hypotheses. Through these hypotheses C is determined up to
   isomorphism compatible with the v_j. `Cat.arrows` (ArrowsFunctor) records endpoints, so the
   arrow colimit matches the node's "arrows" set.
4. A in the containing universe: `(A : Type u) [Category.{v} A]`, which is more general. Correct.
5. PCone objects (A_j, θ_a : A_k D(a) ≅ A_j), θ_1 = 1, θ_{ba} = θ_a ∘ (θ_b D(a)): `functor`,
   `comparison a : D(a) ⋙ functor k ≅ functor j`, `identity`, `composition`. I checked the
   composite: eqToHom(D(a≫b)x = D(b)D(a)x) ≫ θ_b at D(a)x ≫ θ_a at x, which is exactly the node's
   formula. Correct.
6. PCone arrows ρ_j with ρ_j θ_a = η_a (ρ_k D(a)): `Hom.compatibility` (θ_a ≫ ρ_j = ρ_k D(a) ≫ η_a).
   Correct, with componentwise identities and composition.
7. Restriction with identity comparisons is an equivalence: `restriction c A`, with
   comparisons `isoWhiskerRight (eqToIso (c.w a)) F` and maps given by whiskerLeft;
   `filteredColimit_restriction_isEquivalence` gives `.IsEquivalence` for this functor. Correct.
8. Naturality in A: `pseudococone_restriction_naturality` gives functor equality with postcompose H,
   and HEq of the two whiskered transformations for t : H ⟶ H'. Both conjuncts hold
   componentwise (t at F(v_j x)). The HEq is the honest form, since the source and target functors
   are equal only propositionally. Correct.
9. Final reindexing: `[IsFiltered K]`, `w : K ⥤ J`, `[w.Final]`. Mathlib's Final means
   `IsConnected (StructuredArrow j w)` for every j; this is (j ↓ w), and connectedness includes
   nonemptiness, which is the node's condition. The conclusion gives q, `q.IsEquivalence`, the leg
   equations v^K_k ⋙ q = v_{wk}, and the restriction compatibility
   `whiskeringLeft q ⋙ restriction cK = restriction c ⋙ reindex w`. The leg equations pin q,
   because the cK legs jointly cover objects and arrows. Correct.
10. Objectwise equivalences: `e j : D(j) ≌ E(j)` and `s a : e_j ⋙ E(a) ≅ D(a) ⋙ e_k` (σ_a). I
    checked `hidentity` (σ_1 is the strict identity transport) and `hcomposition`, the pasting
    σ_{ab} = σ_b D(a) ∘ E(b)σ_a up to the strict D/E composition equalities. Both are exactly the
    coherence of the node's step 6. The conclusion gives an equivalence Q : C ≌ C_E and
    t_j : v_j ⋙ Q ≅ e_j ⋙ u_j. The displayed equation is the λ-coherence
    Q(v_k D(a)x = v_j x) ; t_j = t_k ; u_k(σ_a⁻¹) ; (u_k E(a) = u_j), with correct directions.
    Correct.

New node `def-per-strict-diagram-pseudococones`: all data are explicit (structure fields,
`restrictObj`, `postcomposeObj`, `postcomposeMap`, `reindexObj`, and the functor actions). Only Prop
laws are `sorry`, each with a proof docstring; none is hollow. The notion is absent from Mathlib
(grep for Pseudococone/PseudoCocone in CategoryTheory), from the live side clone's lean/ tree and
from slopmaster2. The directed-poset coherent-cocone files in the project do not cover general
filtered J. Its statement matches its record, and its lean.statement occurs verbatim in the file.

Edge cases: an empty J is excluded by IsFiltered, as in the node. Empty stage categories and an
empty vertex are covered. A one-object J with only the identity forces θ_1 to be the identity.
Non-faithful transition functors are allowed. w = 𝟭 is included.

Records: the item's lean.statement occurs verbatim in FilteredColimitPseudococones.lean. The added
stmt_dep is the new definition node of this delivery. No theorem node is cited for a definition,
and no universe is restricted beyond the node's single size universe z for J and D.

Mismatches found: none in the mathematics. The only change is this section, which replaces the
worker's self-audit (delivery-errors H11).
