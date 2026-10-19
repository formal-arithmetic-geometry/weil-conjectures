## Worker report

The packet states `CategoryTheory.simplicial_bifibrant_localization` in
`lean/Sheaf/CategoryTheory/SimplicialBifibrantLocalization.lean`.  It uses the
finite-string localization `MorphismProperty.Localization` already provided by
Mathlib, and defines the component category on `BifibrantObject C` with homs
`SSet.π₀ (sHom X.obj Y.obj)`.  The supporting declarations in the same module
are the enriched composition descent, the cotensor parameter map and endpoint
maps, and the bifibrant replacement object.  They are all canonical constructions;
only their theorem proofs are postponed with `sorry`.

The main theorem renders the node statement as follows.

* `C : Type u`, `Category.{v} C`, `ModelCategory C`, and
  `SimplicialCategory C` are the model category and compatible simplicial
  enrichment.  The two `HasFunctorialFactorization` instances are the chosen
  weak-factorization systems.  `T : SimplicialTensorCotensor C` supplies the
  chosen simplicial tensors and cotensors.
* `Q R : C ⥤ C`, `p : Q ⟶ 𝟭 C`, and `j : 𝟭 C ⟶ R` render the functorial
  replacements.  `hQ` and `hR` state that the sources of `Q` and targets of `R`
  are cofibrant and fibrant; `hp` and `hj` state that `p` and `j` are the
  corresponding trivial fibrations and trivial cofibrations.
* `hrecognition` says exactly that a map between `BifibrantObject C` objects is a
  weak equivalence iff its `π₀` vertex class has a two-sided inverse.  The two
  displayed equalities use `simplicialPiZeroComp` and the enriched identity
  vertices.
* `hendpoints` says that for every fibrant `Y`, both endpoint maps from the
  cotensor by the standard one-simplex are trivial fibrations.  The endpoint
  map is the canonical map induced by the two maps `Δ⁰ → Δ¹`, followed by
  evaluation at the unique vertex of `Δ⁰`.
* The conclusion supplies `G : BifibrantObject C ⥤
  (weakEquivalences C).Localization` and `F` in the opposite direction, with
  `G.IsEquivalence`.  The first map clause identifies `G` on every component
  class with `Q.map f`, up to the displayed object equalities, so it is exactly
  inclusion followed by the finite-string localization.
* The next clauses give `F(QX) = RQX`, `F(Qf) = [RQf]`, and the natural
  comparison `X ← QX → RQX` through `α : 𝟭 ⟶ F ⋙ G`, with every component of
  `α` invertible.  The `IsIso (Q.map a) ↔ WeakEquivalence a` clause is the
  requested saturation statement, and the final existential represents every
  localization arrow between bifibrant images by an actual arrow.

The dependency declarations used are:

* `simplicial_boundary_collapse_test` in
  `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest` (model-category
  weak-factorization and two-out-of-three transfer).
* `SimplicialTensorCotensor` in
  `Sheaf.CategoryTheory.SimplicialTensorCotensor`, together with its
  `tensorMap` and
  `SimplicialTensorCotensor.parameterMap` (the enriched tensor/cotensor
  representing data).
* `right_proper_kan_quillen` in
  `Sheaf.AlgebraicTopology.KanQuillenRightProper` (the Kan model structure and
  the simplicial-set endpoint facts, imported
  transitively by the boundary-collapse module).

I checked edge cases before writing the statement: `SSet.π₀` is a quotient of
vertices and therefore also handles an empty mapping simplicial set; no
nonemptiness or Kan assumption is silently added.  `Fin 2` includes both
endpoints, including the degenerate constant-path case.  Identity and
composition clauses are stated for arbitrary bifibrant objects, and all
universe parameters remain explicit so empty categories and arbitrary
large-enough universes are not excluded.

Searches made for an existing declaration or duplicate notion were:

* `msearch.py ... leanfinder "Bifibrant objects simplicial mapping space path
  components form a category equivalent to ordinary localization"` — eight
  Mathlib hits for ordinary `HoCat`/localization, but no enriched-component
  recognition theorem.
* `msearch.py ... grep "piZero|ConnectedComponents|HomotopyCategory"
  AlgebraicTopology/SimplicialCategory` — no hits.
* `msearch.py ... loogle "BifibrantObject, HoCat"` — Mathlib
  `BifibrantObject.HoCat` and related ordinary right-homotopy declarations
  only; no exact match.
* The node's recorded searches for `ModelCategory`/`Localization`,
  weak-equivalence detection, and simplicial localization likewise found only
  ordinary right-homotopy results, so no existing declaration was attached.
* `rg` over `WeilConjectures` and the shared `lean/Sheaf` tree found no
  declaration named `simplicial_bifibrant_localization` or an equivalent
  enriched-component theorem.

No new definition node or dependency repair was needed.  No
`STATEMENT-DISPUTED` flag applies.  The stale duplicate AlgebraicTopology
packet was removed; the delivered module is the single node module recorded in
the node's `lean` field.

## Second reading by Q51

Independent maintainer second reading of immutable delivery
`d5f4c6b628616bc0b98849bf40ef8f207124aa12`; the replacement module and record
contain the mechanical repairs below. The worker report above describes the
original delivery. In the replacement, the H-object type in its formulas is
`SimplicialBifibrantComponent C`, a public synonym for Mathlib's bifibrant objects.

Found and repaired: H9's prohibited file-local category instance is replaced by
that public type synonym and a named global category instance. H8's missing
source/blueprint helper docstrings are supplied. The lean record now lists all
public helpers, as required for the named postponed subclaims of Steps 1 and 3.
The original second-reading paragraph did not substantiate each clause (H11);
this replacement records the actual independent reading. No mathematical
statement or DAG edge changes, and no new node is needed.

### Hypotheses and conclusion

- `C : Type u`, `Category.{v} C`, `ModelCategory C` supply the underlying
  category and its model classes. The two functorial-factorization instances
  are explicitly required in the boundary-collapse dependency's *definition*
  of model category; they are not new assumptions inferred from convenience.
  Mathlib ModelCategory supplies finite limits/colimits, which already suffice
  for these clauses. No additional completeness, finiteness, properness,
  Noetherian, ring, or field assumption is introduced.
- `SimplicialCategory C` is exactly `EnrichedOrdinaryCategory SSet.{v} C`.
  `homEquiv'` identifies ordinary arrows with mapping vertices. The actual
  `SimplicialTensorCotensor` structure has universal tensor/cotensor elements
  and requires the *composition-induced* currying maps to be isomorphisms;
  it does not supply arbitrary unrelated hom-set bijections.
- `Q R`, natural transformations `p : Q ⟶ 𝟭 C`, `j : 𝟭 C ⟶ R`, and
  `hQ`, `hp`, `hR`, `hj` express exactly the two chosen replacements and their
  object and map properties. `(Q ⋙ R).obj X` is RQX, in the correct order.
- `hrecognition` uses arbitrary bifibrant endpoints and ordinary `f`. Its
  witness `g` is an ordinary reverse arrow, with BOTH composite vertex classes
  equal to the appropriate identities. This is equivalent to an inverse in H:
  every component has a vertex representative (`π₀.mk_surjective`).
- `hendpoints` ranges over every fibrant Y and both `Fin 2` vertices, with no
  cofibrancy hypothesis on Y. The map used is canonical: precompose the
  universal cotensor element with K→L, apply the inverse enriched representing
  isomorphism, and evaluate the zero-simplex cotensor at its unique vertex.
  I checked the composition order, braiding, currying, and Δ⁰→Δ¹ vertex maps.
- H uses exactly bifibrant objects and `SSet.π₀ (sHom X.obj Y.obj)` homs.
  Composition is the double quotient lift of enriched composition; identities
  and laws use named postponed Step-3 subclaims, not unknown data.
- `(weakEquivalences C).Localization` and `.Q` are Mathlib's *ordinary*
  finite-path/formal-inverse construction, with precisely identity,
  composition, and both inverse relations. This is not an infinity-localization
  or a substitute on a different site.
- G and its `IsEquivalence` are supplied. Its vertex-map equation and the
  object equalities identify it with inclusion followed by q. Object equality
  for every object follows already by taking f to be its identity; no object
  is lost when there are no maps between two distinct objects.
- F has the stated object formula and actual-arrow formula `[RQf]`, including
  explicit equality transports. The invertible natural transformation α is
  characterized by `q(p_X) ≫ α_X = q(j_QX)` after the displayed target transport,
  exactly the requested replacement zigzag. Since G is an equivalence and
  F⋙G is naturally isomorphic to the identity, F is a quasi-inverse; omission
  of a second explicitly chosen natural transformation does not weaken this.
- The `Arrow C` iff is saturation for EVERY actual arrow, not only bifibrant
  arrows. The final existential is actual-arrow representation for every
  localization morphism between the images of any bifibrant X,Y.

## Source and dependency checks

The source read was Q51's
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
Paragraph 2 and its displayed derived-adjunction calculation. It motivates
this prerequisite; it does not itself state a localization theorem. The node
correctly labels its nine-step proof agent-written and its result ordinary.
I checked all nine steps: closure gives RQX bifibrant and QX bifibrant for
fibrant X; naturality plus two-out-of-three gives weak-equivalence reflection;
edge compatibility defines H; a constant cotensor path makes localized
endpoints equal; replacement extends across the finite-word relations;
α and β are natural, with Gβ=α; conjugation proves full faithfulness; applying
F gives saturation; vertex surjectivity gives actual-arrow representation.
None requires enriched functoriality of Q or R or Kan mapping spaces.

Dependency interfaces opened and checked:

- `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`, exact
  `CategoryTheory.simplicial_boundary_collapse_test`: the item uses the
  model/WFS/object definitions in its preamble and Mathlib model interfaces,
  not the special V-transfer conclusion with its extra colimit assumptions.
- `Sheaf.CategoryTheory.SimplicialTensorCotensor`, exact structure and
  `tensorMap`/`parameterMap`: real universal-element data, with no supplied
  cotensor parameter map. The new cotensor helper is its canonical dual,
  properly owned by this item's endpoint construction.
  I also opened Riehl's Categorical Homotopy Theory, Definitions 3.7.2–3.7.3
  and Remark 3.7.4, printed p.38/PDF p.53, for the enriched adjunction meaning:
  https://emilyriehl.github.io/files/cathtpy.pdf .
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`, exact
  `SSet.KanQuillen.right_proper_kan_quillen`, its weak-equivalence structure
  and replacement map: the fixed model-structure fields and realization weak
  equivalences were read. This dependency is imported transitively. The item
  does not use its coherent-localization clause or assume that its arbitrary
  C equals SSet.

I opened Mathlib `SimplicialCategory/Basic.lean` (`homEquiv'`, `sHom`),
`SimplicialSet/PiZero.lean` (π₀, mk, mk_eq_mk_iff, mk_surjective, lift),
`ModelCategory/Bifibrant.lean` (full-subcategory objects and ordinary instance),
`ModelCategory/Basic.lean` (actual model axioms), and
`CategoryTheory/Localization/Construction.lean` (LocQuiver, relations,
Localization, Q). The relation quotient is exactly finite unoriented edge
zigzags, so no Kan assumption is needed to interpret π₀.

## Duplicate searches, edge cases, and remaining gates

Independent rg searches of Mathlib, upstream WeilConjectures, Q51 lean/Sheaf,
and Q51 dag/lean_names_upstream.json used `π₀.*sHom|sHom.*π₀`, component/homotopy
category vocabulary, and all introduced declaration names. No matching enriched
component-category construction or name collision was found. The absent
slopmaster2/dag/lean_names_upstream.json was not treated as a negative search;
the existing Q51 index and upstream source tree were checked instead. I read
Mathlib BifibrantObjectHomotopy.lean:39–159 and FundamentalLemma.lean:34–118:
the ordinary right-homotopy quotient and its map-surjectivity theorem overlap
parts of this statement, but do not identify the *specified enrichment's*
components or the chosen RQ formulas by a one-line specialization. The item's
actual recorded LeanSearch, Loogle, LeanFinder, and grep results were also read;
the worker report's search history is consistent with these candidates.

Empty mapping simplicial sets remain empty quotients; no Nonempty or chosen
vertex is assumed. Identities still give the required self vertices. Empty or
zero-object examples impose only the original model-category conditions, and
disconnected mapping spaces are allowed. Δ⁰ evaluation and both Δ¹ endpoints,
including constant paths, use the correct dimensions. There is no characteristic
or coefficient restriction. Object universe u and hom/enrichment universe v
remain independent; finite-string localization may have larger hom universe,
which Mathlib's construction handles without equating u and v.

Every def contains actual data. Postponed mathematical proofs are named theorems
with `sorry`, matched to item Steps 1 and 3 and the main nine-step plan. Category
law fields merely apply those named theorems. No arbitrary map or choice from
an undetermined existence statement is used. There are no new independent
prerequisites, no pro-etale substitute, no hidden auto-implicit binders, no
forbidden imports or Sheaf-prefixed declaration names. All fixed lines have
length ≤100. Both required report sections are present.

## Compiler evidence and final checks

The delivered report claimed a clean scompile run without including its full
output. I reproduced the immutable original with:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q51 lem-coef-simplicial-bifibrant-localization snapshot/lean/Sheaf/CategoryTheory/SimplicialBifibrantLocalization.lean`

Exit 0, no diagnostics: sandbox 2.0 s, library 1.9 s. The installed wrapper now
announces server compilation and runs the side-overlay compiler there; its
output confirms private `/dev/shm/nt-tmp/.../.lbuild` artifacts. I used that
prescribed wrapper, never direct ssh, a global/lake build, or a live Lean write.

Final replacement command:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q51 lem-coef-simplicial-bifibrant-localization fixes/lean/Sheaf/CategoryTheory/SimplicialBifibrantLocalization.lean`

Exit 0, no errors or warnings: sandbox 1.8 s, library 1.9 s, private overlay
`/dev/shm/nt-tmp/nt-local-compile-yfobqwdz/.lbuild`. Earlier replacement runs
reported a long-line warning; that line was shortened before this final clean
run. No timeout was raised or linter suppressed to pass.

The original and fixed lean.statement fields were compared byte-for-byte with
the corresponding theorem signatures (keyword through the text before `:=`).
The fixed declarations list registers the complete public helper interface.
The complete fixes preserve the TeX statement and DAG edges. No tool that
claims, delivers, merges, changes Git state, or runs project preflight was used.
All writes are confined to review.md and fixes/. No substantive fault remains.
