## Worker report

The module `Sheaf.CategoryTheory.SiteCoveringsCommonRefinement` states the binary
common-refinement result for every choice of fibre products, including the exact projection
maps, and the finite-family consequence. Both theorem proofs are `sorry`; no definition or
instance is introduced and nothing is proved. The node's statement and dependencies are unchanged.

Source read: Stacks Project, Sites, Lemma 7.10.5, Tag 00W6, statement and proof,
https://stacks.math.columbia.edu/tag/00W6 (the local literature checkout is not present).
Its proof constructs the covering by pullback and composition exactly as the node describes.
The finite-family clause is the stated immediate finite induction, with identity-cover base case.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A site is `{C : Type u} [SmallCategory C]`, `J : Precoverage C` with
  `[J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]`.
  This is precisely the existing encoding in def-weil-pbc-sites-and-cohomology's lean.note.
  These are genuine site axioms, with no global HasPullbacks C hypothesis.
- The common object is `{U : C}`. The two indexed coverings are
  `E : ZeroHypercover.{w} J U` and `F : ZeroHypercover.{w'} J U`.
  Their fields `I₀`, `X`, `f`, and `mem₀` are the indices, members, structure maps,
  and covering assertions; the two index universes are independent and explicitly bound.
- Any choice of `V_j ×_U U_i` is `W : E.I₀ × F.I₀ → C`, with projections
  `p ij : W ij ⟶ F.X ij.2` and `q ij : W ij ⟶ E.X ij.1`.
  `h ij : IsPullback (p ij) (q ij) (F.f ij.2) (E.f ij.1)` states their fibre-product
  universal property, in exactly the V-then-U order of the node. This is not an additional
  restriction on the coverings: it expresses the node's arbitrary choice of fibre products.
  Existence of these choices is provided by the site's HasPullbacks axiom.
- The family covers U exactly when
  `Presieve.ofArrows W (fun ij => q ij ≫ E.f ij.1) ∈ J U`.
  This is the first conclusion, indexed by the product, not a sigma type or a sieve intersection.
- The projection to E is a `PreZeroHypercover.Hom` from this very family to
  `E.toPreZeroHypercover`, with `r.s₀ = _root_.Prod.fst` and `HEq r.h₀ q`.
  The projection to F has `r.s₀ = _root_.Prod.snd` and `HEq r.h₀ p`.
  These are the two further conclusions. HEq is only transport for the dependent codomain:
  after the stated equality of index maps it says the component maps are exactly q or p.
  In particular the conclusions require the specified projections, not just unspecified
  refinement maps. The Hom's w₀ field gives the triangle equation over id_U.
  PreZeroHypercover.Hom is the same underlying notion as ZeroHypercover.Hom; combining
  the first conclusion with the displayed family gives a covering with these morphisms.
- The finite-family clause is the second declaration:
  `(K : Type t) [Finite K] (E : K → ZeroHypercover.{w} J U)` and
  `∃ W : ZeroHypercover.{w} J U, ∀ k : K, Nonempty (ZeroHypercover.Hom J W (E k))`.
  The common covering and a refinement to every member are both asserted. The family of
  coverings may have any finite cardinality; each covering may have arbitrary index cardinality.
  Finite products of Type w index sets stay in Type w. There is no Fintype data assumption
  or Nonempty K assumption.

Dependency declarations used:

- def-weil-pbc-sites-and-cohomology records Mathlib's existing notions. This file uses
  `CategoryTheory.Precoverage`, `CategoryTheory.Precoverage.HasIsos`,
  `CategoryTheory.Precoverage.IsStableUnderComposition`,
  `CategoryTheory.Precoverage.IsStableUnderBaseChange`, and
  `CategoryTheory.Precoverage.HasPullbacks`, defined in
  `Mathlib.CategoryTheory.Sites.Precoverage` and imported by Hypercover.Zero.
  The primary recorded declaration Sheaf.H' and its signature/docstring in
  Mathlib.CategoryTheory.Sites.SheafCohomology.Basic were read; cohomology is not used here.
- def-weil-pbc-site-plus-construction's record explicitly tells citers to use
  `CategoryTheory.Precoverage.ZeroHypercover`, its `Hom` abbreviation and the underlying
  `CategoryTheory.PreZeroHypercover.Hom`, in
  `Mathlib.CategoryTheory.Sites.Hypercover.Zero`. Their definitions and Hom fields were read.
  Its primary plusObj definition in Mathlib.CategoryTheory.Sites.Plus was read; no plus
  presheaf is needed for this node. Thus no unused plus/cohomology import is added.
- The standard `CategoryTheory.IsPullback` is available through the same import.
  Existing `ZeroHypercover.inter`, `PreZeroHypercover.interFst` and `interSnd` were read;
  they use chosen pullbacks and provide the binary canonical construction, but do not
  state the arbitrary-choice and finite-family conclusions of this node.

Edge cases checked before writing:

- Either covering may have empty index type when the site's axioms permit it. The product
  family is then empty and base change/composition still assert it is covering. No
  Nonempty instance is required on E.I₀ or F.I₀.
- For an empty finite family, the singleton identity covering witnesses existence; the
  refinement condition is vacuous. For a singleton family, the member refines itself.
- Duplicate members and index labels are retained; morphisms contain actual index maps.
  A presieve forgets duplicate labels only for covering membership, in accordance with
  the dependency's presieve and reindexing convention.
- Only pullbacks of covering arrows are needed, so sites without all categorical pullbacks
  are included. Noncanonical choices of pullback objects and projections are quantified
  explicitly. The projection order matches V_j ×_U U_i.
- All universes and all binders are explicit. The finite family universe t need not equal
  the covering-index universe w or object universe u. Finite induction preserves w.

Searches for an existing statement (2026-10-11 UTC):

- msearch.py leanfinder: "Two indexed coverings of an object in a site have a common
  refinement by pairwise pullbacks; any finitely many coverings have a common refinement".
  Eight hits: finite pretopology/coverage constructions, coherent coverage, CoversTop.cover,
  and GrothendieckTopology.arrow_intersect; none states this indexed-family result.
- msearch.py loogle: "Precoverage.ZeroHypercover.inter, PreZeroHypercover.interFst,
  PreZeroHypercover.interSnd". No hits; online index does not know the first identifier.
  Local source inspection finds all three in Hypercover.Zero, as described above.
- msearch.py grep: "common.refinement|exists.*refinement|interFst|interSnd" in
  CategoryTheory/Sites. Eight hits: intersection projection definitions for zero/one
  hypercovers and a homotopy construction; no arbitrary-choice or finite-family theorem.
- msearch.py leansearch: "finite family of coverings of an object of a site has a common
  refinement". Unavailable, Internal Server Error; no search verdict drawn from it.
- rg on WeilConjectures and lean/Sheaf for common-refinement/refinement/interFst/interSnd
  finds stratifications, compactifications, etale-site intersections, affine/fpqc refinements
  and comments using refinements; none is this statement for a general site.
- rg on dag/lean_names_upstream.json finds stratification/compactification names, not this
  result. The item id has no existing declaration in WeilConjectures. Searches for the two
  chosen full declaration names in Mathlib, WeilConjectures, lean/Sheaf and the upstream
  name index find no collision.

Validation: lcompile.py passed on the module, exit code 0, with no errors or warnings.
Final delivery dry run is run after this report and node record are written.
No node fault, statement correction, new node, dependency module, or disputed statement.

## Second reading by F1

I independently read the node, its Stacks source (Sites, Lemma 7.10.5, Tag 00W6),
and the submitted module. The node introduces a category `C : Type u` with
`[SmallCategory C]`, a precoverage `J` with `HasIsos`, stability under composition and
base change, and pullbacks; an object `U : C`; two zero hypercovers `E` and `F` of
`U` with independent index universes; a family `W : E.I₀ × F.I₀ → C`; maps `q` to
`E.X` and `p` to `F.X`; and pullback squares `h`. The first conclusion is that the
composite family `q ≫ E.f` is in `J U`. The next two clauses give refinement
morphisms with index maps `Prod.fst` and `Prod.snd`, component maps exactly `q` and
`p` (expressed by `HEq` because the codomain is dependent), respectively. The final
clause asserts existence of one zero hypercover refining every member of a finite
family indexed by an arbitrary finite type `K`.

The Lean signature renders these items exactly: `E : ZeroHypercover.{w} J U`,
`F : ZeroHypercover.{w'} J U`, `W : E.I₀ × F.I₀ → C`, the two displayed map families,
and `h : ∀ ij, IsPullback (p ij) (q ij) (F.f ij.2) (E.f ij.1)`. Its conjunction has
precisely the covering presieve and the two existential `PreZeroHypercover.Hom`
clauses with the stated index equalities and `HEq`s. The finite theorem has
`(K : Type t) [Finite K]` and exactly `∃ W, ∀ k, Nonempty (ZeroHypercover.Hom ...)`.
No hypotheses or conclusion clauses are added or omitted, and all universes are
explicit. `PreZeroHypercover.Hom` is the underlying hom used by the dependency's
`ZeroHypercover.Hom` abbreviation, so this does not change the notion of covering
morphism.

I checked the source proof: it applies base change to each member, then composition,
and observes the two projections; the finite assertion is the stated iteration. Edge
cases remain covered: empty index types give the corresponding empty product family,
empty finite `K` is vacuous and is witnessed by the identity covering, singleton and
zero-index cases impose no hidden `Nonempty` assumptions, and arbitrary pullback
choices are represented by `W` and `h`. The category and object universes are not
restricted. Searches in Mathlib, the source checkout, and `lean/Sheaf` found only the
canonical `inter`, `interFst`, and `interSnd` constructions, no theorem with this
arbitrary-choice and finite-family statement.

No mismatch was found, so no source, node, dependency, or Lean declaration was
changed. The module compiles cleanly with `lcompile.py` (only the intentional
`sorry` proofs are present).
