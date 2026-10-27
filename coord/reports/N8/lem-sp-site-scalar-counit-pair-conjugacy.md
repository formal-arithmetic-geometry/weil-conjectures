## Worker report

The module `Sheaf.CategoryTheory.SiteScalarCounitPairConjugacy` states
`CategoryTheory.site_scalar_counit_pair_conjugacy`, with one postponed proof (`sorry`).
It renders the original node without a statement correction, new definitions, or dependency repairs.
Only the item's `lean` field changes. The node's seven-step natural-language proof is included
in the theorem docstring, including the separate evaluation calculation and essential-surjectivity
argument. The current blueprint source was read at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`,
Charts paragraph (lines 20–36). This lemma is the node's explicit categorical expansion of that
paragraph; no geometric hypotheses are introduced into the abstract lemma.

### Hypotheses and objects

- The eight categories are `XA`, `YA`, `XB`, `YB`, `XA'`, `YA'`, `XB'`, `YB'`, with
  eight separate `Type u...` binders and eight `Category.{v...}` instances. All sixteen
  universes are explicitly declared and independent.
- `FA`, `HA`, `FB`, `HB`, `FA'`, `HA'`, `FB'`, `HB'` have exactly the eight prescribed
  sources and targets. `Functor` includes preservation of identities and composition.
- `epsA : HA ⋙ FA ⟶ 𝟭 YA`, `epsB : HB ⋙ FB ⟶ 𝟭 YB`, and their primed versions
  are precisely the four natural evaluation maps. They are natural transformations in
  functor categories, with no adjunction structure.
- `CXA`, `CYA`, `CXB`, `CYB` are the four comparison functors; `[CYA.EssSurj]` is
  exactly essential surjectivity of the A-side comparison on Y. No other comparison
  functor is assumed essentially surjective, full, or faithful.
- `cA : FA ⋙ CYA ≅ CXA ⋙ FA'` and `cB : FB ⋙ CYB ≅ CXB ⋙ FB'` render the
  prescribed left comparisons. The reversed written order is Mathlib's diagrammatic
  functor composition: `F ⋙ G` means first F, then G.
- `rA : CYA ⋙ HA' ≅ HA ⋙ CXA` and `rB : CYB ⋙ HB' ≅ HB ⋙ CXB` render the
  prescribed right comparisons, with exactly their stated orientations.
- `h_eval_A` and `h_eval_B` render the two evaluation formulas componentwise:
  `F'.map (r.hom.app L) ≫ c.inv.app (H.obj L) ≫ CY.map (eps.app L)` equals
  the primed evaluation at `CY.obj L`. Mathlib's `f ≫ g` means g after f, so
  this is the node's right-to-left displayed composite in execution order.
- `TX`, `TY`, `TX'`, `TY'` are precisely the four coefficient transition functors.
- `deltaX : CXA ⋙ TX' ≅ TX ⋙ CXB` and
  `deltaY : CYA ⋙ TY' ≅ TY ⋙ CYB` render the two coefficient comparison isomorphisms.
- `q : FA ⋙ TY ⟶ TX ⋙ FB`, `q' : FA' ⋙ TY' ⟶ TX' ⋙ FB'`,
  `a : HA ⋙ TX ⟶ TY ⋙ HB`, and `a' : HA' ⋙ TX' ⟶ TY' ⋙ HB'` are the four
  specified natural maps. No `IsIso` assumption is attached to any of them.
- `h_left`, quantified over `M : XA`, is the first comparison square, with execution
  order `TY'(cA(M)), q'(CXA(M)), FB'(deltaX(M))` on the left and
  `deltaY(FA(M)), CYB(q(M)), cB(TX(M))` on the right.
- `h_right`, quantified over `L : YA`, is the second comparison square, with
  execution order `a'(CYA(L)), HB'(deltaY(L)), rB(TY(L))` on the left and
  `TX'(rA(L)), deltaX(HA(L)), CXB(a(L))` on the right.

### Parallel pairs, comparison, and conclusions

The local mathematical abbreviations D, E, D', E', and Z are expanded directly in the
statement, so consumers do not need file-local notation, hidden lets, or helper definitions:

- `D_L` is `q.app (HA.obj L) ≫ FB.map (a.app L) ≫ epsB.app (TY.obj L)`.
- `E_L` is `TY.map (epsA.app L)`.
- `D'_K` is `q'.app (HA'.obj K) ≫ FB'.map (a'.app K) ≫ epsB'.app (TY'.obj K)`.
- `E'_K` is `TY'.map (epsA'.app K)`.
- `Z_L` is the composite
  `TY'.map (FA'.map (rA.hom.app L)) ≫ TY'.map (cA.inv.app (HA.obj L)) ≫ deltaY.hom.app (FA.obj (HA.obj L))`.
  Each factor is the image of an isomorphism component or an isomorphism component itself,
  so this is exactly the hom of the stated composite isomorphism. No isomorphism is
  identified with an identity, and no arbitrary replacement is chosen.
- The first outer conjunct, quantified over L, is `D'_(CYA L) ≫ deltaY(L) = Z_L ≫ CYB(D_L)`.
- The second outer conjunct, separately quantified over L, is
  `E'_(CYA L) ≫ deltaY(L) = Z_L ≫ CYB(E_L)`.
  Neither conjunct is inside an implication assuming D = E.
- The third outer conjunct is precisely `(∀ L, D_L = E_L) → ∀ K : YA', D'_K = E'_K`.
  This includes arbitrary target objects K, rather than just the image of CYA.

Functor composition has its canonical Mathlib associativity identifications; all displayed
claims are component equations, so no noncanonical associator choices arise.

### Dependency declarations used

`def-nagata-category` is a Mathlib leaf: its `mathlib_match` records
`CategoryTheory.Category` in `Mathlib.CategoryTheory.Category.Basic`. I read its
full signature, docstring, and inherited `CategoryStruct` fields. The category laws
`id_comp`, `comp_id`, and `assoc` match the dependency exactly. The module publicly
imports `Mathlib.CategoryTheory.EssentialImage`, which transitively exposes this declaration
and the functor-category, natural-transformation, and natural-isomorphism interfaces.
It directly supplies `CategoryTheory.Functor.EssSurj`, whose definition and essential-image
interpretation were read. `Functor` in `Mathlib.CategoryTheory.Functor.Basic` and `NatTrans`
in `Mathlib.CategoryTheory.NatTrans` were also read, including their preservation and
naturality fields. The only proof dependency is the same category leaf, already imported.

### Edge cases checked

Empty `YA` is allowed: essential surjectivity then forces `YA'` empty, so the final
universal conclusion remains vacuous as required. Empty categories elsewhere are
constrained only by existence of the given functors, not by extra nonemptiness binders.
Identity comparisons reduce the displayed equations to the original component formulas.
In additive categories zero evaluation maps and noninvertible q/a maps are allowed;
the calculation never divides by any of these maps. With one-object categories the
statement is the corresponding naturality/intertwining calculation, including
nontrivial comparison automorphisms. All eight object/morphism universe pairs remain
independent, including categories with objects one universe above their morphisms.
There is no extra smallness, adjunction, full-faithfulness, or invertibility hypothesis.
No node fault or STATEMENT-DISPUTED issue was found.

### Searches for an existing statement

All service searches used
`python3 /home/ubuntu/weil-launcher-all/batch2/msearch.py N8 lem-sp-site-scalar-counit-pair-conjugacy ...`.
Their raw records are in the sandbox's `searches.jsonl`.

- LeanFinder: “Two parallel evaluation composites are conjugate across commuting
  comparison squares of functors without adjunction assumptions, and equality extends
  along an essentially surjective functor”. Eight hits, headed by
  `CategoryTheory.Adjunction.leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm` and
  `leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm`, followed by conjugateEquiv
  commutation/composition/whiskering lemmas. These require adjunctions and are not
  the arbitrary-evaluation pair statement.
- Loogle: `CategoryTheory.NatTrans.naturality, CategoryTheory.Functor.map_comp`.
  Success, zero hits for their combination; these individual laws support the
  elementary calculation but do not state the whole lemma.
- Mathlib grep: `conjugateEquiv_counit|counit.*conjuga|essSurj.*comp`, restricted to
  `CategoryTheory`. Twenty hits, principally essential-surjectivity composition,
  linearity, and mates. I read `conjugateEquiv_counit` and its inverse variant in
  `Mathlib/CategoryTheory/Adjunction/Mates.lean`: both require two adjunctions
  and do not state these two equations for arbitrary evaluations.
- LeanSearch: “Conjugacy of two arbitrary natural evaluation composites under site and
  coefficient comparison isomorphisms, with equality extended by essential surjectivity”.
  Eight hits: function conjugation, bicategorical adjunction mates,
  `CategoryTheory.Iso.isoCongr`, a Galois evaluation congruence, and `compEvaluation`.
  None states the comparison-square pair or the essential-surjectivity implication.
- `rg` searched both `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `scalarCounit|scalar_counit|counitPair|counit_pair`. Hits are concrete scalar-counit
  definitions in derived coefficient modules and unrelated pairing formulas.
  The narrower category-theory search found `scalarCounitTransport` in
  `Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift`; I read its full signature.
  It transports one evaluation through a specified comparison and two arrows,
  not the present two-square pair calculation, and is private.
- The required `grep -rn` of the exact node id in `lean/WeilConjectures` has no hit.
  `rg` of `site_scalar_counit_pair_conjugacy` across Mathlib, both project source
  roots, and `dag/lean_names_upstream.json` has no hit. The chosen name is fresh.

### Validation

The prescribed `scompile.py N8 lem-sp-site-scalar-counit-pair-conjugacy` compiled the
module cleanly in both sandbox and library modes (2.5 s and 1.8 s). Every variable
and universe is explicitly bound. The node's `lean.statement` is copied verbatim
from the theorem keyword to immediately before `:=`; the JSON uses indent 1,
Unicode, and a final newline. No shared repository file was edited and no direct
Git command was run.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
