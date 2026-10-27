## Worker report

This repair supplies `lean/Sheaf/AlgebraicGeometry/UniversalUnramifiedRadicialOpen.lean`
and the node's `lean` binding to
`AlgebraicGeometry.exists_universalUnramifiedRadicialOpen`. The sole theorem has
proof `sorry`; there are no new definitions, helper axioms, or proved theorems.
The node was copied afresh from the live read clone, including Q18's reviewed
nine-step proof. Only `lean` changes. In particular `proof`, `proof_deps`,
`split_report`, `statement` and `stmt_deps` remain exactly as live.

I read the statement and all nine proof steps of the live node, and Stacks
`spaces-more-morphisms.tex`, Tag 05X9,
`spaces-more-morphisms-lemma-where-unramified-universally-injective`, together with
the preceding Tag 05X8. The scheme specialization has exactly the three
hypotheses on p and p2 used below; there is no hypothesis on q beyond the triangle.

The statement correspondence is as follows:

- A, B and C are schemes: `{A B C : Scheme.{u}}` with explicitly declared
  `universe u` and `set_option autoImplicit false`.
- p, q and f have their specified domains and codomains:
  `(p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)`.
- The commutative triangle q after f equals p:
  `(hf : f ≫ q = p)`.
- p is locally of finite type: `[LocallyOfFiniteType p]`.
- Its underlying map is closed: `(hp : IsClosedMap p.base)`.
  `IsClosedMap` means precisely that images of closed subsets are closed.
- The underlying map of p2 from A ×_C A is closed:
  `(hp2 : IsClosedMap (pullback.fst f f ≫ p).base)`.
  The fibre product is over C (the two maps are f), not over B.
- There exists an open subscheme V of B: `∃ V : B.Opens`;
  `V.toScheme` is the restriction to this open and `V.ι` its canonical open immersion.
- Every test scheme and morphism to B:
  `∀ (T : Scheme.{u}) (h : T ⟶ B)`. The universe is arbitrary, as in the
  existing universal-closed-immersion statement. There is no fixed small universe,
  independent potentially smaller test universe, or affine/reduced/finite-type
  restriction on T.
- The induced f_T is `pullback.map p h q h f (𝟙 T) (𝟙 B) ... ...`.
  By the signature of `pullback.map`, its source is `pullback p h` = A ×_B T
  and its target is `pullback q h` = C ×_B T. It is the map induced by f
  on the first coordinate and the identity on T. The first compatibility proof
  is hf.symm after removing composition with the identity on B; the second
  is the identity compatibility for h. These proofs merely type the canonical
  map; no arbitrary comparison map is assumed or chosen.
- Unramifiedness is `IsUnramified` of that map, and universal injectivity is
  `UniversallyInjective` of the identical map, joined by `∧`.
- The `↔` has the entire conjunction on its left, and its right is precisely
  factorization `∃ l : T ⟶ V.toScheme, l ≫ V.ι = h`.
  No uniqueness or additional property is added to the conclusion.

Statement dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`
  (Scheme.lean:42,74).
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` (FiniteType.lean:43).
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.map`
  (HasPullback.lean:95,111,115,270), with scheme pullbacks from
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (OpenImmersion.lean:38), and the standard
  open subscheme `Scheme.Opens.toScheme` and `.ι` in
  `Mathlib.AlgebraicGeometry.Restrict` (Restrict.lean:46,52).
- `def-weil-unramified-morphism`:
  `Sheaf.AlgebraicGeometry.UnramifiedMorphism`,
  `AlgebraicGeometry.IsUnramified`. I read its full definition and docstring:
  it is `LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`.
  The recorded dependency is usable and is imported directly.
- `def-weil-radicial-morphism`: its `mathlib_match` is used directly:
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`,
  `AlgebraicGeometry.UniversallyInjective` (line 47). The docstring and full
  class field quantify over base changes, and `tfae_universallyInjective`
  (line 107, Tag 01S4) supplies the recorded equivalent formulations.
  This dependency needs no replacement module or lean repair.

The module also imports the already stated proof dependencies, as required by
stages/2-statements.md §3(7). Affine finite-type criteria and stability use
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.RingHomProperties`;
common extension fields use `WeilConjectures.FieldTheory.CommonExtensionFields`
(`Field.exists_common_extension`); residue fields use
`Mathlib.AlgebraicGeometry.ResidueField`; the fibre-product point description
uses `Mathlib.AlgebraicGeometry.PullbackCarrier` (`Scheme.Pullback.carrierEquiv`
and its two projection lemmas); the unramified locus uses
`Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange`
(`unramifiedLocus_baseChange`); open factorization, base change and image
isomorphisms use the already imported `OpenImmersion` and `Restrict`.
Proof-only imports are plain `import`; statement dependencies are `public import`.
The theorem docstring records all nine live proof steps, including step 5's
restriction argument and the distinction between closed maps and universally
closed maps.

Edge cases checked before writing:

- A empty: every f_T is unramified and universally injective, so V = B is allowed.
- T empty: both morphism properties hold and the empty map factors through any V.
- f the identity (q = p): V = B satisfies the conclusion.
- C empty forces A empty, so the first check applies.
- A nontrivial finite purely inseparable extension of a field, with B = C
  the spectrum of the base field: the map is universally injective but not
  unramified, so V is empty. This checks that the two properties are conjoined.
- A nontrivial finite separable field extension, or two copies of B mapping to B:
  the map can be unramified but fails universal injectivity, so V is empty
  over a field. This checks the second condition and the relative self-product.
- Nonreduced T is included without any restriction; neither factorization nor
  unramifiedness was replaced by a test only on geometric points.
- Ordinary closedness is used exactly as assumed; q need not be separated and
  p need not be quasi-compact or universally closed.

Searches actually run (2026-10-22):

- `msearch.py ... leanfinder` with query
  `An open subscheme of B represents the base changes of a morphism that are unramified and universally injective, when its source and relative self product map closedly to B`:
  eight hits, including `FormallyUnramified.isOpenImmersion_diagonal`,
  `FormallyUnramified`, `UniversallyInjective`, and base-change instances;
  none states this representing open in B.
- `msearch.py ... loogle` with query `"UniversallyInjective", "IsUnramified"`:
  OK, zero hits.
- `msearch.py ... grep` with query
  `where.*unramified|unramified.*universally.*injective|unramified.*radicial`
  in `AlgebraicGeometry`: OK, zero hits.
- `msearch.py ... leansearch` with query
  `An open subset of the parameter scheme represents unramified and universally injective base changes of a morphism`:
  eight hits about `UniversallyInjective`, `FormallyUnramified`, `Scheme.Opens`,
  and their constructors or base-change stability; no exact theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `where_unramified|unramified.*[Rr]adicial|unramified.*[Uu]niversally|universal-unramified-radicial-open`:
  only the downstream `UniversalClosedImmersionOpen.lean` docstring cites this
  item; it does not state it. `grep -rn` for this item in `lean/WeilConjectures`
  found no occurrence.
- `rg` over Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the proposed declaration/module names
  `exists_universalUnramifiedRadicialOpen|universalUnramifiedRadicial|UniversalUnramifiedRadicialOpen`:
  no existing name found.

Validation: the prescribed `scompile.py N9 lem-sfb-universal-unramified-radicial-open`
compiled this file in sandbox and library module modes with exit code 0 and no
warnings (4.7 s and 6.8 s). No statement dispute or source correction is needed.

## Second reading by N9

I performed a separate second pass with the written module, node copy, live node,
and Tag 05X9 open. This is N9's own second reading, not a claim to review by a
second agent; the dispatcher explicitly forbids starting other agents. The
maintainer's independent stage-2 review remains the external review.

For the first sentence I checked all three scheme binders and all three map
signatures, and the orientation of `hf : f ≫ q = p`. For the assumptions I
checked that finite type is local, that `hp` is ordinary closedness of p.base,
and that `hp2` uses `pullback.fst f f ≫ p`, whose domain is A ×_C A. No extra
property of q appears. For the conclusion I checked the existential quantifier
on V comes before both universal quantifiers, the test scheme shares the
arbitrary universe u of the scheme category, and h is completely unrestricted.
I reopened `pullback.map`'s full signature: its first cospan is `(p,h)`, its
second is `(q,h)`, and its three vertical maps are `(f,id_T,id_B)`, so it has
exactly the node's source and target. Both conjuncts contain this same expression.
The parentheses place the conjunction entirely to the left of `↔`. Finally
`l ≫ V.ι = h` expresses the requested factorization through the actual open
subscheme of B, rather than a subset-only substitute.

I checked the six statement-dependency bindings against their source definitions,
including that `IsUnramified` contains the locally-finite-type condition and that
`UniversallyInjective` means universal injectivity, not injectivity only of f_T.
The empty-source, empty-test, identity and two field-extension examples above
still fit every binder. I also compared the node copy structurally with the
live node: the only differing key is `lean`; the nine proof steps, proof_deps,
review fields and split_report are retained. The theorem docstring follows those
nine steps, with the precise open restriction argument of step 5. No mismatch
was found in this second pass, and no statement correction was made.

Return-point repairs:

1. H1: replaced the stage-1-only packet with an actual Lean module and complete
   lean record, compiled through scompile.py. There is exactly one sorry theorem
   attached to the item and no unattached declarations.
2. H2 and supersession: started from the current live node containing Q18's
   reviewed nine-step split. The seven-step returned split is not used or
   re-delivered. No proof, proof dependency, split report or review field changes.
3. H11: supplied this actual second reading, checking every hypothesis, both
   conjuncts, the canonical map and both sides of the equivalence against the
   live node and source. The repair is substantive Lean work, not a re-push of
   returned head 7eb9ee39947a.
