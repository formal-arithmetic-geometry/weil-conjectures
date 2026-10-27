## Worker report

The module `Sheaf.CategoryTheory.NormalizedMateScalarSiteTransport` states the
node without changing its mathematical statement. Its declarations are
`CategoryTheory.normalizedMateTransport` (real five-factor construction),
`CategoryTheory.normalizedRightMate` (the first assertion), and
`CategoryTheory.normalizedMateScalarSiteTransport` (the second assertion,
including the specified mate and its extension to every primed object).
Both theorem proofs are `sorry`; the definition has no postponed data or proof.
Every declaration belongs to this node and carries its source and blueprint tag.

Hypothesis and conclusion correspondence:

- The four original categories are `CA, DA, CB, DB`, with separately bound object
  universes `u₁,...,u₄` and morphism universes `v₁,...,v₄`.
- The functors are exactly `FA, GA, HA, FB, GB, HB`; the specified adjunctions
  are `adjA : FA ⊣ GA` and `adjB : FB ⊣ GB`, with their actual `.counit`.
- The two right-adjoint model comparisons are `γA : HA ≅ GA` and `γB : HB ≅ GB`.
  The expression `FA.map (γA.hom.app K) ≫ adjA.counit.app K` is exactly z_A,K;
  the corresponding B expression appears in `hnorm`. No new counit is chosen.
- `S, T, q, a` give the scalar functors and the specified natural isomorphisms.
  `q : FA ⋙ T ≅ S ⋙ FB` is TF_A ≅ F_B S in Mathlib's diagrammatic notation.
  `a : HA ⋙ S ≅ T ⋙ HB` is SH_A ≅ H_B T.
- `hnorm` is exactly the displayed normalization for every `K : DA`, with the
  three factors on the left written in diagrammatic composition order.
- The arrow b is the existing `mateEquiv adjA adjB q.inv`, not an unconstrained
  comparison. `mateEquiv_counit` identifies its inverse transpose as
  `q.inv.app (GA.obj K) ≫ T.map (adjA.counit.app K)`.
- `normalizedRightMate` asserts the component equality
  `S.map (γA.inv.app K) ≫ a.hom.app K ≫ γB.hom.app (T.obj K)` and `IsIso` of
  the entire natural transformation. Thus its naturality is included by its type.
- The four new categories `CA', DA', CB', DB'` have independent object universes
  `u₅,...,u₈` and morphism universes `v₅,...,v₈`.
- `FA', GA', FB', GB'` and `adjA', adjB'` are the specified new adjunctions.
- `UA, VA, UB, VB` are equivalences `≌`, with their functor, inverse functor and
  natural isomorphisms. They are not merely fully faithful arbitrary functors.
- `cA, cB, ρA, ρB` are exactly the given left/right comparison isomorphisms.
  `hcA` and `hcB` are the actual two counit equations, for every original object.
- `S', T', δX, δY, q'` are the additional scalar functors and comparisons.
  `hsquare` is exactly the displayed square, at every `M : CA`. None of its
  comparisons is identified with an identity or replaced by a chosen mate.
- `normalizedMateTransport ρA ρB δX δY b` has endpoints
  `VA.functor ⋙ GA' ⋙ S' ⟶ VA.functor ⋙ T' ⋙ GB'`. Expanding its component
  gives, in order, `S'(ρA.inv)`, `δX`, `UB(b)`, `ρB`, `GB'(δY.inv)`.
  This is precisely the specified arrow bar-b, with all five directions fixed.
- The first conjunct of `normalizedMateScalarSiteTransport` is the asserted
  counit equation for bar-b, including the inverse of q' at `GA'(VA K)`.
- Its second conjunct identifies this constructed natural transformation with
  `Functor.whiskerLeft VA.functor (mateEquiv adjA' adjB' q'.inv).natTrans`.
  This is the uniqueness-of-transpose assertion, with naturality in K.
- Its third and fourth conjuncts assert invertibility of bar-b as a natural
  transformation and invertibility of the specified right mate on all of DA'.
- Its last conjunct gives the component at every `K' : DA'` and every isomorphism
  `j : VA.functor.obj K ≅ K'`: conjugation of bar-b by `S'GA'(j.inv)` and
  `GB'T'(j.hom)`. This records arbitrary isomorphic replacements, and since VA
  is an equivalence its image covers every new object. The equality to the
  fixed mate makes this independent of the chosen presentation.
- There are no additive, tensor, ring, sheaf, or geometric hypotheses. Empty
  categories and arbitrary category sizes are allowed.

Dependency declarations read and used:

- `def-nagata-category` is the Mathlib leaf `CategoryTheory.Category`, in
  `Mathlib.CategoryTheory.Category.Basic`; its full signature and laws were read.
- `def-weil-pbc-adjunction-mate` is the Mathlib leaf `CategoryTheory.mateEquiv`,
  in `Mathlib.CategoryTheory.Adjunction.Mates`. The signature, construction,
  `TwoSquare` definition and `mateEquiv_counit` were read. It is used directly.
- The proof dependency `lem-weil-pbc-adjunction-of-natural-bijection` is the
  Mathlib leaf `CategoryTheory.Adjunction.mkOfHomEquiv`, in
  `Mathlib.CategoryTheory.Adjunction.Basic`. Its signature, constructor and
  `homEquiv`/`homEquiv_counit` were read. The proof plan uses the inverse Hom
  bijection's injectivity. Its module is an explicit non-public proof import.
- `Mathlib.CategoryTheory.Equivalence` supplies the specified equivalences.

Source: read the full current-blueprint exceptional-reduction proof at
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/`
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`, particularly
Existence, uniqueness, naturality and Charts. Read all six proof steps in the
node. Both theorem docstrings give these calculations and their dependencies.

Edge cases checked before writing: all identity data gives identity mates and
identity transport; a nontrivial model automorphism shows that hnorm is needed;
no implication that an arbitrary mate of an isomorphism is invertible is used.
For empty categories all objectwise equations quantify over the empty category
and equivalence still ensures coverage of the new category. The last clause
uses every j, rather than only the chosen equivalence counit. All sixteen
category universes are independent; no equality of site universes is imposed.
The generic five-factor construction uses only actual functors and given
natural isomorphisms, without a choice or a Nonempty witness.

Searches for an existing statement:

- msearch.py leanfinder: "Counit normalized right adjoint models identify a
  right mate by conjugation, preserved by a square of equivalences preserving
  counits" returned eight results: mateEquiv_counit, mateEquiv_counit_symm,
  mateEquiv, mateEquiv_apply, unit_mateEquiv, conjugateEquiv_counit,
  conjugateEquiv_counit_symm, mateEquiv_symm_apply. These give the mate
  correspondence and its equations, not the complete two-part normalized
  model and eight-category transport result.
- msearch.py loogle: `CategoryTheory.mateEquiv, CategoryTheory.Equivalence`
  returned zero results.
- msearch.py grep: `mateEquiv.*(counit|conjug)|conjug.*mateEquiv` in
  CategoryTheory returned fourteen hits in Adjunction.Mates, bicategorical
  mates and Monoidal.Closed.Functor. None gives this node's complete result.
- rg searched the project Sheaf and upstream WeilConjectures directories for
  normalized mates/site transport and this exact node id. Related specialized
  scalar/coefficient results exist, but no declaration for this abstract node.
  Exact searches for the three new declaration names in both project trees
  and Mathlib returned no hits.

No new DAG nodes, dependency repairs, statement correction or disputed statement.
Only the item's lean field is changed in its node copy. The stage-1 reviewed
record is preserved. The sandbox contained no prior module at the start of
this retry; its earlier reported blocker was the stage-2 preflight treating a
stage-1 split/review as an already finished item. This packet retries that
check without altering any review, status, or reopening field.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
