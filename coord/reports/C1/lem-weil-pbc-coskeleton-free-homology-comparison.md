## Worker report

The module `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison` states
`CategoryTheory.SimplicialObject.isIso_homologyMap_of_local_surjective_coskeletal`.
Its only theorem has proof `sorry`; there are no new definitions, dependency modules,
or statement corrections. The complete seven-step natural-language proof from the node
is carried in its docstring, with the proof dependency names.

Hypothesis and conclusion correspondence:

- A site is `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`.
- An integer `n ≥ 1` is `(n : ℕ) (hn : 1 ≤ n)`.
- Simplicial presheaves of sets are
  `{L K : SimplicialObject (Cᵒᵖ ⥤ Type (max u v w))}`.
- Their morphism is `(f : L ⟶ K)`, a natural transformation, so it commutes
  with all face and degeneracy operators.
- Isomorphism in every degree below `n` is `hlow : ∀ i : ℕ, i < n →
  IsIso (f.app (Opposite.op ⦋i⦌))`.
- Surjectivity in degree `n` after sheafification is `hsurj : Epi
  ((presheafToSheaf J (Type (max u v w))).map (f.app (Opposite.op ⦋n⦌)))`.
  Epimorphism in sheaves of sets is local surjectivity; no objectwise
  surjectivity is asserted.
- Both objects being `n`-coskeletal is precisely `hL` and `hK`, asserting
  `IsIso ((coskAdj n).unit.app L)` and `IsIso ((coskAdj n).unit.app K)`.
  These are the node's canonical morphisms into coskeleton of truncation.
- Any commutative ring is `(R : Type (max u v w)) [CommRing R]`.
- The conclusion is `∀ i : ℕ, IsIso (... .map f)`. The functor inside this
  expression first applies `ModuleCat.free R` objectwise to each presheaf,
  then `presheafToSheaf J (ModuleCat.{max u v w} R)` termwise to the resulting
  simplicial module presheaf, then `alternatingFaceMapComplex` to form its
  chain complex, and finally `HomologicalComplex.homologyFunctor` in degree `i`.
  Thus it is the induced morphism on homology, not merely an unspecified
  isomorphism between the homology objects. The complex differential is the
  alternating sum of the free-module maps induced by the face maps.

Dependency declarations read and used:

- `def-weil-pbc-sheafification`: Mathlib.CategoryTheory.Sites.Sheafification,
  `CategoryTheory.presheafToSheaf`, whose docstring and signature give the
  left adjoint to the inclusion; `sheafificationAdjunction` supplies its unit.
- `def-weil-pbc-simplicial-object`: Mathlib.AlgebraicTopology.SimplicialObject.Basic,
  `CategoryTheory.SimplicialObject`, the functor category `SimplexCategoryᵒᵖ ⥤ C`;
  its face maps `δ` are maps of the standard increasing injections and `σ`
  of the degeneracy surjections.
- `def-weil-pbc-simplicial-coskeleton`: the same Mathlib module,
  `SimplicialObject.truncation`, `SimplicialObject.Truncated.cosk` and
  `SimplicialObject.coskAdj`. Its adjunction unit is the canonical map the node names.
  All three dependency nodes have status `mathlib`; their `mathlib_match`
  records are used directly, and no dependency record is rewritten.

Further existing Mathlib constructions used: `ModuleCat.free` in
Mathlib.Algebra.Category.ModuleCat.Adjunctions (finitely supported functions),
`Functor.whiskeringRight`, `SimplicialObject.whiskering`,
`AlgebraicTopology.alternatingFaceMapComplex` in
Mathlib.AlgebraicTopology.AlternatingFaceMapComplex, and
`HomologicalComplex.homologyFunctor` in
Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex.
No private replacement of any of these notions is defined.

Universe and inference check: `u`, `v`, `w` are explicit. The common value
universe `max u v w` is large enough for the site and its covers, with `w`
arbitrary to allow the coefficients and sets to be larger. No extra existence
hypothesis for sheafification, Kan extension, or homology is added. These
instances are inferred. Locally registering Mathlib's existing lemma
`preservesFilteredColimitsOfSize_shrink` as an instance allows the existing
filtered-colimit preservation of the module forgetful functor to be used
at the smaller cover universe. This registers an existing result and proves
nothing new. All variables are explicit; no auto-implicit binders are used.

Edge cases checked before writing: `n = 1` requires precisely degree-zero
isomorphism; `n = 0` is excluded by the node itself (although the source proves
it too). Homology degree zero is included. Empty simplicial presheaves and
empty sites are allowed; none of the binders requires a section or object.
The zero commutative ring is allowed: no nontriviality, field, characteristic,
or torsion condition is inserted. The identity simplicial map satisfies the
comparison. A locally surjective map need not be objectwise surjective, which
is why the hypothesis is an epi of sheaves and not a surjectivity statement
for each presheaf evaluation.

Source read: the local Stacks checkout was absent, so I opened the authoritative
[Stacks Lemma 01GD](https://stacks.math.columbia.edu/tag/01GD) online. It states
these four hypotheses and the homology conclusion for free abelian groups;
the node's free-R variant follows the same chain homotopy construction for
any commutative ring. The node deliberately restricts `n ≥ 1`, and is kept
unchanged. No statement fault or disputed clause was found.

Searches for an existing comparison (all via msearch.py under this item's id,
except the direct source searches):

- LeanFinder: `simplicial presheaf coskeletal local surjection homology free module
  sheaves`; eight results, including `SimplicialObject.IsCoskeletal` and
  `isoCoskOfIsCoskeletal`, but no comparison theorem.
- Loogle: `CategoryTheory.SimplicialObject.coskAdj,
  AlgebraicTopology.alternatingFaceMapComplex`; zero results.
- Mathlib grep: `cosk.*homology|homology.*cosk`; zero results.
- LeanSearch: `simplicial presheaf coskeleton locally surjective homology
  isomorphism`; unavailable, Internal Server Error.
- Direct rg of WeilConjectures and lean/Sheaf for `cosk.*homology|homology.*cosk`
  and the item's id: no comparison theorem and no declaration carrying this id.
- Direct rg of the project and source for free complexes, free sheaves, alternating
  complexes, and coskeleton: unrelated free-complex-cover and Cech-complex modules,
  no statement matching this node.
- Source declaration index `dag/lean_names_upstream.json` was searched for
  `cosk|homology`; no existing declaration stating this comparison.

The first server compiles identified missing imports and filtered-colimit
universe inference; these were repaired using existing Mathlib imports and
its shrink lemma. A long-line warning was repaired by wrapping the signature.
Final validation is the server compile and deliver2.py --no-push dry run.

## Second reading by C1

I reread the node statement, its Stacks source (Hypercoverings, Tag 01GD,
lines 662--715), and the complete Lean declaration.

- The site is rendered by `{C : Type u} [Category.{v} C]` and
  `(J : GrothendieckTopology C)`; this introduces exactly the node's site.
- The bound `n \ge 1` is rendered by `(n : ℕ) (hn : 1 ≤ n)`; `hn` is present
  as a hypothesis even though the statement body does not need to inspect it.
- Simplicial presheaves of sets are exactly
  `{L K : SimplicialObject (Cᵒᵖ ⥤ Type (max u v w))}` and their morphism is
  `(f : L ⟶ K)`. This is the functor category of set-valued presheaves, with
  no extra pointedness or size restriction beyond explicit universes.
- The lower-degree condition is rendered as
  `hlow : ∀ i : ℕ, i < n → IsIso (f.app (Opposite.op ⦋i⦌))`, matching an
  isomorphism in every degree strictly below `n`.
- Local surjectivity in degree `n` is rendered as the epi hypothesis
  `hsurj : Epi ((presheafToSheaf J (Type (max u v w))).map
  (f.app (Opposite.op ⦋n⦌)))`; this is precisely surjectivity after
  sheafification and does not strengthen it to objectwise surjectivity.
- The two coskeletal hypotheses are `hL` and `hK`, asserting `IsIso` of the
  `coskAdj n` units. These are the canonical maps from each object to
  `cosk_n (sk_n -)`, as required by the node.
- The arbitrary coefficient ring is `(R : Type (max u v w)) [CommRing R]`.
  No field, nonzero, characteristic, finiteness, or Noetherian assumption is
  present.
- The conclusion is `∀ i : ℕ, IsIso (...)`, where the displayed composite is
  objectwise free `R`-modules, termwise sheafification, the alternating-face
  complex, and `homologyFunctor` in degree `i`; its `.map f` is therefore the
  induced homology morphism. All homology degrees, including zero, are
  quantified.

The declaration compiled with `scompile.py`. No mismatch was found and no Lean
or node statement was changed. The proof remains `sorry` as required for stage
2, and the declaration docstring records all seven proof steps and their proof
nodes. The imports are Mathlib-only and all universes and variables are bound.

Edge cases checked: `n = 1` leaves exactly degree zero in the lower-isomorphism
condition; `n = 0` is excluded by the node's explicit hypothesis; homology
 degree zero is included; empty sites and empty simplicial presheaves are not
excluded; the zero commutative ring is allowed; identity maps satisfy the
hypotheses. The universe parameter `w` permits coefficient and set values at
any larger universe without restricting the site's objects.

Existing-definition searches were repeated with LeanFinder, Loogle, LeanSearch,
Mathlib/source `rg`, and the upstream declaration index. They found only the
primitive simplicial/coskeleton, sheafification, free-module, alternating-face,
and homology constructions; no theorem states this local-surjection homology
comparison. Thus this module is the single declaration for the node and no
new definition or dependency module is needed.
