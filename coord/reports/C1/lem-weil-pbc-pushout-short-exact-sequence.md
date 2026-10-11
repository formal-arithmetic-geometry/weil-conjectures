## Worker report

The module `Sheaf.CategoryTheory.PushoutShortExactSequence` states
`CategoryTheory.pushout_short_exact_sequence`, with its sole proof `sorry`.
No new definition, dependency module, or statement correction is needed.

Hypotheses and clauses, matched with the node:

- An arbitrary abelian category is `{𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]`.
  Object and morphism universes are explicit and independent. No extra finite-limit,
  finite-colimit, or biproduct hypothesis is imposed; these follow from `Abelian`.
- The given sequence is `S : ShortComplex 𝒜`, `hS : S.ShortExact`.
  Its objects `S.X₁`, `S.X₂`, `S.X₃` are A, B, C; maps `S.f`, `S.g` are f, g.
  `ShortComplex` includes `f ≫ g = 0`; `ShortExact` means exactness, monic f, epic g.
- Any object I and morphism from A to I are `{I : 𝒜} (u : S.X₁ ⟶ I)`.
  Neither injectivity of I nor monicity of u is assumed.
- E and its canonical maps are Mathlib's chosen `pushout u S.f`,
  `pushout.inl u S.f : I ⟶ E`, and `pushout.inr u S.f : B ⟶ E`.
  This is literally `colimit (span u S.f)`; abelian finite colimits provide its
  `HasPushout` instance. The displayed equation `u ≫ inl = S.f ≫ inr` gives the
  required square, with diagrammatic composition.
- The parenthetical description as Coker((u,-f)) is the first conjunct:
  `∃ e : pushout u S.f ≅ cokernel (biprod.lift u (-S.f))`, with both equations
  identifying the inclusions with `biprod.inl ≫ cokernel.π` and
  `biprod.inr ≫ cokernel.π`. Thus it identifies the pushout with the quotient
  compatibly with its structure maps, not merely the underlying object.
- Existence and the characterizing equations for p are `∃ p : E ⟶ S.X₃`,
  `inr ≫ p = S.g ∧ inl ≫ p = 0`. The following `∀ q` clause asserts uniqueness
  among all morphisms satisfying those two equations, independently of exactness.
- The pushed-out short exact sequence is
  `∃ hz : inl ≫ p = 0, (ShortComplex.mk inl p hz).ShortExact`.
  `hz` binds the proof needed to type the short complex; it adds no mathematical
  hypothesis. No unnamed sorry is used for this proof.
- The morphism of short exact sequences is `∃ m : S ⟶ ShortComplex.mk inl p hz`
  with `m.τ₁ = u`, `m.τ₂ = inr`, and `m.τ₃ = 𝟙 S.X₃`.
  Mathlib's `ShortComplex.Hom` carries both required commuting squares.

Dependency declarations read and used:

- `def-sp-abelian` has the Mathlib match `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`: its full class extends `Preadditive`,
  normal-mono and normal-epi categories, and supplies finite products, kernels,
  and cokernels. This is the node's abelian-category notion, with zero objects
  and biproducts consequences in the same file. `Abelian.hasFiniteBiproducts`
  is enabled locally, and `Abelian.hasPushouts` supplies the chosen pushout.
- `def-weil-pbc-category-colimit` records `CategoryTheory.Limits.colimit`,
  `Mathlib.CategoryTheory.Limits.HasLimits`, with Cocone, IsColimit, desc, and
  IsFiltered. Their full signatures and docstrings were read. Here its specific
  diagram is `span u S.f`, and the existing `pushout` abbreviation is that colimit.
  The dependency's filtered-colimit clause is not relevant to a pushout.
- Supporting Mathlib structures are `ShortComplex`, `ShortComplex.Hom`,
  `ShortComplex.ShortExact`, `biprod.lift`, and `cokernel`/`cokernel.π`; none is
  duplicated. Both imports are used by the statement.

Edge cases checked mathematically before writing:

- If I is zero, E is the cokernel of f and hence isomorphic to C; the result
  becomes `0 → 0 → C → C → 0` with its expected projection.
- If u is zero, E is I ⊞ C and the resulting extension splits; no monicity of u
  is needed. If u is the identity, the pushout recovers the original extension.
- If A, B, C are all zero, E is isomorphic to I, the first map is an isomorphism,
  and the resulting sequence is short exact. If C is zero, f is an isomorphism
  and the same conclusion applies.
- No set of indices, characteristic assumption, ring, or scheme is involved.
  The zero category is allowed, and independent object/hom universes exclude
  no abelian category. Choosing the standard pushout loses no case: any pushout
  is uniquely isomorphic compatibly with its inclusions by the colimit property.

Searches (2026-10-11):

- `msearch.py ... leansearch "pushout short exact sequence extension abelian category"`:
  unavailable, Internal Server Error (no mathematical verdict from this service).
- `msearch.py ... leanfinder "pushout of a short exact sequence along a morphism
  from its first object is short exact"`: eight hits, principally
  `IsPushout.exact_shortComplex` and `ShortComplex.SnakeInput` declarations.
  The former concerns the square's complex A → I ⊞ B → E, not the extension
  I → E → C with unique projection and cokernel description.
- `msearch.py ... loogle "CategoryTheory.IsPushout,
  CategoryTheory.ShortComplex.ShortExact"`: no hits.
- `msearch.py ... grep "pushout|ShortExact" CategoryTheory/Abelian`: 25 hits
  covering existing ingredients, no declaration of the whole result.
- `rg` of pushout/ShortExact and the item's id in `WeilConjectures/` and
  `lean/Sheaf/`: no upstream match; landed torsor-pushout and Yoneda modules
  are specializations, not the result for every abelian category. The torsor
  module cites this item in its proof. Searches for the chosen declaration
  name in `dag/lean_names_upstream.json`, both project trees, found no collision.

Source reading: the local literature checkout has no stacks-project directory,
so the cited source was read at the authoritative Stacks pages:
https://stacks.math.columbia.edu/tag/010I (item (2)),
https://stacks.math.columbia.edu/tag/05PJ (part (2)),
https://stacks.math.columbia.edu/tag/08N4 (part (2)), and
https://stacks.math.columbia.edu/tag/08N3 (part (2)).
These confirm the pushout extension, quotient description, monicity, and
cokernel identification. The declaration docstring includes all six proof
steps from the node. No statement dispute or node fault was found.

## Second reading by C1

Read the item's complete node, its six proof steps, the delivered Lean, both
statement dependencies, and the actual Mathlib signatures. No statement correction,
new definition node, or dependency module is present or needed.

Independent source reading: the local literature directory contains no Stacks
checkout. Read the authoritative homology.tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/homology.tex
(the scratchpad copy is not delivered), especially lines 701–715, 852–917,
and 1260–1356, as well as the tag pages
[010I](https://stacks.math.columbia.edu/tag/010I),
[05PJ](https://stacks.math.columbia.edu/tag/05PJ),
[08N4](https://stacks.math.columbia.edu/tag/08N4), and
[08N3](https://stacks.math.columbia.edu/tag/08N3).
010I item (2) assumes an abelian category, an extension, and an arbitrary map
from its first object. No injectivity, enough injectives, or smallness assumption
on the category is needed for this construction. The discussion of Ext as a set
is separate from constructing the pushout extension. 05PJ (2) supplies exactly
the signed cokernel description; 08N4 (2), with the square flipped, supplies
monicity of iota; 08N3 (2) supplies the cokernel identification.

Object/hypothesis/conclusion inventory and H3 verdicts:

1. Abelian category A: `{𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]`.
   PASS. Read `def-sp-abelian` (sec-abelian-varieties) and its Mathlib match
   `CategoryTheory.Abelian` at Basic.lean:112. The class requires preadditivity,
   normal monos/epis, finite products, kernels, and cokernels; zero objects and
   finite biproducts are consequences, so this is precisely the node's notion.
   No additional category structure is assumed. The local finite-biproduct
   instance is the theorem `Abelian.hasFiniteBiproducts`, not a new hypothesis.
2. Objects A, B, C and arrows f, g forming a short exact sequence:
   `(S : ShortComplex 𝒜) (hS : S.ShortExact)` with `S.X₁`, `S.X₂`, `S.X₃`,
   `S.f`, `S.g`. PASS. Read ShortComplex.Basic:34–66 and ShortExact:35–39:
   `S.zero` is f ≫ g = 0; ShortExact contains exactness, Mono f and Epi g.
   The endpoint zeros are therefore represented without losing any condition.
3. Object I and arbitrary map u from A: `{I : 𝒜} (u : S.X₁ ⟶ I)`.
   PASS. No Mono u or Injective I instance is required.
4. E is the pushout I amalg_A B, with canonical iota and v:
   `pushout u S.f`, `pushout.inl u S.f`, `pushout.inr u S.f`.
   PASS. Read `def-weil-pbc-category-colimit` and its existing colimit record,
   HasLimits.lean:175–191 and HasPullback.lean:90–156. Pushout is literally
   `colimit (span u S.f)`; its inclusions are the colimit coprojections and its
   desc is `colimit.desc`. `Abelian.hasPushouts` supplies existence from the
   stated category structure. A chosen pushout represents every pushout up
   to its canonical isomorphism; no extra object assumption is introduced.
5. Parenthetical E = Coker((u,-f): A → I ⊕ B): the first conjunct existentially
   gives `e : pushout u S.f ≅ cokernel (biprod.lift u (-S.f))` and identifies
   each inclusion with `biprod.inl`/`biprod.inr` followed by `cokernel.π`.
   PASS. The sign, summand order, and map compatibility agree with 05PJ (2)
   and node proof Step 2; this is not merely an abstract object isomorphism.
6. Commuting square iota ∘ u = v ∘ f:
   `u ≫ pushout.inl u S.f = S.f ≫ pushout.inr u S.f`.
   PASS. Lean uses diagrammatic composition, reversing the written ∘ order.
7. Existence of p: `∃ p : pushout u S.f ⟶ S.X₃` with
   `pushout.inr u S.f ≫ p = S.g` and `pushout.inl u S.f ≫ p = 0`.
   PASS. Both equations concern the same p and the original quotient C.
8. Uniqueness of p: `∀ q : pushout u S.f ⟶ S.X₃`, the same two equations
   imply `q = p`. PASS. Uniqueness ranges over all maps satisfying the
   characterizing composites, without imposing short exactness on q.
9. The resulting sequence is short exact: `∃ hz : inl ≫ p = 0`, followed
   by `(ShortComplex.mk inl p hz).ShortExact`.
   PASS. The existential hz is a proof of the already asserted zero composite,
   needed to form a ShortComplex; it adds no assumption and no data-level hole.
10. Morphism of the original sequence to the resulting sequence:
    `∃ m : S ⟶ ShortComplex.mk inl p hz`, with
    `m.τ₁ = u ∧ m.τ₂ = pushout.inr u S.f ∧ m.τ₃ = 𝟙 S.X₃`.
    PASS. The read ShortComplex.Hom signature includes both commuting squares;
    the three components are exactly (u,v,id_C). The p, hz, and second sequence
    are shared with the exactness conclusion, in the required quantifier order.

Edge cases: I = 0 gives the original cokernel C; u = 0 gives I ⊞ C and a split
extension; u = id recovers the original extension; A = 0 already has B ≅ C
and gives I ⊞ B; C = 0 has f an isomorphism and E ≅ I; A = B = C = 0 also
gives E ≅ I. The zero category is allowed. Universes u and v are bound and
independent, including small and large abelian categories. There is no index
set, scheme, integer n, or characteristic to restrict. No Nonempty or
finiteness assumption occurs beyond the finite limits/colimits intrinsic to
an abelian category.

Independent H4 searches used different words from the first reader:

- LeanSearch: `cocartesian square induces extension with same cokernel in abelian
  category` — service unavailable (Internal Server Error); no verdict inferred.
- LeanFinder: `cobase change of an extension preserves exactness with quotient
  fixed` — eight results about exactness under module quotients, cotangent
  base change, and the module snake lemma. None states this categorical result.
- Loogle: `CategoryTheory.ShortComplex.ShortExact, CategoryTheory.Limits.pushout`
  — zero results.
- rg for `cobase|push.?out|cocartesian` in Mathlib's ShortComplex and Abelian
  trees, and in WeilConjectures and this project's lean/Sheaf. Opened
  Abelian.CommSq's `IsPushout.exact_shortComplex`: its sequence is
  A → I ⊞ B → E, a different sequence. Opened Basic's
  `BiproductToPushoutIsCokernel.isColimitBiproductToPushout`: it supplies the
  cokernel-description ingredient, not the unique projection to C and the
  pushed-out extension. Opened the landed `etale_pushout_extension` and
  `exists_injective_resolution_ses_complexes`: these specialize or use this
  result, with additional torsor/resolution structures, and do not duplicate it.
  No whole-statement match exists in the inspected results.
- rg for `pushout_short_exact_sequence` in dag/lean_names_upstream.json,
  WeilConjectures, and lean/Sheaf: no name collision.

H5–H10: no definitions or data-valued sorries; the single theorem's proof is
`by sorry`, with nothing proved. The module and declaration docstrings name
the source places and blueprint ID. The six natural-language proof steps
match the node, but they omitted explicit DAG dependency IDs. Repaired that
H8 documentation gap by adding the cited IDs to Steps 1–6, preserving the
mathematical argument and the theorem signature verbatim. No other mismatch
was found and no node field was changed. All imports are used; the namespace,
file path, bound variables, and universes follow the conventions. Wrapped
all edited lines to at most 100 characters. The node's lean.statement agrees
verbatim with the signature before :=.

Validation: server single-file compile and deliver2 dry-run preflight are run
after these repairs; delivery requires both to pass without non-sorry warnings.
