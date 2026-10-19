## Worker report

The module Sheaf.Algebra.Homology.SubcategoryLeftResolution states
CochainComplex.exists_subcategory_left_resolution, with its sole proof `sorry`.
Read the full node and Stacks derived.tex, lemma-subcategory-left-resolution,
Tag 05T7(1), statement and proof (lines 5302–5384, including the separate part (2)).
Only part (1) is stated, exactly as the item requests. No new notion, dependency
module, or statement correction is needed. No node fault or statement dispute found.

Clause-by-clause correspondence:

- Abelian category A: `{C : Type u} [Category.{v} C] [Abelian C]`.
  Object and morphism universes are separately explicit.
- Subset P of objects: `(P : C → Prop)`, its characteristic predicate.
- P contains a zero object: `hzero : ∃ Z : C, P Z ∧ IsZero Z`.
  This deliberately allows a non-isomorphism-closed class containing a particular
  zero object, without requiring it to contain Mathlib's chosen zero object.
- Every object is a quotient of an element of P: `hcover : ∀ X : C,
  ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p`.
- Integer bound: `(a : ℤ)`; complex: `(K : CochainComplex C ℤ)`.
- K vanishes above a: `hK : ∀ n : ℤ, a < n → IsZero (K.X n)`.
- Existence of a complex and its chain map to K:
  `∃ (L : CochainComplex C ℤ) (f : L ⟶ K)`.
- Quasi-isomorphism: `QuasiIso f`, Mathlib's isomorphism on every cohomology object.
- Every term belongs to P: `∀ n : ℤ, P (L.X n)`.
- Every component is epic: `∀ n : ℤ, Epi (f.f n)`.
- The identical strict upper bound: `∀ n : ℤ, a < n → IsZero (L.X n)`.

Dependency declarations read and used:

- def-sp-abelian: CategoryTheory.Abelian, in
  Mathlib.CategoryTheory.Abelian.Basic (class signature and docstring read).
- def-weil-abstract-derived-category: its recorded module
  Mathlib.Algebra.Homology.DerivedCategory.Basic is publicly imported. The needed
  constituent declarations are CochainComplex (Mathlib.Algebra.Homology.HomologicalComplex)
  and HomologicalComplex.QuasiIso (Mathlib.Algebra.Homology.QuasiIso); their full
  signatures and docstrings were read. No derived category object or localization
  size hypothesis occurs in this statement about complexes.
- Proof dependency lem-sp-abelian-refinements: import
  Mathlib.CategoryTheory.Abelian.Refinements, without `public`. Read
  CategoryTheory.epi_iff_surjective_up_to_refinements,
  CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements, and
  CategoryTheory.Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements.
  These give the refinements used in the seven-step docstring proof.

Edge cases checked mathematically: K zero; K concentrated in degree a (one
cover followed by covers of kernels suffices); arbitrary negative or zero a;
P containing just one selected zero object in a zero category, and P not closed
under isomorphisms or finite sums. The existential zero-object condition handles
the last cases. There is no projective, functorial-cover, or closure hypothesis.
Vanishing means IsZero, the categorical meaning of a zero object, not equality
with a separately chosen representative. All degree quantifiers include every
integer, including the degrees where the terms vanish.

Searches actually run using msearch.py with group NQ and this item:

- LeanFinder: "A bounded above cochain complex admits a termwise epimorphic
  quasi-isomorphism from a complex in any quotient generating class containing a
  zero object". Eight hits: K-projective/K-injective, CM5b, and derived fraction
  or bounded representative results. None allows an arbitrary covering class
  with the required termwise epimorphisms and same upper bound.
- Loogle: `"QuasiIso", "IsStrictlyLE"`. Zero hits.
- LeanSearch: "bounded above cochain complex resolution arbitrary quotient
  generating class termwise epimorphism". Eight hits: component-epi facts,
  projective resolutions, CM5b, and unrelated localization/cochain facts.
  No exact match; CM5b has enough-injectives and opposite boundedness assumptions.
- Mathlib grep: `exists.*[Qq]uasiIso|[Ss]ubcategory|quotient.generat` in
  Algebra/Homology/LeftResolution. One hit, an example of a full subcategory in
  Reduced.lean, with no theorem matching this statement.
- rg in the source WeilConjectures and shared lean/Sheaf trees:
  `left_resolution|leftResolution|subcategory.left.resolution|subcategory-left-resolution`.
  Upstream FromJoel resolutions use functorial left-resolution data; the existing
  LeftResolutionBoundedMinus requires an additive fully faithful inclusion and a
  zero-preserving functorial cover. These are stronger inputs, not this lemma.
  SubcategoryTruncationResolutionSystem cites this item but does not state it.
- grep of the node id in upstream WeilConjectures: no hits. rg of the node id in
  dag/lean_names_upstream.json: no hits. Final-name search
  `exists_subcategory_left_resolution|subcategory_left_resolution` in upstream,
  Mathlib, shared lean/Sheaf, and dag/lean_names_upstream.json: no hits.

## Second reading by NQ

Author's second pass under the dispatcher's direct-delivery protocol; the
maintainer supplies the independent review. Reopened the source statement and
compared each binder and each of the four conclusion clauses above. In particular,
the source assumes a subset containing zero, not a replete additive subcategory:
`hzero` is existential, and there is no isomorphism or biproduct closure binder.
`hcover` is epic onto every ambient object, `hK` is termwise vanishing rather than
cohomological boundedness, and the output requires both QuasiIso and epimorphy
of every component, with exactly the input bound a. There are no missing clauses
or added mathematical assumptions, and no change was needed on this rereading.
Every binder and universe is explicit, and autoImplicit is disabled. The single
sorry has the complete seven-step natural-language proof in its docstring and
matches the existing DAG node. The node copy changes only its lean field.

Validation: scompile.py NQ lem-sfb-subcategory-left-resolution compiled the delivered
module successfully in both sandbox and library contexts, with no errors or
warnings. The node diff is lean-only; every Lean line is at most 100 characters.
