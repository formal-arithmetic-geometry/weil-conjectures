## Worker report

The module `lean/Sheaf/Algebra/Homology/PreciseVanishing.lean` states
`CategoryTheory.precise_vanishing`.  It uses Mathlib's arbitrary abelian category
`A`, a cochain complex `P` and a complex `K` indexed by `ℤ`, and the localization
functor `DerivedCategory.Q` from the dependency node.

The node's hypotheses render as follows.  Boundedness of `P` is
`∃ a b : ℤ, (∀ i, i < a → IsZero (P.X i)) ∧ (∀ i, b < i → IsZero (P.X i))`.
Termwise projectivity is `∀ i, Projective (P.X i)`.  Truncation below `n` is
`∀ i, i < n → IsZero (P.X i)`.  Vanishing of the cohomology of `K` in degrees at
least `n` is `∀ i, n ≤ i → IsZero (K.homology i)`.  The conclusion is
`∀ f : (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K), f = 0`, exactly the
assertion that every derived morphism is zero.

The dependency declaration is `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
`CategoryTheory.DerivedCategory` and its `Q` functor (recorded by
`def-weil-abstract-derived-category`).  The theorem proof is `sorry`, as required
for stage 2.

Edge cases checked: `n` is an arbitrary integer; the bounds may be any integers,
including empty ranges; `P` and `K` may be zero complexes; and no nonempty-index,
positivity, or characteristic assumptions are introduced.

Searches made: the node's recorded LeanFinder, Loogle, grep, and LeanSearch
searches were read; LeanFinder found only general derived-category declarations,
Loogle had no matching identifier, grep found no exact precise-vanishing theorem,
and LeanSearch was unavailable.  `rg` over the project source and existing
`lean/Sheaf` found no declaration for this node.  Mathlib's `DerivedCategory.Q`,
`CochainComplex`, `Projective`, `IsZero`, and `homology` were used directly.

## Earlier second reading (a previous round; superseded)

Reading the node and module independently, every hypothesis and conclusion is
present with the same objects and integer inequalities.  The only proof content
is `sorry`; no claim is proved or weakened.  The Mathlib localization object
`DerivedCategory.Q.obj P` is the recorded `Q(P)` of the node.


## Second reading by G1

I independently read the node, its dependency node, the delivered Lean, and
Stacks `derived.tex`, section `section-projective-resolutions` and lemma
`lemma-precise-vanishing` (Tag 064D). The local repository has no Stacks checkout;
I read the upstream raw TeX, saved as `derived-source.tex` in this sandbox.
The section imposes no extra enough-projectives, smallness, or ring hypothesis.
The source also records homotopy-category vanishing; this node selects the
stated derived-category vanishing, with comparison in its proof. The Lean
renders exactly that node, without adding the homotopy clause as a conclusion.

Object, hypothesis, and conclusion checklist:

- Arbitrary abelian category A: `(A : Type u) [Category.{v} A] [Abelian A]`.
  Correct: neither module categories nor enough projectives are assumed.
- Complexes P and K: `(P K : CochainComplex A ℤ)`. Correct: Mathlib's
  `CochainComplex` is the homological-complex shape `up`, indexed by all integers.
- Integer n: `(n : ℤ)`. Correct; no positivity restriction.
- P is bounded: `hPbounded : ∃ a b : ℤ, (∀ i, i < a → IsZero (P.X i)) ∧
  (∀ i, b < i → IsZero (P.X i))`. Correct: actual terms vanish outside a finite
  interval; it is not merely cohomological boundedness.
- Each term is projective: `hPprojective : ∀ i : ℤ, Projective (P.X i)`.
  Correct: Mathlib `Projective` in Preadditive/Projective/Basic.lean:48 is the
  lifting property for epimorphisms, not a global enough-projectives assumption.
- Terms below n vanish: `hPtruncated : ∀ i : ℤ, i < n → IsZero (P.X i)`.
  Correct: the inequality is strict and concerns terms, not cohomology.
- Target cohomology at and above n vanishes:
  `hKvanishing : ∀ i : ℤ, n ≤ i → IsZero (K.homology i)`. Correct: the boundary
  degree is included. ShortComplex/HomologicalComplex.lean:90 defines this as
  the homology of the short complex, hence the required kernel/image quotient.
- Q and D(A): `DerivedCategory.Q.obj P` and `DerivedCategory.Q.obj K`.
  Correct: I opened the recorded dependency `def-weil-abstract-derived-category`
  and Mathlib DerivedCategory/Basic.lean:74-98. `DerivedCategory` is the
  localization at quasi-isomorphisms, and Q its functor, exactly as that node.
- Every derived morphism is zero: `∀ f : (DerivedCategory.Q.obj P ⟶
  DerivedCategory.Q.obj K), f = 0`. Correct: universal quantification comes after
  the objects and hypotheses; this is the vanishing of the entire Hom group.
- Universe choice: `universe u v w` and `[HasDerivedCategory.{w} A]`.
  Correct: this chooses the localization and its Hom universe as in the
  dependency node's size convention. Basic.lean:81 supplies the standard choice
  at `w = max u v` for every abelian category; this is not a mathematical
  finiteness or smallness restriction. All variables and universes are bound.

Edge cases: n may be negative, zero, or positive, and the equality degree n is
covered by the target hypothesis. The zero complex and zero abelian category
are allowed. Bounds are arbitrary integers with no imposed ordering, allowing
empty support. There is no separate indexing family requiring nonemptiness;
the index type ℤ is exactly the source's. No scheme, field, ring, characteristic,
or nonempty-scheme assumption occurs; those specializations are unrestricted.
`IsZero` expresses categorical zero objects up to isomorphism, as required in
an arbitrary abelian category.

Independent searches (not just the first worker's recorded searches):

- `msearch.py ... leanfinder` with "Derived morphisms vanish when the source is
  a bounded projective cochain complex supported in degrees at least n and
  target cohomology is supported below n" returned eight candidates. I opened
  `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective` in
  Ext/EnoughProjectives.lean:71: its source is a single projective object, and
  its target is strictly termwise bounded. It is not the node's theorem.
- The same search returned
  `DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`.
  I opened Fractions.lean:163: its source is bounded above and target below,
  the reverse direction, and both bounds concern terms. It is not this theorem.
  Other hits concern the t-structure or K-projectivity, not this vanishing.
- `msearch.py ... leansearch` with "No morphisms from bounded projective
  complexes concentrated above n to complexes with cohomology below n in the
  derived category" returned Internal Server Error, recorded as unavailable.
- `msearch.py ... grep 'from.*eq_zero|to.*eq_zero|IsStrictlyGE|IsStrictlyLE'
  Algebra/Homology/DerivedCategory` found the candidates just discussed, not
  an exact declaration. Direct `rg` for precise vanishing, truncated projective,
  projective vanishing, and comparison names in Mathlib, WeilConjectures, and
  the project's `lean/Sheaf` found no duplicate. The project contains a use in
  DerivedSplittingUnique.lean, not a declaration of this theorem. Searches of
  `dag/lean_names_upstream.json` and those source trees found no collision for
  either spelling of the delivered declaration name.

Mismatches repaired: H8, the old proof docstring only listed tools and did not
carry the node's proof. It now spells out all three steps, truncations, the two
vanishings, exactness, and the comparison, naming every proof dependency. H9,
added the standard copyright/license header and changed the theorem name to
Mathlib's snake-case `CategoryTheory.precise_vanishing`, updating the node's
`lean.declaration`, verbatim `lean.statement`, and worker-report reference.
The mathematical signature is unchanged. There are no new definition nodes,
no dependency modules, and no statement correction to review. No definition
is introduced, and the only proof is the required `sorry`.
