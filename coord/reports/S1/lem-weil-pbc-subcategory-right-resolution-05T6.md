## Worker report

The module `lean/Sheaf/Algebra/Homology/SubcategoryRightResolution.lean` states
`CochainComplex.exists_mono_quasiIso_in_subcategory`, Stacks Tag 05T6(1).
Its only proof is `sorry`; no definitions or additional theorems are introduced.
The six-step natural-language proof from the node is included in the theorem docstring,
with the supporting DAG nodes named at each non-elementary step.

Hypothesis and conclusion correspondence:

- An abelian category A: `(C : Type u) [Category.{v} C] [Abelian C]`, with independent,
  explicitly declared object and morphism universes `u v`.
- A subset of its objects: `(𝓘 : Set C)`. This is an arbitrary subset, with no assumption
  of closure under isomorphisms, sums, kernels, or cokernels.
- The subset contains zero: `(hzero : (0 : C) ∈ 𝓘)`, using Mathlib's chosen zero object.
- Every object is a subobject of an element of the subset:
  `(hembed : ∀ X : C, ∃ (Y : C) (f : X ⟶ Y), Y ∈ 𝓘 ∧ Mono f)`.
  Subobject here means an embedding into such an object, exactly as in the source.
- The integer lower bound: `(a : ℤ)`.
- The given cochain complex: `(K : CochainComplex C ℤ)`; the complex structure includes
  the differential-square-zero equations.
- Its terms vanish below the bound: `hK : ∀ n : ℤ, n < a → IsZero (K.X n)`.
  Categorical vanishing uses `IsZero`, as in the landed injective specialization.
- A resulting cochain complex and a morphism of complexes:
  `∃ (I : CochainComplex C ℤ) (α : K ⟶ I)`; the morphism structure includes differential
  commutation, so no arbitrary family is substituted for a chain map.
- A quasi-isomorphism: `QuasiIso α`. Its definition requires all induced cohomology maps
  to be isomorphisms; homology exists automatically in an abelian category.
- Each component is injective: `∀ n : ℤ, Mono (α.f n)`; no injectivity-of-object assumption.
- Each resulting term belongs to the given subset: `∀ n : ℤ, I.X n ∈ 𝓘`.
- The resulting terms vanish below the same bound: `∀ n : ℤ, n < a → IsZero (I.X n)`.

Dependency declarations read and used:

- `def-sp-abelian` is a Mathlib leaf whose match is `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`. Its full class signature and docstring were
  read: preadditivity, normal mono/epi categories, finite products, kernels and cokernels.
  The imported `Mathlib.Algebra.Homology.ShortComplex.Abelian` supplies this class and
  homology existence for all short complexes in C.
- `def-weil-abstract-derived-category` is a Mathlib leaf whose recorded match is
  `DerivedCategory` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`; that declaration
  and its universe/localization assumptions were read. This lemma uses its underlying
  notions of complexes and quasi-isomorphisms, not localization, so imports the defining
  `Mathlib.Algebra.Homology.QuasiIso` instead of requiring a derived-category choice.
  `CochainComplex` in `Mathlib.Algebra.Homology.HomologicalComplex` and `QuasiIso` in
  `Mathlib.Algebra.Homology.QuasiIso` were read with their full signatures and docstrings.
  Neither dependency needs a replacement module.

Edge cases checked: all integer bounds, including zero and negative values, are included;
vanishing means categorical zero without a literal-object equality requirement. A zero
complex can be resolved by the complex whose objects are the chosen zero, available by
`hzero`. The empty subset is ruled out by the source's zero-membership requirement.
The subset consisting only of zero can satisfy `hembed` only in a category where every
object is zero, and the conclusion then holds. For a non-replete subset, actual membership
of every output term is required; vanishing is not used to silently infer membership.
For the full subset the identity resolution works. The subset of injective objects with
enough injectives gives the existing bounded-below injective specialization, retaining
exactly the bound a. No additional size, enough-injectives, or derived-category assumption
is imposed.

Searches (all performed for this item):

- `msearch.py leanfinder`: "A bounded below cochain complex admits a termwise monomorphic
  quasi-isomorphism into a complex in any class containing zero into which all objects
  embed". Eight hits, including `CochainComplex.cm5b`, K-injectivity and its injective
  term lemmas. None states the arbitrary-subset assertion.
- `msearch.py loogle`: "CochainComplex, QuasiIso, Mono". No hits; service reports unknown
  identifier `Mono` in the unqualified query.
- `msearch.py grep`: "exists.*quasiIso|subcategory.*resolution|exists_mono_quasiIso"
  in `Algebra/Homology`. Ten hits; the candidates in CM5a and
  DerivedCategory/DerivabilityStructureInjectives assume enough injectives and restrict
  the terms to injectives. The full signatures of CM5a's two candidate lemmas were read:
  the monomorphic version loses one degree in the bound, while the version keeping the
  bound does not assert monomorphic components. Neither is this statement.
- `rg` in the source project, the project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `subcategory.*resolution|exists_mono_quasiIso|right_resolution`: the landed
  `BoundedBelowInjectiveResolutionMono.lean` is the injective specialization and cites
  this item; the source hit concerns functorial localized equivalences, not this theorem.
- `grep -rn` for the exact item id in source `WeilConjectures`: no hits.
- `rg` for `exists_mono_quasiIso_in_subcategory|SubcategoryRightResolution` in Mathlib,
  source, project's Lean, and the upstream-name index: no hits, so the new name is free.

The named local Stacks TeX file is not present on this machine. The primary source was
therefore opened directly at https://stacks.math.columbia.edu/tag/05T6: part (1) has
exactly the given hypotheses and conclusions, and the proof refers to the dual of 05T7.
No node fault or disputed statement was found; no statement correction or new node is
needed. Server compilation passed cleanly (1.1 s), after enabling Mathlib’s scoped `ZeroObject`
instance for the chosen-zero notation. The delivery dry run is checked before READY;
its expected second-reading omission is left to the independent reader.

## Second reading by S1

I reread the node's statement against the Lean declaration and the Stacks source (Tag 05T6(1)). The correspondence is exact:

- The abelian category is rendered by `(C : Type u) [Category.{v} C] [Abelian C]`; no size, Noetherian, or other extra hypothesis is added.
- The object subset is `(𝓘 : Set C)`, with the required zero-membership hypothesis `hzero : (0 : C) ∈ 𝓘`.
- “Every object is a subobject of an element” is exactly `hembed : ∀ X, ∃ Y f, Y ∈ 𝓘 ∧ Mono f`.
- The integer bound and complex are `(a : ℤ)` and `(K : CochainComplex C ℤ)`.
- Bounded-below terms are exactly `hK : ∀ n, n < a → IsZero (K.X n)`.
- The conclusion introduces `I : CochainComplex C ℤ` and a complex morphism `α : K ⟶ I`; `QuasiIso α` expresses isomorphisms on every cohomology object, and `∀ n, Mono (α.f n)` gives the termwise injections.
- Membership `∀ n, I.X n ∈ 𝓘` and the same lower-bound vanishing `∀ n, n < a → IsZero (I.X n)` are both present, in the same quantifier order.

The empty subset is excluded by `hzero`; zero and zero-complex cases are covered by the chosen zero object and `hK`; all integer bounds, including `a = 0` and negative values, are allowed. No universe restriction excludes a case from the source. The subset need not be replete, and the conclusion correctly requires literal membership of each resulting term.

I searched Mathlib, `WeilConjectures`, `lean/Sheaf`, and the upstream-name index using LeanFinder/Loogle/grep queries for subcategory resolutions and monomorphic quasi-isomorphisms. Only injective-object specializations were found; no existing declaration states this arbitrary-subset result. The module therefore remains a new declaration.

No mismatch was found and no repair was needed. The module compiles cleanly with `scompile.py`; its only proof is the permitted named theorem `sorry`, and the docstrings cite the source and blueprint node.
