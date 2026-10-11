## Worker report

The module `Sheaf.CategoryTheory.RightDerivedExactComposite` states
`CategoryTheory.Functor.exists_rightDerived_exact_comp_iso`, with `sorry` as its only proof.
It asserts the degreewise canonical isomorphism after an exact functor carrying injectives
to acyclic objects. No definition, new node, dependency replacement, or statement correction
is needed. All writes were in the item sandbox; compilation was on the server.

Hypothesis and conclusion correspondence:

- The three arbitrary abelian categories are the separately universe-polymorphic
  `{A : Type u₁} {B : Type u₂} {C : Type u₃}`, their independently universe-polymorphic
  `Category` instances, and `[Abelian A] [Abelian B] [Abelian C]`.
- Enough injectives in A and B is `[EnoughInjectives A] [EnoughInjectives B]`.
  Mathlib obtains `HasInjectiveResolutions` from these abelian-category hypotheses; no
  enough-injectives hypothesis on C is imposed.
- The functors are `(T : A ⥤ B) (U : B ⥤ C)`. Exactness of T is `[T.Additive]`,
  `[PreservesFiniteLimits T]`, and `[PreservesFiniteColimits T]`. For abelian categories
  this is the standard equivalent formulation of additive exactness: kernels and
  cokernels are preserved, and finite (bi)products are preserved. Left exactness of U
  in the dependency convention is `[U.Additive] [PreservesFiniteLimits U]`, equivalent
  to an additive kernel-preserving functor.
- Every injective image is U-acyclic is
  `hTU : ∀ (I : A), Injective I → U.rightAcyclic (T.obj I)`. The recorded acyclicity
  definition quantifies `IsZero ((U.rightDerived (q + 1)).obj (T.obj I))` for every q,
  exactly all positive degrees. Injective here is Mathlib's extension-along-monos property.
- Every object and nonnegative degree are `(M : A) (i : ℕ)`.
- The isomorphism of derived-functor values is
  `e : ((T ⋙ U).rightDerived i).obj M ≅ (U.rightDerived i).obj (T.obj M)`.
  Lean composition `T ⋙ U` means the paper's U composed with T.
- The word “canonical” is retained, not replaced by mere existence of some abstract iso:
  the existential iso must satisfy the formula for EVERY injective resolution I of M,
  EVERY injective resolution J of T(M), and EVERY chain-map lift φ of the identity.
  The lift condition is `T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0`; since single-zero complexes
  have no other nonzero source degrees, this is exactly commutation over the identity.
  Its formula is I's derived/cohomology identification, the inverse complex-composition
  identification on homology, the homology map of U(φ), and the inverse of J's
  derived/cohomology identification. Thus it is exactly the Leray comparison specified
  in step 3 of the node's proof. These universally quantified resolution/lift data
  describe the conclusion and introduce no extra hypothesis on T, U, M, or i.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`, `Mathlib.CategoryTheory.Abelian.Basic`.
  Read its class and docstring: preadditive, finite products, kernels, cokernels, normal
  monos/epis; zero objects and biproducts follow.
- `def-sp-injective-resolutions`: `CategoryTheory.InjectiveResolution`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`; injectivity is
  `CategoryTheory.Injective` and enough injectives is `CategoryTheory.EnoughInjectives`,
  both in `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
  Read the resolution's N-indexed complex, injective terms, augmentation and quasi-iso fields.
- `def-sp-acyclic`: `CategoryTheory.Functor.rightAcyclic`,
  `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` (the module imported).
  Read its full definition and the acyclic-resolution comparison docstrings.
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.rightDerived` and
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`,
  `Mathlib.CategoryTheory.Abelian.RightDerived`. Read their signatures, definitions and
  docstrings. The supporting classes are `Functor.Additive` and `PreservesFiniteLimits`,
  and the kernel-preservation equivalence is in `Mathlib.CategoryTheory.Preadditive.LeftExact`.
- The formula also uses Mathlib's `Functor.mapHomologicalComplexCompIso` and
  `HomologicalComplex.homologyMap`, rather than duplicating any notion.

Edge cases checked: i = 0 is included (the isomorphism is the ordinary composite
identification under the degree-zero derived identifications); zero objects, T = 0,
T = identity and U = identity satisfy the expected comparison. Higher degrees vanish
when appropriate. Arbitrary unrelated category and morphism universes are allowed.
No nonzero-category, positive-degree, or injective-image-is-injective assumption is added.
The acyclicity hypothesis is essential; the previously reported forgetful/Hom counterexample
fails it. No statement fault or STATEMENT-DISPUTED issue was found.

Searches (2026-10-11):

- `msearch.py ... leanfinder "right derived functor composite exact functor sends injectives
  to acyclic objects"`: eight hits, including Mathlib's `rightDerived`, vanishing on
  injectives and `rightDerived_map_eq`; no composite comparison with these hypotheses.
- `msearch.py ... loogle "Functor.rightDerived, Functor.comp"`: no hits; unknown identifier
  `Functor.rightDerived` in that service.
- `msearch.py ... leansearch "right derived functors composition exact acyclic"`: service
  unavailable (Internal Server Error), recorded without a mathematical verdict.
- `msearch.py ... grep "rightDerived.*[Cc]omp|comp.*rightDerived" CategoryTheory`: 17 hits
  for general localization-derived-functor APIs and natural-transformation composition;
  no matching theorem for the degreewise right-derived convention.
- `rg` in Mathlib's CategoryTheory/Abelian and in project WeilConjectures and lean/Sheaf
  for derived/composite/rightDerived combinations: acyclic-resolution APIs and derived
  category composition APIs found. The latter concern derived-category functors and
  sometimes require preservation of injectives; they are not this degreewise statement.
- Source grep for `lem-sc-ext-derived-composite` found no declaration. The upstream-name
  index has no entry for this node. A full-name grep for
  `exists_rightDerived_exact_comp_iso` in Mathlib, WeilConjectures, lean/Sheaf, and the
  upstream-name index found no existing declaration.

Source checked: Stacks https://stacks.math.columbia.edu/tag/015M, including its proof:
choose an injective resolution, apply the first functor, then apply the acyclic-resolution
comparison (015E). Local literature files are absent on this machine; the published tag
supplied that check. The node specializes the first left exact functor to an exact functor.

Validation: `scompile.py H1 lem-sc-ext-derived-composite` compiled the final module on the
server in 1.4 seconds, with no errors or warnings. The required `deliver2.py --no-push`
dry run printed OK: commit 939fadcc4 compiled and passed preflight except for the
second-reading section, which the tool explicitly reserves for the second reader.
Nothing was pushed. The second reader supplies their own reading.

## Second reading by H1

Independent reading on 2026-10-11; I did not write the statement. I opened the item
node, its proof, all four statement-dependency nodes, the actual dependency declarations,
and the delivered Lean module. Verdict: the Lean says the node's statement, including
its canonical Leray comparison. No mathematical mismatch was found; the module and
node record need no repair. This section and the independent search log are the additions.

Source reading: local literature is absent. I read the Stacks `derived.tex` source at
https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex,
`lemma-compose-derived-functors` (015M, lines 6801–6850), including the preceding section
assumptions and its proof, and Tag 015E at https://stacks.math.columbia.edu/tag/015E.
015M has abelian A, B, C, left exact F and G, enough injectives in A and B, and the
injective-image acyclicity condition. The node takes the exact-first-functor specialization
on an object in degree zero, so RF(M) identifies with T(M). The proof's arrow goes from
G(F(I)) to RG(F(I)); this agrees with the delivered forward map. No hidden Grothendieck,
Noetherian, characteristic, or enough-injectives-in-C assumption occurs here. I also
opened the parent `lem-sc-ext-locally-free` node and read its standard-homological-algebra
step: this general comparison is used with A = B = scheme modules and U = global sections.

Object/hypothesis/conclusion checklist (the node's list, with its Lean and verdict):

1. Three abelian categories A, B, C: `{A : Type u₁} {B : Type u₂} {C : Type u₃}`,
   `[Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]`, and the three `Abelian`
   instances. Exact match; all six universes are explicitly declared and independent.
   I read `Abelian` in Mathlib `CategoryTheory/Abelian/Basic.lean`: preadditivity,
   normal monos/epis, finite products, kernels and cokernels. Its zero object and finite
   biproducts recover the dependency node's formulation.
2. Enough injectives in A and B: `[EnoughInjectives A] [EnoughInjectives B]`.
   Exact match; none is demanded in C. I read `Injective`, `InjectivePresentation`, and
   `EnoughInjectives` in `Preadditive/Injective/Basic.lean`: every object embeds into an
   injective. `HasInjectiveResolutions` is inferred, rather than an extra hypothesis.
3. Exact T from A to B: `(T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
   [PreservesFiniteColimits T]`. Exact match in abelian categories. These mean additive
   preservation of kernels and cokernels, equivalently preservation of short exact
   sequences; they do not impose preservation of arbitrary limits or colimits.
   I read the kernel/finite-limit and cokernel/finite-colimit equivalences in Mathlib
   `Preadditive/LeftExact.lean`, and `Functor.Additive` in `AdditiveFunctor.lean`.
4. Left exact U from B to C: `(U : B ⥤ C) [U.Additive] [PreservesFiniteLimits U]`.
   Exact match with `def-sp-left-exact-additive`'s additive kernel-preserving convention.
   Additivity's map-add formulation is equivalent to finite biproduct preservation here.
5. Every injective image is U-acyclic: `hTU : ∀ (I : A), Injective I →
   U.rightAcyclic (T.obj I)`. Exact match. I read the recorded upstream `rightAcyclic`
   definition: `∀ q : ℕ, IsZero ((U.rightDerived (q + 1)).obj ...)`.
   Thus it requires precisely all positive degrees, and uses the dependency's existing
   definition rather than a private predicate or injectivity of T(I).
6. An arbitrary M and every i ≥ 0: `(M : A) (i : ℕ)`. Exact match, including degree zero.
7. Isomorphism of Rⁱ(U ∘ T)(M) with RⁱU(T(M)): the existential
   `e : ((T ⋙ U).rightDerived i).obj M ≅ (U.rightDerived i).obj (T.obj M)`.
   Exact match; `T ⋙ U` has the required order. I read Mathlib's `rightDerived` and
   `InjectiveResolution.isoRightDerivedObj` in `CategoryTheory/Abelian/RightDerived.lean`.
   They compute the cohomology of the functor applied to an injective resolution, as
   `def-sp-left-exact-additive` prescribes.
8. Canonical comparison: after choosing e, the conclusion quantifies every
   `I : InjectiveResolution M`, `J : InjectiveResolution (T.obj M)`, and complex map
   φ from T(I) to J, subject to `T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0`.
   This is precisely a lift over the identity of T(M); other augmentation components
   have zero sources. I read `InjectiveResolution`'s injective-term and quasi-isomorphism
   fields and its `ι_f_succ` lemma in Mathlib `Preadditive/Injective/Resolution.lean`.
   The formula transports through I's derived/cohomology identification, the inverse of
   `mapHomologicalComplexCompIso`, Hⁱ(U(φ)), and the inverse of J's identification.
   I opened `mapHomologicalComplexCompIso` in Mathlib `Algebra/Homology/Additive.lean`:
   its forward direction is successive application to application of the composite,
   so the delivered inverse has the correct direction. I also read upstream
   `InjectiveResolution.isoRightDerivedObjOfQuasiIso` and
   `Functor.rightDerivedObjIsoOfResolution` in `RightDerived/Acyclic.lean`; their
   displayed comparison agrees with the formula. Exact match with the node's proof
   step 3, which specifies this sense of canonical. These are conclusion quantifiers,
   not added hypotheses, and lifts exist by the injective-resolution comparison.

Edge cases: i = 0 is allowed and computes the ordinary composite under the standard
zero-degree identifications. M = 0 and T = 0 give zero objects; identity T and identity U
have the expected comparison. There is no nonzero-object assumption. There is no family
index set to restrict; ℕ indexes a resolution, not a nonempty family parameter. An empty
abelian category is already excluded by its zero-object axiom, not by an extra Lean binder.
An empty scheme can be used in the parent's application without any new restriction.
No field, ring, prime or characteristic parameter is specialized. Independent object and
morphism universes impose no smallness equality. The condition is acyclicity of all
injective images, not a finiteness or injective-preservation condition.

Independent searches using different terms from the first reader:

- LeanFinder via `msearch.py`: `Grothendieck spectral sequence degenerates exact inner
  functor derived composition comparison`. Eight hits: exact-functor maps on Ext,
  localization derivability-structure lemmas, and vanishing on injectives. No exact match.
- Loogle via `msearch.py`: `"rightDerived", "comp"`. Twelve hits for general
  localization-derived-functor comparisons and natural-transformation composition.
  These do not state this degreewise abelian-category result.
- LeanSearch via `msearch.py`: `cohomology derived functor of composition with exact
  functor acyclic injective images`. Unavailable (Internal Server Error); no mathematical
  verdict is inferred from that failure.
- Independent `rg` on pinned Mathlib's abelian-category sources, all upstream
  `WeilConjectures`, and repository `lean/Sheaf` for `rightDerived.*[Cc]omp`,
  `[Cc]omp.*rightDerived`, and derived/composition variants. The close candidate is
  upstream `Functor.rightDerivedFunctorCompIso` in
  `CategoryTheory/DerivedCategory/RightDerivedFunctor/Comp.lean`. I opened its declaration
  and `PreservesKInjectiveComplexes` class: it concerns total unbounded derived functors
  and assumes preservation of K-injective complexes, not just U-acyclic injective images.
  It is therefore not an existing realization of this node. The acyclic-resolution API
  computes one functor on a resolution, not the two-functor comparison. No matching
  statement was found. Grep of the full proposed name and blueprint id in upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no declaration to reuse.

H5–H9: there are no definitions or local copies, no hollow data, and exactly one theorem
whose proof is `by sorry`. Its module and theorem docstrings cite the source and blueprint
id, and its proof paragraph covers all three node steps with the relevant dependencies.
The single upstream import supplies notions used by the statement. Namespace, filename,
line lengths, explicit variables and universes follow the conventions. There are no new
nodes, dependency modules, or stage-2 statement corrections to review under H12/H13/4c.
The node's `lean.statement` is the unchanged theorem signature verbatim before `:=`.

Validation: independently ran `scompile.py H1 lem-sc-ext-derived-composite` on the
module; compiled on the server in 1.5 seconds, exit code 0, with no warnings or errors.
