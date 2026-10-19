## Worker report

Record an existing upstream declaration; no new Lean module is needed:
`DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi`
in `WeilConjectures.CategoryTheory.DerivedCategory.FlatModelOfClass`, lines 72–124.
Read its full statement, docstring and proof, and the definitions it uses.
The node itself names precisely this source declaration. Only the item's `lean`
field changes; its old record named the theorem but omitted the complete interface.

Specialize the theorem's category `C` to
`Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` for `X : Scheme.{u}`,
`Λ : Type (u + 1)` and `[CommRing Λ]`. This is the module-valued sheaf encoding
explicitly authorized by def-weil-pbc-etale-sheaves. The ambient structures
`Abelian`, `IsGrothendieckAbelian`, `MonoidalCategory`, `MonoidalPreadditive`,
`MonoidalClosed`, `BraidedCategory`, `HasDerivedCategory` and
`Abelian.HasFunctorialFlatResolution` are provided on this category; they are
not extra mathematical hypotheses on X or Λ. The sheaf monoidal structure is
locally activated as explained in the recorded derived-tensor module.
`GrothendieckAbelian.Sheaf` supplies the Grothendieck instance and
`GrothendieckAbelian.Monoidal.FlatResolution` supplies flat resolutions via
flat separators and sheafified free Yoneda sheaves. The existing étale
`Derived.Finiteness.FlatModel` module also applies this exact generic theorem
to this exact category (lines 199 onward).

Hypothesis-by-hypothesis match:

- The properties S,T are `{S T : ObjectProperty C}`.
- Zero in T and closure under isomorphisms, kernels and cokernels are
  `[T.ContainsZero]`, `[T.IsClosedUnderIsomorphisms]`,
  `[T.IsClosedUnderKernels]`, `[T.IsClosedUnderCokernels]`.
- Zero in S and closure under isomorphisms are `[S.ContainsZero]` and
  `[S.IsClosedUnderIsomorphisms]`.
- Closure of S under binary biproducts is
  `hS : ∀ X Y, S X → S Y → S (X ⊞ Y)`.
- Every S-object belongs to T and is flat are `hST : S ≤ T` and
  `hSf : S ≤ ObjectProperty.flat`.
  `ObjectProperty.flat` requires exact tensoring on both sides; the braiding
  identifies these, so this is equivalent to the node's exactness of F tensor -.
- Lifting is `hlift : ChainComplex.LiftsAlongEpi S T`. Its definition quantifies
  over every `p : A ⟶ B` with `[Epi p]`, every `g : G ⟶ B`, and `T G`, and
  returns `E,e,h` with `S E ∧ Epi e ∧ h ≫ p = e ≫ g`. Lean composition order
  gives exactly the node's p∘h = g∘e.
- The integers and derived object are `{a b : ℤ} {K : DerivedCategory C}`.
- Every cohomology object lies in T is
  `hKT : ∀ n, T ((homologyFunctor C n).obj K)`.
- The vanishing for every sheaf F and every degree outside [a,b] is
  `hK : torAmplitudeIn C a b K`. Its definition is
  `∀ F : C, homologyConcentratedIn a b (K ⊗ (singleFunctor C 0).obj F)`;
  `homologyConcentratedIn` is the conjunction of the canonical t-structure
  lower and upper bounds, equivalently vanishing in those degrees. The monoidal
  structure here is the same unbounded K-flat derived tensor as
  `AlgebraicGeometry.Etale.derivedTensor`, whose body is `curriedTensor _`.

Conclusion-by-conclusion match:

- `∃ (P : CochainComplex C ℤ)` supplies the cochain complex.
- `P.IsStrictlyGE a` and `P.IsStrictlyLE b` say its terms are zero below a and
  above b. Here zero means a zero object, as appropriate in an abelian category.
- `∀ n, ObjectProperty.flat (P.X n) ∧ T (P.X n)` says every term is flat and in T.
- `Nonempty (Q.obj P ≅ K)` is exactly existence of the requested isomorphism.

Dependency declarations read and used in interpreting the specialization:

- def-weil-pbc-etale-site: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
- def-weil-pbc-etale-sheaves: `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
  (read using `scompile.py --source` because it is missing in the older checkout),
  and its recorded `CategoryTheory.Sheaf`; the latter is the full subcategory
  of presheaves satisfying `Presheaf.IsSheaf` in
  `Mathlib.CategoryTheory.Sites.Sheaf`. This node's note expressly provides the
  `Sheaf ... (ModuleCat Λ)` encoding used here; its locally constant predicates
  and torsion predicates are not additional hypotheses of this item.
- def-weil-abstract-derived-category:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; cohomology is
  `DerivedCategory.homologyFunctor` in the sibling `HomologySequence` module.
- def-kun-derived-tensor: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`; full definition and docstring read.

Edge cases: no `a ≤ b` is assumed or added. If a>b, tensoring with the unit
forces K to be zero; the zero complex meets the conclusion since T contains
zero and zero is flat. If a=b there is a single possibly nonzero flat T-term.
The zero object, zero coefficient ring and empty scheme require no exclusions.
No Noetherian, finiteness of Λ, or separate boundedness hypothesis is required.
Closure of T under extensions is not assumed, and the theorem does not add it.
No statement correction or disputed assertion was found.

Searches made with `msearch.py ND lem-sf-flat-model-class-resolution`:

- LeanFinder: "bounded flat model of Tor amplitude with terms in a class lifting
  epimorphisms" returned eight generic derived-category support/truncation
  declarations, no lifting-class theorem.
- Loogle: `DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi`
  returned unknown identifier (upstream theorem is not indexed in Mathlib).
- Mathlib grep: `LiftsAlongEpi|torAmplitudeIn` returned zero hits.
- LeanSearch: "bounded flat model Tor amplitude class lifting epimorphisms"
  was unavailable (Internal Server Error); no negative verdict inferred.
- `rg` of upstream `WeilConjectures` for the full declaration name,
  `def torAmplitudeIn`, `def LiftsAlongEpi` found this exact theorem,
  its definitions and its actual étale specialization caller.
- `rg` of upstream for the node id found no blueprint-tag occurrence.
- `rg` of `lean/Sheaf` for `flat_model|FlatModelOfClass|LiftsAlongEpi`
  found other flat-model material, no duplicate of this theorem.

Validation: the required dry run checks the existing declaration by compiling
an import and `#check @DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi`
through `scompile.py`, then runs server preflight. No proof or duplicate module
is delivered. The independent second reading is left to the next worker.

## Second reading by ND

Independent reading of the node copy, its four statement dependencies and the
complete source theorem (including its section binders and proof). Verdict:
retain the existing declaration; no mathematical or Lean-record repair is needed.
Only this review section is added. There are no new nodes or dependency modules.

The node's source is FlatModelOfClass.lean, lines 72–124, specialized to
small-etale module-valued sheaves. I also read the local Stacks TeX at
cohomology.tex, lemma-tor-amplitude (08CI), and more-algebra.tex,
lemma-tor-amplitude (0654). The former assumes a ringed space and a ≤ b;
the latter allows arbitrary integers. Neither asserts the lifting-class
refinement. The explicitly named upstream theorem is the source of that
refinement and allows arbitrary a,b, as the node correctly states. Its ambient
section asks for an abelian Grothendieck braided closed monoidal category with
monoidal preadditivity, a derived category and functorial flat resolutions.
These structures are available for the specified sheaf category; they impose
no extra condition on the scheme or commutative coefficient ring.

Object/hypothesis/conclusion checklist, in node order:

1. Arbitrary scheme X, commutative ring Λ, and its module-valued small-etale
   sheaf category: specialize `C` to
   `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` with
   `X : Scheme.{u}`, `Λ : Type (u + 1)`, `[CommRing Λ]`. PASS.
   I read `Scheme.Etale`/`smallEtaleTopology`, the sheaf full-subcategory
   definition in Mathlib Sites.Sheaf, and the dependency records. In particular
   def-weil-pbc-etale-sheaves explicitly authorizes this ModuleCat encoding;
   its set-sheaf predicates are not substituted for module sheaves.
2. Usual tensor, derived category, localization Q and K-flat derived tensor:
   `MonoidalCategory C`, `DerivedCategory C`, `DerivedCategory.Q` and the
   derived monoidal structure used by `torAmplitudeIn`. PASS.
   I read Basic.lean's localization definitions, HomologySequence.lean's
   `homologyFunctor` and factorization through Q, and the recorded
   `AlgebraicGeometry.Etale.derivedTensor`, whose body is `curriedTensor _`.
   These are the dependency notions, not alternative tensor constructions.
3. Flat means exact F tensor -: `ObjectProperty.flat F` is exact tensoring
   on both sides, as read in FromJoel/CategoryTheory/Abelian/Flat/Basic.lean.
   The braiding identifies the two functors, so this is equivalent to the
   node's condition, not an additional flatness assumption. PASS.
4. Properties S,T: `{S T : ObjectProperty C}`. PASS.
5. T contains zero and is closed under isomorphisms, kernels and cokernels:
   `[T.ContainsZero]`, `[T.IsClosedUnderIsomorphisms]`,
   `[T.IsClosedUnderKernels]`, `[T.IsClosedUnderCokernels]`. PASS.
   There is no extra extension-closure assumption.
6. S contains zero and is closed under isomorphisms and binary biproducts:
   `[S.ContainsZero]`, `[S.IsClosedUnderIsomorphisms]`, and
   `hS : ∀ X Y, S X → S Y → S (X ⊞ Y)`. PASS.
7. Every S-object is flat and belongs to T: `hSf : S ≤ ObjectProperty.flat`
   and `hST : S ≤ T`. PASS.
8. Lifting every epimorphism p along every g from a T-object:
   `hlift : ChainComplex.LiftsAlongEpi S T`. PASS. I opened
   Algebra/Homology/ResolutionByClass.lean:58: its definition quantifies
   over all A,B,G,p,[Epi p],g,T G and returns E,e,h with S E, Epi e,
   and `h ≫ p = e ≫ g`, precisely p∘h = g∘e. No projectivity or
   epimorphism condition on g is added.
9. Integers a,b and derived object K: `{a b : ℤ} {K : DerivedCategory C}`.
   PASS; no inequality or boundedness hypothesis is inserted.
10. All cohomology objects in T:
    `hKT : ∀ n, T ((homologyFunctor C n).obj K)`. PASS.
11. Tensor cohomology vanishes outside [a,b], for every sheaf F:
    `hK : torAmplitudeIn C a b K`. PASS. I opened TorAmplitude.lean:59
    and TStructure.lean:52: this is `∀ F : C`, the lower and upper
    canonical t-structure bounds of `K ⊗ (singleFunctor C 0).obj F`,
    exactly the stated vanishing, with F universally quantified before
    the degree tests. The tensor is the K-flat-derived one above.
12. Existence of a cochain complex P: `∃ (P : CochainComplex C ℤ)`. PASS.
13. Terms zero below a and above b: `P.IsStrictlyGE a` and
    `P.IsStrictlyLE b`. PASS; Mathlib Embedding/CochainComplex.lean's
    `isStrictlyGE_iff`/`isStrictlyLE_iff` identify these with termwise
    zero objects in the respective degrees.
14. Every term flat and in T:
    `∀ n, ObjectProperty.flat (P.X n) ∧ T (P.X n)`. PASS.
    The conclusion correctly asks for T, not the stronger property S.
15. Isomorphism Q(P) ≅ K: `Nonempty (Q.obj P ≅ K)`. PASS;
    all existential choices follow the hypotheses in the required order.

Edge cases: a=b permits one nonzero term, including a=b=0; b<a forces
K to be zero by tensoring with the unit and is covered by the zero complex.
Zero objects, the zero coefficient ring, and the empty scheme are not excluded.
There is no independent index-set parameter or nonemptiness assumption.
No characteristic, Noetherian, finite-ring or constructibility restriction is
added. The universe u is arbitrary; the site's morphisms live in u and objects
in u+1, and ModuleCat values have the established u+1 convention. The generic
source binds object, morphism and localization universes separately. Nothing
requires the site object and morphism universes to coincide.

Independent searches using different phrases from the worker:

- `msearch.py ... leanfinder "bounded complex flat objects lifting epimorphism
  object property"`: eight results, including surjectivity up to refinements
  and degreewise epimorphisms; none is the class-resolution theorem.
- `msearch.py ... loogle "CochainComplex, ObjectProperty"`: unknown identifier
  ObjectProperty; no negative mathematical conclusion inferred.
- `msearch.py ... leansearch "resolution by a class of flat objects with
  bounded Tor amplitude"`: service unavailable (Internal Server Error).
- Independent rg searches of Mathlib CategoryTheory and Algebra/Homology for
  LiftsAlongEpi/torAmplitudeIn: no hits. Searches of project lean/Sheaf for
  LiftsAlongEpi/FlatModelOfClass: no duplicate. Broader flat-model searches
  found module and scheme variants, not this lifting-class result.
- Upstream rg located ResolutionByClass, TorAmplitude, FlatModelOfClass and
  its genuine specialization in SixFunctors/Etale/Derived/Finiteness/FlatModel.
  I read the caller at lines 199 onward and the complete generic proof.
  This independently confirms the existing record instead of creating a copy.

The source proof first obtains the cohomological bounds, represents K by a
complex zero above b, replaces it by an S-resolution using the lifting property,
and uses bounded-above flatness to make this resolution K-flat. Tor vanishing
makes its opcycles at a flat; T-closure under cokernels puts these opcycles in T.
Truncation below a then gives the flat T-complex and the isomorphism through Q.
The node has no additional proof steps. H5/H6/H8/H9 introduce no new obligations:
this delivery creates no definition, theorem, module or sorry; it records an
already proved declaration with its existing documentation and proof.

Validation: a direct Python comparison confirmed `lean.statement` is verbatim
the source signature. Its C and universe variables are bound by the source
section, not unbound auto-implicit variables. A non-delivered scratch probe
was compiled with the required `scompile.py ND lem-sf-flat-model-class-resolution`.
It imports the theorem and the recorded derived-tensor module, activates the
usual sheaf monoidal instance, checks the specialization, and synthesizes the
abelian, Grothendieck, monoidal-preadditive, closed, braided, derived-category
and functorial-flat-resolution structures. Both compiler passes completed
cleanly in 1.6 seconds without warnings. No live file was edited, no global
build was run, and the scratch probe is outside the delivered module directory.

Mismatches found: none. Changes: appended this independent review only;
retained the worker's existing declaration and exact signature.
