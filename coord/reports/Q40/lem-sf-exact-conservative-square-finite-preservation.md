## Worker report

The module Sheaf.CategoryTheory.ExactConservativeSquareFinitePreservation states
CategoryTheory.Functor.additive_exact_finite_preservation_of_conservative_square.
Its only proof is sorry. It introduces no definitions, no new nodes and no dependency
repairs. The natural-language statement and the accepted six-step Q121 proof split
are unchanged. Q121 completed stage 1; the node had no Lean attachment, so the earlier
worker's assertion that stage 2 would re-split the item does not apply.

Hypotheses and conclusions, checked against the entire node:

- The four abelian categories are C, D, A, B, each with its own explicit object
  universe uC/uD/uA/uB, morphism universe vC/vD/vA/vB, Category instance and
  Abelian instance. No equality between universes is imposed.
- The three functors are p : C ⥤ A, q : D ⥤ B, L : A ⥤ B. Their additivity is
  [p.Additive], [q.Additive], [L.Additive]. The hypotheses hp, hq and hL each
  quantify over every ShortComplex in the appropriate source and require that
  ShortExact is carried to ShortExact by ShortComplex.map. Their additivity supplies
  the zero-morphism preservation needed to form these mapped complexes.
- Faithfulness of q is [q.Faithful]: map_injective is injectivity on each hom set.
  Conservativity is [q.ReflectsIsomorphisms]: an isomorphism q.map f implies IsIso f.
  Neither full faithfulness nor an equivalence is assumed.
- H : C ⥤ D has no additivity or zero-preservation hypothesis. The given natural
  isomorphism eta : H ⋙ q ≅ p ⋙ L has exactly the direction q ∘ H ≅ L ∘ p.
- The conclusion ∃ (_ : H.Additive), ... asserts additivity rather than assuming it.
  This proof binder makes the inferred zero-preservation instance available when
  elaborating ShortComplex.map H. Its next conjunct is preservation of every short
  exact sequence ∀ S : ShortComplex C, S.ShortExact → (S.map H).ShortExact.
  Existential quantification over a proof of the Prop-valued class adds no data or
  hypothesis to the mathematical claim.
- PreservesFiniteLimits H and PreservesFiniteColimits H give both remaining
  preservation assertions. Their underlying PreservesLimit/PreservesColimit
  classes send any given limiting cone/colimiting cocone to an actual limit/colimit
  of its image, rather than merely asserting an object isomorphism. Empty shapes
  include terminal and initial objects, hence zero objects in these abelian
  categories. Parallel-pair diagrams include equalizers and coequalizers; taking
  one arrow zero gives kernels and cokernels, since the asserted additivity also
  preserves zero morphisms. Finite discrete shapes give finite products and
  coproducts. The Additive conclusion also yields the existing
  preservesFiniteBiproductsOfAdditive instance, whose mapBicone proof verifies
  the actual image injection/projection identities, including the empty family.
  No independent preservation clauses or extra hypotheses are needed for these
  listed special cases.

Dependency declarations read and used:

- def-sp-abelian: CategoryTheory.Abelian, Mathlib.CategoryTheory.Abelian.Basic;
  its finite products, kernels, cokernels, normal monos and normal epis give the
  node's zero object and finite biproducts.
- def-weil-pbc-additive-functor: CategoryTheory.Functor.Additive,
  Mathlib.CategoryTheory.Preadditive.AdditiveFunctor. Its sole field is map_add.
- def-weil-pbc-exact-sequence: the recorded module
  Mathlib.Algebra.Homology.ExactSequence is imported, using its ShortComplex.Exact
  interface and CategoryTheory.ShortComplex.ShortExact from
  Mathlib.Algebra.Homology.ShortComplex.ShortExact. ShortExact means Exact plus
  Mono f and Epi g; ShortComplex.map uses exactly the original image arrows.
- def-galois-finite-limits-colimits: HasFiniteLimits/HasFiniteColimits in
  Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits, available through the public
  preservation imports. All these finite shapes are available in abelian categories.
- def-galois-exact-functor: PreservesFiniteLimits/PreservesFiniteColimits in
  Mathlib.CategoryTheory.Limits.Preserves.Finite, the node's recorded Mathlib match;
  exactFunctor in Mathlib.CategoryTheory.Limits.ExactFunctor is precisely their
  conjunction. These imports use that interface, without a private replacement.
- The proof dependency lem-sp-exact-functor-preserves-homology is imported through
  Mathlib.Algebra.Homology.ShortComplex.PreservesHomology, with the recorded
  Functor.preservesHomologyOfExact. Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
  is also a proof-only import for exact_tfae, which identifies short-exact
  preservation with finite-limit and finite-colimit preservation.

Sources checked: the equivariant extension-by-zero additive and finite-preservation
instances in WeilConjectures.WeilSheaf.OpenImmersion; the naturally commuting
forgetful square and finite-preservation instances in
WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra; and Stacks homology.tex,
lemma-exact-functor (Tag 010N). The docstring carries all six accepted proof steps,
including faithful cancellation, the image-to-kernel comparison and actual finite
biproduct identities. No proof route was changed.

Edge cases checked before writing: q = identity reduces to transport of additivity
and exactness across the given natural isomorphism; H can be the zero functor when
p ⋙ L is zero; no nonzero-object, nonempty-index or positive-degree hypothesis is
present. Empty diagrams and empty biproducts are included. eta is an arbitrary
natural isomorphism, not an equality or componentwise identity. The eight separate
universe variables impose no size restriction between the four categories.

Searches for an existing statement:

- msearch.py leanfinder: "A functor in a naturally commuting square of abelian
  categories is additive exact and preserves finite limits and colimits if the
  other three functors are additive exact and the target vertical functor is
  faithful and conservative". Eight results, including exact_tfae,
  reflects_exact_of_faithful, ExactFunctor.of and Guitart exactness. None states
  this full square criterion with no prior additivity assumption on H.
- msearch.py loogle: "CategoryTheory.Functor.Additive,
  CategoryTheory.Limits.PreservesFiniteLimits". Twelve results including
  exact_tfae and preservesFiniteLimits_tfae; these assume the additivity of the
  functor under study and do not give the square criterion.
- msearch.py grep in CategoryTheory:
  "additive_of_comp_faithful|reflects_exact_of_faithful|exact_tfae|conservative.*square".
  Five hits: individual additivity/exactness reflection lemmas and their uses;
  no full criterion. exact_tfae was separately read in Algebra.Homology.
- rg in lean/WeilConjectures and lean/Sheaf for conservative-square names,
  additive_of_comp_faithful and existential additive conclusions found only
  individual uses or specialized statements, not this theorem. The required
  grep for this blueprint id in lean/WeilConjectures found no declaration.
  The proposed full declaration name is absent from both project roots and Mathlib.

No disputed statement, node fault or statement correction was found.

Validation: scompile.py compiled the sandbox probe and the actual library module
cleanly on the server (0.9 seconds each). The signature record agrees verbatim
with the source, and every Lean line is at most 100 characters. Delivery preflight
is run with deliver2.py --no-push.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
