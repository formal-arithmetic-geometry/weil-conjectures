## Worker report

The module Sheaf.Algebra.Homology.BoundedInjectiveTotalHomExact states
CochainComplex.boundedInjective_totalHom_exact, with one sorry and no new definitions.
The node is copied from the live stage-1-reviewed record, changing only lean.
There is no repair note for this item. The Q107 PASS in reviewed is a stage-1 review:
it does not supply a Lean record or settle the stage-2 task.

Clause-by-clause correspondence:

- A commutative ring: `{A : Type u} [CommRing A]`.
- Integer-indexed cochain complexes of A-modules: `U V W I : CochainComplex
  (ModuleCat.{u} A) ℤ`. The maps `j : U ⟶ V` and `p : V ⟶ W` are chain maps,
  including their differential commutation laws, by Mathlib's complex morphism type.
- Short exactness of the input in every degree: `hseq` gives, for every integer s,
  `Function.Injective (j.f s)`, `Function.Exact (j.f s) (p.f s)`, and
  `Function.Surjective (p.f s)`. Function.Exact says precisely that the image of j
  is the kernel of p; it includes the assertion pj = 0, so no separate zero-composite
  hypothesis is required.
- Injective terms of I: `hinj : ∀ q : ℤ, Injective (I.X q)`. This is categorical
  injectivity in the category of A-modules, hence exactly extension across injections.
- Integers a <= b: `(a b : ℤ) (hab : a ≤ b)`.
- Vanishing outside [a,b]: `hbound : ∀ q : ℤ, q < a ∨ b < q → IsZero (I.X q)`.
  An isZero module is precisely a module whose underlying group is zero; it does not
  require a syntactic equality with Mathlib's chosen zero module.
- The total Hom objects are the recorded `moduleHomComplex W I`,
  `moduleHomComplex V I`, and `moduleHomComplex U I`. No construction is copied.
  Their degree-r modules are Mathlib's homogeneous Cochain products and the
  differential is the recorded A-linear δ_hom, with d_I z - (-1)^r z d_M.
- The asserted maps are existentially quantified as actual morphisms of these
  cochain complexes, so their components are A-linear and commute with differential.
  The first formula fixes every `(pstar.f r) z` at every pair `(s,t)` with `s+r=t`
  to `p.f s ≫ z.v s t hst`; the second fixes `(jstar.f r) z` to
  `j.f s ≫ z.v s t hst`. Composition here means z_s after p_s or j_s.
  These formulas determine both chain maps uniquely. This is the asserted existence
  and exactness of the prescribed canonical maps, not an assumption of arbitrary maps
  or a definition by an unconstrained existence theorem.
- The final universally quantified conjunction is injectivity of pstar, exactness
  at Hom(V,I), and surjectivity of jstar in each degree r. This states both zero ends
  and the full middle exactness of the displayed sequence, retaining A-module maps.
- No bounds, finite-generation conditions, or Noetherian hypotheses occur on U,V,W
  or A. There is no derived-isomorphism claim in this node: the claim is exactness
  of explicit complexes, so it remains at the complex level.

Dependency declarations read and used:

- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  DerivedCategory and HasDerivedCategory. Its underlying integer-indexed complex and
  chain-map notions are Mathlib's CochainComplex and HomologicalComplex.Hom; their full
  definitions were read in HomologicalComplex.lean. The recorded module is imported.
  The derived-category localization is not needed by this complex-level statement.
- def-sp-injective-resolutions: Mathlib.CategoryTheory.Preadditive.Injective.Basic,
  CategoryTheory.Injective, with its extension property `factors`. The resolution
  clause was also read in Injective.Resolution; no resolution is assumed or used here.
- def-sc-module-total-hom-complex:
  WeilConjectures.Algebra.Homology.ModuleHomComplex,
  CochainComplex.moduleHomComplex. Its actual data and the helper proofs
  moduleHom_shape/moduleHom_square were read. Mathlib's HomComplex.Cochain.v and
  δ_hom supply the existing component API and differential.
- Function.Exact is reused from Mathlib.Algebra.Exact.Basic, with its exact-pair
  docstring and definition read; it is not a replacement definition of exactness.

Sources read: local Stacks more-algebra.tex, section-hom-complexes (Tag 0A8H),
including the product and signed differential; homology.tex, definition-injective
(Tag 0135); and dualizing.tex, lemma-finite-ext-into-bounded-injective (Tag 0G4H)
and its truncation proof. The statement is the node's auxiliary complex-level
expansion, not an assertion that Stacks states this auxiliary lemma verbatim.

Edge cases checked before writing:

- I = 0: all Hom modules vanish, the two prescribed maps are zero, and the asserted
  sequence is exact. Its terms satisfy categorical injectivity and the support bound.
- a = b: only s = a-r contributes in degree r, reducing the claim to the extension
  property of the single injective module. The endpoints are included in hbound.
- U = 0 or W = 0: the corresponding input arrow is an isomorphism degreewise;
  the output exactness and its reversed orientation are correct.
- The zero ring and complexes unbounded in both directions are admitted. Every
  cochain component is quantified and no finite direct-sum surrogate is introduced.
- Necessity of injectivity: over Z, the degree-zero sequence Z --2--> Z --> Z/2
  and I = Z[0] makes jstar multiplication by 2, which is not surjective. The stated
  injectivity hypothesis excludes precisely this invalid test.
- Distinct module and ring sizes do not impose a mathematical restriction: the
  recorded total Hom interface uses the same universe, and u may be chosen large
  enough for the ring and all complexes. No extra universe equality binder is added.

Searches performed on 2026-10-22:

- msearch.py leanfinder, query "Total Hom into a bounded termwise injective module
  complex preserves short exact sequences degreewise": 8 hits, including
  HomologicalComplex.shortExact_of_degreewise_shortExact,
  HomologicalComplex.shortExact_iff_degreewise_shortExact, and
  CategoryTheory.ShortComplex.Exact.descToInjective. These are general criteria
  or extension tools; none states exactness of the specified total Hom sequence.
- msearch.py leansearch, query "Contravariant module valued total Hom into a bounded
  injective cochain complex preserves short exact sequences": 8 hits, including
  Ext.contravariantSequence_exact and ShortComplex.ShortExact.unop. These are Ext
  exactness and opposite-category results, not this cochain-level result.
- msearch.py loogle, query "CochainComplex.moduleHomComplex,
  CategoryTheory.ShortComplex.ShortExact": 0 hits; Loogle reports the project-only
  moduleHomComplex identifier unknown. This is not evidence about the project;
  the project's definition was found and read directly.
- msearch.py grep, query "HomComplex.*[Ee]xact|[Ee]xact.*HomComplex|moduleHomComplex",
  subdirectory Algebra/Homology: 0 hits.
- rg in lean/WeilConjectures and lean/Sheaf for moduleHomComplex, precomposition,
  bounded-injective Hom, and Hom/ShortExact: existing total Hom, Koszul comparison,
  derived Hom and precomposition-homotopy modules, but no exact statement matching
  this node. The precise item-id search in WeilConjectures gives no match.
- The existing ModuleHomPrecompHomotopy module defines precomposition and proves
  homotopy identities. Those identities do not state the present exactness result.
  This delivery does not redefine that construction: the single theorem characterizes
  its two maps by their component formulas. No helper notion or new node is needed.
- rg for totalHom_exact, boundedInjective_totalHom, total_hom.*exact, and
  moduleHom.*[Ee]xact in both project roots found no declaration collision.

Validation: scompile.py Q92 lem-trf-bounded-injective-total-hom-exact compiled the
single module cleanly against the live server library. autoImplicit is disabled;
every variable and universe is bound explicitly. Only the theorem proof is sorry.
No STATEMENT-DISPUTED flag, statement correction, new node, or dependency repair.
The maintainer performs the independent reading required by the dispatch brief.

## Second reading by Q92

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
