## Worker report

The module Sheaf.Algebra.Homology.DerivedEvaluationFiniteInjective defines
DerivedCategory.finiteInjectiveEvaluation and states
DerivedCategory.isIso_finiteInjectiveEvaluation, with its sole theorem proof `sorry`.
The node statement, proof, and dependency lists are unchanged.

Source read: Stacks Project more-algebra.tex, lemma-internal-hom-evaluate (Tag 0A67),
lemma-internal-hom-evaluate-isomorphism (Tag 0A68), and
lemma-internal-hom-evaluate-isomorphism-technical (Tag 0A69). The latter's three
conditions are exactly the item's three hypotheses. The map is the map of 0A67,
constructed from evaluation with the usual Koszul symmetry, rather than an
arbitrary morphism between the same objects. The module docstring carries all
six proof steps of the node, including the two uniform tail estimates.

Hypotheses and clauses, matched with Lean:

- A commutative ring R: `(R : Type u) [CommRing R]`. No Noetherian, local, nonzero,
  finite global dimension, or characteristic assumption is imposed.
- K,L,M in D(R): `(K L M : DerivedCategory (RingSiteModules R))`.
  `CategoryTheory.RingSiteModules` is the existing category of modules on the
  one-object site with bottom topology and constant ring R. On this site every
  presheaf is a sheaf and evaluation at its unique object identifies this category
  with R-modules. The two `HasDerivedCategory.{u}` binders fix the small-Hom
  localization conventions for these module categories; they are size structure,
  not additional mathematical finiteness assumptions.
- Derived internal Hom: `SignedRingedHom.hom` and `homFunctor`, whose definitions
  specialize the recorded `CategoryTheory.derivedInternalHomOfUniverses` to this
  one-object ringed site. Thus the Hom is the dependency's K-injective-derived
  internal Hom, with its functorial action in both arguments.
- Derived tensor: the existing `SignedRingedHom.derivedMonoidal` instance supplies
  `⊗` and `⊗ₘ`. This is the native K-flat-derived monoidal structure from ordinary
  total tensor, not a new tensor operation. Its representative comparison is
  normalized in RingedInternalHomSignedCalculus.
- Hypothesis (i), L: `hL` exhibits a cochain complex J, integers a,b such that every
  term outside the interval is `IsZero`, injectivity `∀ i, Injective (J.X i)`, and
  `Nonempty (Q.obj J ≅ L)`. Hypothesis (i), M: `hM` has the identical three clauses
  for I and M. Bounded means bounded on both sides, as the node explicitly states;
  no injectivity is requested for the input K.
- Hypothesis (ii): `hTor` binds one interval with `a ≤ b`, then quantifies over every
  module N on the one-object site and every integer j. The premise
  `j < a ∨ b < j` implies that the j-th `homologyFunctor` object of
  `RHom(L,M) ⊗ (singleFunctor _ 0).obj N` is zero. The interval is independent of
  N and j; singleFunctor puts N in degree zero. For cochain complexes these
  homologyFunctor objects are exactly cohomology.
- Hypothesis (iii): `hK` quantifies over every representative P with
  `Nonempty (Q.obj P ≅ K)`, then over every integer n. `P.truncLE n` is Mathlib's
  good truncation, retaining the kernel of the outgoing differential at degree n.
  The exact additive evaluation functor on the one-object bottom-topology site
  sends that truncation to an ordinary ModuleCat R complex. `Q.obj` and the
  dependency `DerivedCategory.IsPseudoCoherent` then express precisely that the
  truncation is pseudo-coherent. This is independent of the representative:
  good truncation preserves quasi-isomorphisms, and this site's evaluation is an
  exact equivalence. Requiring every representative is therefore equivalent to
  the node's derived good truncation condition, not an added hypothesis. Every
  localization object admits a representative, so this quantifier is not vacuous.
- The canonical arrow's source is `RHom(L,M) ⊗ K` and target is
  `RHom(RHom(K,L),M)`. `finiteInjectiveEvaluation` is actual data: transpose under
  `SignedRingedHom.adjunction` of associativity, the braiding of K with RHom(K,L),
  evaluation `RHom(K,L) ⊗ K → L`, and evaluation `RHom(L,M) ⊗ L → M`.
  This differs from the node's three-factor order only by the ordinary associator
  and the graded symmetries the node specifies. The adjunction is the existing
  evaluation-normalized adjunction on K-flat representatives; no arbitrary choice
  of adjunction, map, or natural isomorphism is added as a hypothesis.
- Isomorphism: the first conjunct is `IsIso (finiteInjectiveEvaluation R K L M)`.
- Natural in K,L,M: the second conjunct is the commuting naturality square for
  arbitrary `f : K ⟶ K'`, `l : L' ⟶ L`, and `m : M ⟶ M'`. L is contravariant and
  K,M covariant in both source and target. The right-hand target map uses
  `homFunctor.map (f.op,l)` inside an opposite and then the outer Hom map with m.
  No finiteness condition is needed on the primed triple for naturality of this
  canonical map, and no such condition is added.

Dependency declarations read and used:

- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q` (def-weil-abstract-derived-category).
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses:
  `CategoryTheory.derivedInternalHomOfUniverses`, through
  Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus's
  `SignedRingedHom.homFunctor`, `hom`, `adjunction`, and `derivedMonoidal`
  (def-pur-derived-internal-hom). The adjunction's normalized representative
  characterization and the specialization's full source were read.
- Mathlib.CategoryTheory.Preadditive.Injective.Basic: `CategoryTheory.Injective`
  (def-sp-injective-resolutions); its `factors` field is extension along all monos.
  The source of `InjectiveResolution` was also read; a bounded model of an entire
  derived object is written explicitly because it is not a resolution of a
  single degree-zero module.
- Sheaf.Algebra.Homology.KFlat:
  `CochainComplex.IsKFlatIndependentCoefficients` and the canonical monoidal
  infrastructure (def-pc-kflat-complex), used through the native derived tensor.
- Mathlib.Algebra.Homology.BifunctorShift: `CochainComplex.mapBifunctor`
  (def-pc-tensor-complex-sheaves), ordinary total tensor underlying that structure.
- Sheaf.RingTheory.RingPseudoCoherent: `DerivedCategory.IsPseudoCoherent`
  (def-pc-ring-pseudo-coherent-complex), whose definition is a bounded-above finite
  free complex with a derived isomorphism. No private copy is introduced.
- The existing `RingSiteModules` abbreviation from
  Sheaf.Algebra.Homology.RingHomExtensionDefs is reused without redefining it.
- Recorded proof modules for Tor-amplitude flat models, bounded-flat K-flatness,
  the heart/truncation infrastructure, derived cohomology exact sequences,
  K-injective representatives, and the cohomology ladder are imported privately.
  The canonical-map and pseudo-coherent-case proof nodes have no Lean record yet;
  their proof-only modules are omitted. No missing statement notion is hidden
  behind an unstated theorem in this module.

Edge cases checked mathematically: R may be the zero ring, and K,L or M may be
zero. All maps in the zero cases have zero source and target and the conclusions
remain valid. For a field with L=M=R[0], finite-dimensional K in degree zero gives
ordinary double-dual evaluation. Unbounded K is not excluded: only its good
truncations are constrained. Neither positive nor negative n is excluded. No
nonemptiness or nonzero constraint is imposed on any interval's terms. The
interval in hTor is nonempty as the statement requires a≤b, which also represents
zero complexes. Arbitrary commutative non-Noetherian rings are allowed; the
pseudo-coherent condition uses finite free models, not a Noetherian substitute.

Searches (msearch.py, Q74, this item; successful search results also logged by the
wrapper in searches.jsonl):

- LeanFinder query: "The evaluation morphism RHom L M tensor K to RHom RHom K L M
  is an isomorphism for finite injective dimension finite Tor dimension and pseudo
  coherent truncations". Eight results concerned K-projective localization,
  bounded derived representatives, Tor, and condensed internal projectivity;
  none stated this theorem.
- Loogle query: "DerivedCategory, CategoryTheory.IsIso". Twelve results included
  DerivedCategory.isIso_iff and localization criteria; none stated the evaluation
  criterion with these three hypotheses.
- Mathlib grep query:
  `derivedEvaluation|internal-hom-evaluate|finite.*[Ii]njective.*[Ee]val`,
  subdirectory Algebra/Homology. Zero hits.
- LeanSearch query: "Derived evaluation RHom L M tensor K to RHom RHom K L M is
  invertible when L M have finite injective dimension and RHom L M finite Tor
  dimension and truncations K pseudo coherent". Eight results on invertible
  modules, contraction and ordinary ModuleCat closed adjunction; none is the
  unbounded derived evaluation theorem.
- rg of the upstream WeilConjectures tree for this node id and
  `finiteInjectiveEvaluation`: no matches. The upstream-name registry also has
  no match for the proposed names. Search of lean/Sheaf for derivedEvaluation and
  this node found the complete-local-duality proof docstring citing this node,
  and unrelated coefficient-system and sections-evaluation declarations; no
  duplicate theorem or map. The generic RingedInternalHomSignedCalculus API
  supplies the existing Hom, tensor, braiding, and normalized adjunction used here.

Validation: the initial module compiled cleanly with scompile.py against the
published server library (both sandbox and library checks). The completed packet
is then checked by the required deliver2.py dry run. No statement correction,
new node, dependency-module replacement, or STATEMENT-DISPUTED issue is needed.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
