## Worker report

The delivery states `CategoryTheory.ringedUnboundedDescentCriterion` in
`Sheaf.CategoryTheory.RingedUnboundedDescentCriterion`. Its only theorem proof is
`sorry`; there are no new definitions, axioms, private instances or copied notions.
Source read: `literature/stacks-project/sites-cohomology.tex`, lines 5687–5707,
Situation `situation-olsson-laszlo` (0D6R), and lines 6434–6485,
Lemma `lemma-equivalence-unbounded-one` (0D7V), including its proof.

Hypothesis and conclusion correspondence:

- Sites and commutative ring sheaves: `{C D : Type u} [SmallCategory C]
  [SmallCategory D]`, `J`, `K`, `O : Sheaf J CommRingCat`, and
  `R : Sheaf K CommRingCat`. The existing sheafCompose/forget₂ converts a
  commutative ring sheaf to the ring sheaf expected by the recorded module category.
  The common site/coefficient universe is the chosen universe containing the small
  sites; this is the dependency's small-site presentation, and imposes no geometric,
  connectedness, nonemptiness or finiteness restriction. Derived localization
  universes `wC`, `wD`, `wAb` are independent, explicit HasDerivedCategory binders.
- The geometric ringed-topos morphism is exactly the recorded
  `CategoryTheory.RingedToposMorphism`, with induced module direct image `f.modules`.
  It is not required to come from a functor of presented sites.
- Module pullback is presented as `L` with `adj : L ⊣ f.modules`. This is a
  presentation of the actual module pullback, not an unconstrained map: any left
  adjoint to this specified direct image is uniquely isomorphic to it. The adjunction
  identifies its unit and counit; all assertions are invariant under the unique
  comparison of left adjoints. `[L.Additive]`, `[PreservesFiniteLimits L]`, and
  `[PreservesFiniteColimits L]` render hypothesis (1), exact module pullback.
- `A` and `B` are Mathlib ObjectProperty predicates on the respective recorded
  `ringedSiteModules`. Their full subcategories use ObjectProperty.FullSubcategory.
  ContainsZero and IsClosedUnderIsomorphisms express zero and strict fullness;
  IsClosedUnderKernels, IsClosedUnderCokernels and IsClosedUnderExtensions are exactly
  the three weak Serre closure conditions, not closure under arbitrary subobjects.
- `heart` renders (2): an equivalence `B.FullSubcategory ≌ A.FullSubcategory`,
  whose functor, after inclusion, is naturally isomorphic to L after inclusion,
  and whose inverse similarly identifies with f.modules. The two displayed natural
  isomorphisms are witnesses of restriction of these fixed functors, not substitutes
  for their canonical derived maps.
- `unit₀` renders (3): for every `G` with `B G`, the unit of the existing canonical
  `adj.mapDerivedCategoryRightDerivedAdjunction`, evaluated on
  `(DerivedCategory.singleFunctor _ 0).obj G`, is an isomorphism. The exact
  pullback/single-object comparison identifies its target with Rf*(f*G)[0] in
  the source's notation. No arbitrary derived adjunction is supplied as a hypothesis.
- `boundC` and `boundD` each begin with `∃ V : Set C` (respectively D), followed
  by a covering presieve of every site object all of whose domains belong to V.
  For each member U of V, `∃ d : ℤ` precedes the universal quantifier over
  covering presieves P. The existential Q is again covering and every arrow of Q
  factors through an arrow of P; hence Q is an actual refinement, not merely a
  comparison of generated sieves. Every domain W of Q, every F in A (or B), and
  every natural degree p with `d < (p : ℤ)` has vanishing right-derived sections.
  Taking all such good coverings supplies exactly the cofinal collection of 0D6R;
  conversely a cofinal collection provides a Q for each P. Passing from repeated
  indexed families to presieves forgets only repeated arrows and preserves this
  property. The Grothendieck topology has the same cofinal site coverings.
  Cohomology is `homologyFunctor AddCommGrpCat p` of the existing total right
  derived `sectionEvaluation` evaluated on F[0], so it is the right derived functor
  of sections, as requested. `IsZero` applies to an additive group object.
- The first conclusion `L.mapDerivedCategory.IsLeftDerivedFunctor
  L.mapDerivedCategoryFactors.hom (HomologicalComplex.quasiIso _ (.up ℤ))`
  expresses Lf* = termwise f*, with the exact canonical localization comparison.
- The next two conjuncts assert isomorphy of the canonical derived unit on every
  object of `DerivedCategory.homologyProperty B` and of the canonical derived counit
  on every object of `DerivedCategory.homologyProperty A`, respectively. That
  upstream definition means all integer cohomology objects belong to B or A.
- The final existential is an equivalence between precisely those full
  subcategories. Its forward functor identifies after inclusion with L.mapDerivedCategory
  and its inverse identifies with f.modules.rightDerivedFunctor. Integer-shift
  structures and IsTriangulated for both directions give the triangulated assertion.
  In particular these clauses assert preservation of the indicated cohomology
  conditions by the actual functors, not merely an unrelated equivalence of categories.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`,
  including all its geometric, structural-ring and induced-module fields.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  a transparent abbreviation for Mathlib SheafOfModules, with its inherited abelian
  structure; no additional chosen abelian instance.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the dependency
  `CategoryTheory.Precoverage.IsSiteForCoverings`; this statement uses its retained
  Mathlib GrothendieckTopology, Presieve, Sieve.generate and covering-sheaf convention.
- `def-weil-size-convention` is metatheoretic and has no declaration; the explicit
  universes and small-category and localization binders render it.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: DerivedCategory,
  HasDerivedCategory, Q and the canonical triangulated derived-category structure.
- The additional already-landed definition node
  `def-sfb-ringed-site-section-functors` owns the reused
  `CategoryTheory.RingedSiteSectionFunctors.sectionEvaluation` in
  `Sheaf.CategoryTheory.Sites.RingedSiteSectionFunctors`. Its declaration and
  underlying evaluation/forget-scalars expression were read. Only its id is added
  to stmt_deps, as authorized for already-landed definition nodes.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction; its exact
  left adjoint and K-injective right derivation construction were read in full.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs` and
  `.Triangulated`: the actual unbounded rightDerivedFunctor and its canonical
  K-injective shift/triangulated structures.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`:
  DerivedCategory.homologyProperty and its weak Serre triangulated-subcategory
  instances, read together with Mathlib ObjectProperty closure classes.

All recorded proof-dependency modules that exist are imported privately, including
ExactFunctorDerivedFunctor, TruncationsAndHomotopyColimits,
CohomologyInWeakSerreSubcategory, RingedSiteKInjectiveResolutionsOfUniverses,
ProjectionMateExact, and the relevant Mathlib exact/homology modules. The right
derived triangulated module is public because its canonical functor is also part
of the signature. The two proof dependencies
`lem-sfb-ringed-bounded-below-descent-criterion` and
`lem-sfb-ringed-local-bound-direct-image-truncation` have no Lean module yet;
they are proof dependencies only, not needed to type this statement. Their proof
roles are preserved in the theorem docstring.

Edge cases checked: empty sites and empty covering presieves; zero rings and zero
modules; the minimal weak Serre class of zero objects and the full module class;
identity morphisms and equivalences; integer local bounds including negative d;
nonnegative p including p = 0; arbitrarily negative cohomology of the derived
objects. No bounded-below condition is added. Empty covering presieves make their
domain clauses vacuous, as the source does; covering by the empty family is allowed
only when the topology allows it. The existence of V includes the empty-site case.
Negative cohomology of a module in degree zero under derived sections vanishes,
so nonnegative p covers exactly the potentially nonzero cohomology in 0D6R.

Searches actually run with msearch.py Q01 and this item:

- LeanFinder: `Exact pullback of ringed topoi equivalence on weak Serre subcategories
  induces unbounded derived equivalence with local cohomology bounds`. Eight hits:
  exact_tfae, Ext.mapExactFunctor_hom, exact derived factorization, isHomological,
  and standard derived t-structure facts; no descent criterion.
- LeanSearch: `Local cohomological bound on a ringed site gives an unbounded derived
  equivalence for a flat morphism of ringed topoi`. Eight hits, all scheme/ring/module
  flatness lemmas; none states the item.
- Loogle: `Adjunction.toEquivalence, IsWeakSerre`: zero hits, with unknown identifier
  Adjunction.toEquivalence. Repeated with fully qualified
  `CategoryTheory.Adjunction.toEquivalence`: nine hits including the actual generic
  adjunction-to-equivalence construction. It assumes units and counits already
  invertible, so does not state this node.
- Logged grep: `IsWeakSerre|olsson|laszlo|unbounded.*[Ee]quivalence` in Mathlib
  CategoryTheory: zero matches.
- Direct rg of both lean/WeilConjectures and lean/Sheaf for RingedToposMorphism,
  weak Serre and local bounds found the reused weak Serre closure/homologyProperty,
  module-adjunction and section-functor APIs listed above. Direct grep of the item
  id in lean/WeilConjectures found nothing. Exact name checks for
  ringedUnboundedDescentCriterion, equivalence_unbounded_one and equivalenceUnboundedOne
  in Mathlib, WeilConjectures and Sheaf found no existing declaration.
- `blueprint_refs.py search 'local cohomology bound'`: zero blueprint matches.
  The existing DAG search for situation-olsson-laszlo/local bound property found
  this item and its local-bound proof lemmas, not an existing statement of it.

There is no statement correction, source discrepancy or STATEMENT-DISPUTED flag.
The live node's statement, source, proof and proof_deps are retained verbatim.

## Second reading by Q01

Author's second reading; the independent review is the maintainer's delivery review.
Re-read the node, source and complete Lean signature after the first elaboration.
The five hypotheses are separately visible as exact L, heart, unit₀, boundC, boundD.
The weak Serre assumptions use kernels/cokernels of maps between members, not the
stronger Serre notion. The two natural identifications in heart and in the final
equivalence pin both functors. The unit and counit clauses name the canonical
adjunction construction, not the existential equivalence's unspecified maps.
The actual refinement factorization is retained in the local bound, and its bound
is outside both the refinement and module quantifiers, as in 0D6R. The basis cover
and cofinal-good-cover clauses are both present on both sites. The nonnegative
cohomology degrees include zero and the bound is an integer. All derived cohomology
conditions quantify over every integer. The triangulated assertion covers both
functors. No new mismatch with the node or source was found. Explicit derived
localization universe arguments were added to the equivalence clause to reduce
elaboration work; the heartbeat setting is scoped to the declaration. The file
retains the prescribed module mode and contains only the main theorem with sorry.

Validation: scompile.py compiled both the sandbox and library module cleanly
(43.7 s and 43.9 s respectively, with no non-sorry warnings). The prescribed
deliver2.py --no-push passed preflight and compilation, printing OK at commit
5ba98e74c8c. The final signature record is verbatim, all Lean lines are at most
100 characters, and exactly one sorry remains, on the main theorem.
