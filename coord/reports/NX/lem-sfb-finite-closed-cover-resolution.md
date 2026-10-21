## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteClosedCoverResolution` states
`AlgebraicGeometry.finite_closed_cover_resolution`. Its only postponed proof is this
named theorem. All helper data are definitions with real terms; the theorem's existential
resolution is never selected in a definition. The main theorem returns the specified
augmented quasi-isomorphism, its ordinary derived natural isomorphism, explicit signed
refinement compatibility, and augmentation-normalized pullback compatibility.

This repairs the independent review of immutable head `23a13b10a3d7`.
The required first dry run of the retained packet passed (`04f844ff276`), but the
saved source still had both returned mathematical/interface defects. The Lean source
has therefore been substantively changed, rather than re-pushing that passing packet.
The local live node has the original nine statement dependencies and no resolution
Lean record; the packet retains its original geometry, signs, and refinement clause.

Hypothesis and clause correspondence:

- Schemes X and Z are `{X Z : Scheme.{u}}`; the closed immersion is `i` with
  `[IsClosedImmersion i]`. The finite ordered family is `W : Fin m → Over X`, with
  `hm : 0 < m`; `hclosed` requires each member's structure morphism to be closed.
- Factoring through Z is `hfactor : ∀ a, Nonempty (W a ⟶ Over.mk i)` in the actual over
  category. Because i is monic, these factorizations carry no extra choice. `hcover`
  is precisely equality of the image of i with the union of the members' images.
- The complementary opens are the `U : X.Opens` in `hqc` and `hqcW`, with the displayed
  complementary-image equalities and `QuasiCompact U.ι`. This is quasi-compactness of
  the open immersion, not compactness of its source scheme or of its topological space.
- Arbitrary commutative ring-sheaf coefficients are now explicitly
  `A : Sheaf (ProEt.topology X) CommRingCat.{u+1}`. Every module category uses
  `ringedSiteModules.{u+1} (proEtaleModuleCoefficients A)` directly. The original
  small site's object and morphism universes remain u+1 and u, respectively.
- `finiteClosedIntersection W s` is the finite categorical product in `Over X`.
  This is the scheme-theoretic fibre-product intersection, including the empty
  intersection X. No reduced structure or set-theoretic replacement is used.
- `finiteClosedRestriction k A` is exactly
  `proEtaleModuleInverseImage k A ⋙ proEtaleRingedDirectImage k A`,
  with coefficients the recorded inverse-image ring. `finiteClosedUnit` is the
  sectionwise-normalized actual adjunction unit from the landed closed-projection module.
- The theorem returns `D : FiniteClosedResolution i W A`. Its `rows` is a functor on all
  module sheaves; `additive` supplies its additivity. `terms p` identifies horizontal
  degree p with the finite product of the restrictions to strictly increasing
  (p+1)-tuples. In this abelian category the finite product is canonically the direct sum.
  Thus singleton terms have degree zero, and the last nonzero degree is m-1 with the
  single full tuple. `support` asserts zero terms outside [0,m-1].
- `restriction s t` is fixed, for s⊆t, by `restriction_unit`: its composite with the
  actual source unit equals the actual target unit. Those source units are epis by
  the closed/open localization sequence (and the empty-intersection unit is an iso).
  Consequently these equations specify uniquely the actual pushed-forward restriction
  units, including their coefficient-composition identifications. The conventional
  zero value for non-inclusions is explicit in `restriction_zero` and is never used
  by a face restriction.
- `finiteClosedDifferential` is the sum over deleted positions j of (-1)^j times
  the projection to that face followed by its actual restriction. The field
  `differential` identifies this formula under the graded-term isomorphisms.
- `augment` is natural in the module. `augment_unit` says its composite with K→i_*i^*K,
  projected to each singleton, is exactly the singleton's actual unit. Singleton
  intersections are the canonical one-factor product in Over X, so this is the node's
  direct sum of singleton units under its canonical identification.
- `finiteClosedDouble` applies rows termwise and flips axes so horizontal degree is
  first. `finiteClosedTotal` is Mathlib's total with differential d_h+(-1)^p d_K.
  Since rows have only m nonzero columns, every diagonal is finite, although we use
  the existing general coproduct total construction. The zero preservation and
  coproduct-existence instances are assembled from actual existing adjunction and
  colimit data; they introduce no extra mathematical assumption or postponed theorem.
- `totalAugment` is a natural transformation from termwise i_*i^* to this total.
  `totalAugment_f` fixes its component to the row augmentation followed by the (0,n)
  diagonal inclusion, so no augmentation map is left unconstrained.
- `quasiIso` quantifies over every integer cochain complex with `CochainComplex.plus`
  (existence of an integer lower bound). It asserts that this precise augmentation
  is a `QuasiIso`. `derivedIso` is a natural isomorphism after the ordinary localization
  `DerivedCategory.Q`, and `derivedIso_hom` pins its forward arrow to that same map.
  It uses no completed derived category and is not merely a collection of homology
  isomorphisms. The restriction to `CochainComplex.Plus` is exactly the stated input class.
- `FiniteClosedRefinementCompatible` quantifies over every finer nonempty ordered
  closed cover V, every function f and factorizations V_b→W_(f b), with the same
  quasi-compact-complement condition. Its cross restrictions are normalized by the
  actual units. `finiteClosedRefinementSign` sums permutation signs for permutations
  carrying the increasing target tuple to f of the finer tuple: a repeated image
  gives zero, otherwise there is one permutation and its sorting sign. The resulting
  `finiteClosedRefinementMap` is required to be the graded formula of a natural row
  chain map ρ. Its totalization preserves the augmentation exactly. Its derived map
  equals `finiteClosedDerivedRefinement D D' = D.derivedIso.symm ≪≫ D'.derivedIso`.
  This formula also gives refinement-function independence, identity and composition,
  including permutations (automorphisms of the ordered-family presentation).
- `FiniteClosedPullbackCompatible` quantifies over every scheme morphism g, every
  resolution D' for `finiteClosedPullbackFamily W g`, and the identified comparisons
  c for Z and `cs s` for EVERY scheme-theoretic intersection. The latter target is
  the product intersection of the pulled-back members, so the scheme-theoretic
  base-change identification is included in the comparison, not assumed to be a
  definitional equality of chosen limits. `hc` and `hcs` require the actual units
  to commute with these comparisons on every module.
- Its existential row map σ has source `D.rows ⋙ finiteClosedPullbackComplex g A`
  and target `proEtaleModuleInverseImage g A ⋙ D'.rows`. For each p and t, its natural-transformation
  component under `D.terms` and `D'.terms`, followed by the t-th product projection,
  is the inverse image of the source projection followed by `cs (univ.image t)`.
  Thus the components are exactly the product of the supplied intersection
  comparisons. The next equation requires σ to carry the augmentation through c.
  These two conditions were absent in the returned version.
- The natural chain map τ on totals is required to satisfy the diagonal-inclusion
  equation for ALL integers p,q,n with p+q=n. It takes each inverse image of a
  source (p,q)-summand inclusion to `(σ.app (K.X q)).f p` followed by the target
  inclusion. This is precisely the universal-property description of the
  totalized row map through the canonical interchange g* Tot ≅ Tot g*; it fixes
  τ on the jointly epimorphic summand inclusions. The equation covers negative
  degrees as well as the finite nonzero strip. The final equation requires
  `DerivedCategory.Q.map (τ.app K.obj) = e.hom.app K` on every bounded-below K,
  where e satisfies the augmentation-normalization square with the termwise c.
  Existence of the conjugate e alone can no longer satisfy this predicate.
- Naturality is expressed by natural transformations σ, τ and e. All equations
  remain valid after whiskering by arbitrary parameter-category functors, giving
  automorphisms and parameterized diagrams. Uniqueness from the normalized
  augmentation gives comparison composition. No unconditional closed base-change
  assertion or covering in the pro-etale topology is assumed.
- The statement never asserts that the closed family is a covering in the pro-etale site.

Dependency declarations used:

- Mathlib `AlgebraicGeometry.Scheme`, `IsClosedImmersion`, `QuasiCompact`, `Over`,
  categorical products and pullbacks, `CochainComplex`, `QuasiIso`, `DerivedCategory.Q`,
  `CochainComplex.Plus.ι`, `NatTrans.mapHomologicalComplex`, and
  `HomologicalComplex₂.totalFunctor` and `ιTotal`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleModuleInverseImage` and `proEtaleSheafInverseImage` directly; `ProEtaleRingedOpenClosed`: `proEtaleRingedDirectImage` and
  the ringed localization theorem; `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`.
- `def-sfb-proetale-unit-normalized-adjunction` now owns the already public
  `AlgebraicGeometry.ProEtaleClosedProjection.adjunction` and its unique
  sectionwise-unit characterization `adjunction_exists`, in the existing module
  `Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection`. Its exact declaration
  is reused with `existing: true`; no module is copied and no second adjunction is
  defined. The theorem conclusion `closed_underived_projection` is not used.
- The alias-only `lem-pur-proetale-inverse-image-tensor-comparison` and helper-only
  `lem-weil-pbc-proetale-closed-underived-projection` have both been removed from
  the item's stmt_deps. `def-weil-pbc-proetale-operations` remains for the existing
  ordinary module-derived-category instance reexported by its recorded module.
- Plain proof imports follow all recorded proof-dependency modules: geometric inverse
  image exactness, site inverse-image tensor, ring-sheaf operations and base-change
  mates, finite-strip row augmentation, exact-functor homology, composite adjunction,
  and Mathlib's closed-immersion and quasi-compact base-change instances.

Edge cases checked before writing and again after elaboration:

m=1 has only its singleton in degree zero; the augmentation is the actual closed
restriction comparison, invertible since the member has the same support. Repeated
members are permitted and do not alter the contraction argument. Empty intersections
are empty schemes and their module terms are zero. Z empty, all members empty, and
zero coefficient module/complex are permitted. The ring need not be finite or nonzero.
Lower bounds may be negative, and no uniform lower bound is imposed on all inputs.
The empty member family is deliberately excluded by m≥1 exactly as in the node;
empty subsets occur only in the restriction helper and denote X. Refinement functions
can repeat values: the sign formula then vanishes on those tuples. Pullback comparisons c and every cs must preserve actual units.
On closed intersections the units are epis, so these normalizations also force the
face-restriction squares needed for σ. Products of the cs determine σ in every
nonnegative degree; zero support handles all other degrees. For m=1 the totalization
condition reduces to the singleton cs; for repeated members each factor still has its
own specified comparison; empty intersections contribute zero factors. Identity g is
included with the canonical chosen-limit identifications. A putative e defined merely
by conjugating augmentations no longer suffices: the σ product and τ summand equations
must first hold, and e must equal Q(τ).
The source's quasi-compactness is precisely morphism quasi-compactness, including
non-quasi-separated X; no qcqs hypothesis was added to the theorem.

Searches actually run:

- msearch.py leanfinder, "Augmented finite closed cover resolution of a bounded below
  complex of proetale sheaves by closed intersections": eight hits, mostly affine
  transition-limit descent declarations and Scheme.etaleTopology; none states this.
- msearch.py loogle, `"Cech", "complex"`: CategoryTheory.cechComplexFunctor, a general
  full-tuple presheaf Čech construction, not this finite increasing closed-restriction
  resolution with arbitrary internal ring coefficients.
- msearch.py grep, `closedCover|closed_cover|ClosedCover`: two unrelated Jacobian
  closed-cover approximation declarations in Mathlib.MeasureTheory.Function.Jacobian.
- rg over lean/WeilConjectures and lean/Sheaf for closedCover, closed_cover, ClosedCover,
  finiteClosed, finite_closed and the item id: finite closed-cover cohomological
  vanishing and geometric spread lemmas, plus finite-coefficient support operations;
  no existing declaration gives this arbitrary-ring finite closed-support resolution.
  Existing open Čech complexes were also inspected; their source category and
  section-valued terms do not express these closed internal module restrictions.

There is no statement correction or disputed statement. All new helper declarations
remain part of the resolution notion. There is one new definition-node RECORD reusing
an existing declaration, and no new Lean module for that node.

## New nodes

`def-sfb-proetale-unit-normalized-adjunction` records the existing arbitrary-ring-sheaf
adjunction `ProEtaleClosedProjection.adjunction`, together with its existing unique
unit characterization `adjunction_exists`. This supplies the precise definition used
by `finiteClosedUnit`, and the left/right adjoint instances used for zero preservation.
The source is sites-modules.tex, `lemma-adjoint-push-pull-modules` (Tags 03D2, 03D3),
with proetale.tex Tag 09AA. Read the complete source construction in
ProEtaleClosedUnderivedProjection.lean: `adjunction_exists` has no closed-immersion
hypothesis, fixes every section to `inverseSection`, and proves uniqueness;
`adjunction` selects only this uniquely determined data. Also read the actual
`canonicalAdjunction` and `canonicalUnit_sections` in
ProEtaleModuleInverseImageCanonicalUnit.lean, which construct and normalize it.
The new node does not restate the projection theorem, and none of that theorem's
projection/tensor conclusions is used by the resolution statement.

Searches for this node: msearch LeanSearch with “Canonical adjunction for inverse
image and direct image of module sheaves on small proetale sites with sectionwise
unit” returned 8 generic sheaf/topological/structure-sheaf adjunctions. Loogle
`SheafOfModules.pullbackPushforwardAdjunction` returned the general adjunction and
4 generic consequences. Mathlib grep
`canonicalAdjunction|adjunction.*[Pp]ro[Ee]tale|proEtale.*[Aa]djunction` returned 0.
Project grep located the exact public declaration above and the private construction;
WeilConjectures had no exact match. DAG definition-node grep found no owner for this
public adjunction. `blueprint_refs.py search 'module adjunction'` gave five general or
constant-coefficient results, none this specialization; `ancestor` reports None,
matching the consumer's existing technical-extraction ancestry. The raw service queries
and returned names are recorded in the new node's mathlib_searches. Since the Lean
notion already exists, the new record is `existing: true` with the same module; no
new definition or module is introduced.

## Repair of the returned findings

F1: replaced the bare conjugate-isomorphism condition by unit-compatible c and cs,
a row comparison σ pinned by product projections, its augmentation equation, and
its totalization τ pinned on all diagonal inclusions. Require Q(τ)=e in addition
to the normalized derived square. The proof docstring now explains how the epi-unit
identities force face compatibility, how products construct σ, and why summand
inclusions characterize totalization through the canonical interchange.

F2: unfolded all four aliases to the recorded definition interfaces throughout the
module and removed the alias-only tensor theorem dependency. Added the definition-node
record above for the existing canonical adjunction and removed the helper-only
projection theorem dependency. The underlying adjunction declaration remains identical;
its section-normalization theorem determines unique data. No dependency node or
upstream module was changed.

## Second reading by NX

The repair was read again against the node and the Lean source. This is the required
self-check; no additional agent was started. The nine original geometric/coefficient
hypotheses are retained with exactly their earlier meanings, including morphism
quasi-compactness of the complementary opens. The row support, signed differential,
actual singleton-unit augmentation, finite-total sign, bounded-below quasi-isomorphism,
ordinary derived natural isomorphism and signed refinement clauses are retained.
The coefficient and module binders are now spelled with the existing definition
interfaces; this changes no universes and no mathematical objects.

For the repaired pullback clause, inspected the full types of c and every cs and
both unit equations. The source and target intersection objects are exactly the chosen
finite products in the appropriate over categories. The projection equation has the
same t on both sides, and its right side uses precisely cs indexed by that tuple's
image; there are no unmentioned permutations or scalar factors. The augmentation
square uses c for Z, rather than replacing c by an arbitrary natural map. The total
square is checked on every summand of every diagonal and uses σ at horizontal degree
p and input K.X q. Its differential is still the previously checked total differential.
The final derived equality refers to this particular τ; the old unconstrained
conjugate e cannot supply σ or satisfy the summand equation on its own. Every datum is
asserted by the theorem and never selected from its sorry in any definition.
The new definition-node record was reread against the actual public adjunction and
its unique section-normalization helper; it is an exact reuse, not a different
adjunction or a theorem substituted for the resolution claim.

Validation: `scompile.py NX lem-sfb-finite-closed-cover-resolution
lean/Sheaf/AlgebraicGeometry/FiniteClosedCoverResolution.lean` passed both the sandbox
(28.9 seconds) and actual library-module (30.1 seconds) compilation with no diagnostics.
Only the original main theorem proof is `sorry`. The product-component formula is
expressed as an equality of natural transformations, so no copied module-category
alias or objectwise expansion is needed. The 60-second file timeout was not raised.
