## What changed

Proved AlgebraicGeometry.etaleCohomology_localRing_colimit with its complete original
signature, including the specified cocone legs, uniqueness of local-scheme factorizations,
and eventual vanishing. The public imports of the original module are unchanged.

One new obligation, AlgebraicGeometry.etaleOpenObjectCohomology_natural, isolates steps
1-2 of the original argument. It gives the natural comparison on all opens but asserts
no local-scheme continuity or vanishing. The main proof conjugates the supplied diagram
by d followed by this comparison and constructs the canonical pullback cocone.

The second new module proves AlgebraicGeometry.etaleRestrictedCohomology_neighbourhood_colimit
from the existing fixed-base cohomology continuity theorem. It restricts to the full
subcategory of affine neighbourhoods, obtains its cofilteredness and initiality from
the affine basis, packages the stated affine-neighbourhood limit as an IsLimit, applies
nonempty_isColimit_cofiltered_fixed_base_cohomology, and transfers the result back by
Final.isColimitWhiskerEquiv. No new continuity sorry is introduced.

Mathlib fromSpecStalkOfMem gives the factorizations, cancellation of open immersions gives
uniqueness, the existing triangle laws give compatibility of cocone legs, and Mathlib's
Concrete.isColimit_exists_of_rep_eq gives eventual vanishing. The smaller index universe
requires explicitly shrinking the filtered-colimit preservation instance for the forgetful
functor of AddCommGrpCat.

## Proved and sorry left

Proved the original module's sole sorry:
- AlgebraicGeometry.etaleCohomology_localRing_colimit
  (lem-weil-pbc-etale-cohomology-local-ring-colimit).

Also proved the new theorem:
- AlgebraicGeometry.etaleRestrictedCohomology_neighbourhood_colimit
  (lem-weil-pbc-etale-restricted-cohomology-neighbourhood-colimit).

The only sorry in the delivered files is:
- AlgebraicGeometry.etaleOpenObjectCohomology_natural
  (lem-weil-pbc-etale-open-object-cohomology-natural).

The existing theorem AlgebraicGeometry.Etale.nonempty_isColimit_cofiltered_fixed_base_cohomology
remains an imported obligation (lem-weil-pbc-cofiltered-fixed-base-cohomology-continuity).
The affine-neighbourhood scheme-limit theorem remains an imported obligation
(lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods). They are existing stage-3
items, not new sorries. The triangle-law theorem used here is already proved.

## No longer needed

Removed these direct imports from the original module:
- Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
- Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
- Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
- Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
- Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit
- Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
- Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

The direct proof no longer needs the original nodes
prop-weil-pbc-kinjective-resolutions-exist,
prop-weil-pbc-cohomology-resolution-independent, or
lem-weil-pbc-derived-inverse-image-composition. All groups and maps use their existing
Ext encodings; an additional K-injective comparison is unnecessary for this argument.
The natural comparison obligation uses Ext via injective resolutions directly.

The original continuity and cofinality dependencies are retained below the proved
neighbourhood-continuity specialization, chiefly through the existing fixed-base
continuity theorem. OpenRestrictionPullbackUnit and the inverse-image restriction
comparison are retained in the proof plan of the remaining comparison obligation.
The general canonical-morphism properties are not used to construct g: Mathlib already
provides its open-neighbourhood factors. SpecStalkLimitAffineNeighbourhoods still imports
that module; this delivery does not alter its transitive imports or claim global pruning.
No node realizing a unit statement or unit proof step is bypassed.

For completeness, the following old direct proof dependencies are now used below
one of the two new lemmas rather than directly in the main theorem:
- lem-weil-pbc-open-immersion-etale
- lem-weil-pbc-cohomology-pullback-functorial
- lem-weil-pbc-etale-inverse-image-restriction
- lem-weil-pbc-inverse-image-composition
- lem-weil-pbc-open-restriction-pullback-unit
- lem-weil-pbc-open-fibre-product
- lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods
- lem-weil-pbc-etale-cohomology-limit-of-schemes
- lem-weil-pbc-colimit-constant-connected-diagram
- lem-weil-pbc-colimit-initial-full-subcategory

The definition nodes def-weil-pbc-etale-site, def-weil-pbc-sites-and-cohomology,
def-weil-pbc-etale-cohomology, def-weil-pbc-inverse-image,
def-weil-pbc-cohomology-pullback and def-weil-pbc-category-colimit remain the
statement vocabulary; removing their old direct proof-plan entries does not replace
any definition. The old direct proof dependency
lem-weil-pbc-spec-local-ring-canonical-morphism is pruned in favor of Mathlib's
Scheme.Opens.fromSpecStalkOfMem and fromSpecStalkOfMem_ι; the node remains a
statement dependency and is also reached transitively from the affine-limit module.
Together with the three pruned proof nodes above, this accounts for every old
proof_deps entry removed from the main node. No global unreachability is claimed.

Second reading also removed the redundant newly added direct import
Mathlib.AlgebraicGeometry.Stalk; its declarations are already available through
the retained imports.

## Where the brief, the DAG or earlier work was wrong

The original docstring cited clause (5) of cohomologyPullbackFunctorial to preserve
injectives. Its actual Lean statement has three clauses (naturality, composition,
identity); it supplies no such clause. The remaining comparison obligation instead
states the missing object/open comparison explicitly, with the injective-resolution
and exact-extension-by-zero proof in its docstring and node.

STATEMENT-DISPUTED: AlgebraicGeometry.etaleCohomologyOverOpen in
Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen compares H^q(X,G) with H^q(U,G|U), rather
than object cohomology over U with cohomology on U. It therefore cannot supply the
comparison here. For X the disjoint union of two separably closed points, U one component,
and the constant integer sheaf, its degree-zero assertion would identify Z x Z with Z.
This unrelated module is neither imported nor changed by this delivery; its declaration
needs separate correction. The new comparison has the actual object-cohomology presheaf
P as its source and passes this edge-case check.

Checked the source online because the local literature directory lacks the .tex files:
https://stacks.math.columbia.edu/tag/03F3 (injective resolution restricted to an object),
https://stacks.math.columbia.edu/tag/03Q6 (continuity), and
https://stacks.math.columbia.edu/tag/09AX (the local-ring stalk colimit).
LeanSearch returned an internal server error and is recorded as unavailable, not as a
negative result. Loogle, Lean Finder, and repository/Mathlib searches supplied no direct
natural object/open comparison. The existing localized-object comparison has different
universe assumptions and no compatibility with cohomologyMap; it is not a substitute.

Edge cases checked: degree zero; zero coefficients; disconnected X with U one component;
the empty open in the natural comparison; non-quasi-separated X (only affine stages need
qcqs hypotheses); arbitrary diagram presentations d; and the empty scheme, where no x
exists. The two new statements impose no extra hypotheses on X or F.

## New nodes

lem-weil-pbc-etale-open-object-cohomology-natural records the sole new sorry, the natural
comparison of object cohomology with cohomology of inverse images on opens. It is strictly
steps 1-2, without a point, local scheme, cocone, continuity, or eventual vanishing.

lem-weil-pbc-etale-restricted-cohomology-neighbourhood-colimit records a proved specialization
of existing fixed-base continuity to affine neighbourhoods and cofinal transfer. It
asserts the colimit property for supplied cocone data; the main module constructs those
data and proves the remaining clauses. Both nodes inherit sec-proper-base-change and
sk-thm-p1. No statement, definition, unit record, or target signature was changed, and no
change record is required.

## Second reading by B2

1. Compared the delivered original module with the repository using diff and extracted
   its theorem signature: byte-for-byte identical. All three original public imports
   remain identical, and no existing definition or statement changes. Verdict: pass.
2. Compiled all three delivered modules through lcompile.py in import order, with no
   errors or warnings. Inspected all proof bodies and private constructions: no hollow
   definitions or forbidden declarations; exactly one named sorry, as reported.
   Scratch-copy #print axioms checks for all three public theorems show only propext,
   Classical.choice, Quot.sound and sorryAx. The latter is expected from the comparison
   obligation and existing imported continuity/affine-limit obligations. Verdict: pass
   as a partial proof delivery, not an axiom-free completion of the target closure.
3. Read the new comparison statement, its complete docstring proof and node against
   Stacks Tags 03F3 and 09AX. It compares object cohomology, not cohomology of X, with
   restricted-sheaf cohomology and records the correct composition inverse. Checked
   q=0, zero coefficients, empty opens, and a disconnected X with U one component.
   The continuity specialization uses only qcqs affine stages, so non-quasi-separated
   X introduces no missing hypothesis; empty X has no point. Both statements are
   strictly parts of the original argument. Repeated Lean Finder search with
   "Ext from free abelian representable sheaf localization restriction natural
   isomorphism", Loogle with the qualified cohomologyPresheafFunctor name, and rg
   for localization/restriction and Ext. Mathlib's comparison is explicitly TODO;
   the existing localized-object theorem lacks the naturality and required universe
   specialization. No directly usable replacement was found. Verdict: pass; closing
   the comparison requires substantial Ext/adjunction work, not a short repair.
4. Read the proof top downward: Mathlib factors through opens and cancels monomorphisms;
   comparison naturality conjugates the transitions; proved triangle laws construct
   the cocone; affine cofinality reduces continuity to the existing fixed-base theorem;
   the filtered-colimit equality criterion proves eventual vanishing. Inspected the
   sk-thm-p1 realized statement and all four step lists: none is bypassed or changed.
   Original proof-only imports are pruned, all new proof imports are plain imports,
   and all removed old proof_deps are now explicitly accounted for. Verdict: pass.
5. Checked both new nodes' Lean statements verbatim, sources, creation fields, searches,
   and proof steps. The existing node's proof matches the Lean construction; repaired
   its unused canonical-morphism-properties dependency. The remaining dependency
   lists are unions of their steps' uses and distinguish new comparison, affine-limit,
   and fixed-base continuity obligations. Verdict: pass after the repair.

Changes in this second reading: removed the unused canonical-morphism-properties
proof dependency from the main node, completed the pruning inventory, and removed
one redundant Mathlib.Stalk import. No mathematical proof or theorem signature changed.
