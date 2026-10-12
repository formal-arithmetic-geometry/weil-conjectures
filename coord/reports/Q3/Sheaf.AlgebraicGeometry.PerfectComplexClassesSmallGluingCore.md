## What changed

Closed `AlgebraicGeometry.Scheme.perfectComplex_classesSmallOnOpen_union_core` with its
signature unchanged. The private `small_skeleton_of_triangle_terms` proves the categorical
part: code the second triangle arrow by two small endpoint skeletons and small Hom types,
then use rotation and Mathlib `exists_iso_of_arrow_iso` to prove injectivity into the small
range of encoded arrow classes. No cone object is chosen from an unproved existence theorem.

Added four modules. `PerfectGluingEndpointProperties` constructs derived direct image on a
localized open site using the actual right adjoint of restriction and defines the local
restriction, middle and overlap families. `PerfectGluingTrianglePresentation` is proved from
`schemeKInjective_mayerVietoris_presentation`: it constructs local derived categories in the
supplied universe, compares localized and scheme direct images by right-adjoint uniqueness,
and applies the actual short-exact-sequence triangle. `PerfectGluingEndpointsSmall` is proved
by mapping small local restriction skeletons through derived direct image and biproduct.
`PerfectRestrictionClassesSmall` isolates the remaining geometric transport argument.

All five delivered modules compile together, without warnings. The original theorem and
visibility are unchanged. No existing module is adapted. The route remains the original
restriction/Mayer--Vietoris/small-Hom/cone-uniqueness argument. The node's unit record has empty
`realized.statement` and `realized.steps`, so no unit-level step is bypassed.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Scheme.perfectComplex_classesSmallOnOpen_union_core`
(node `new-perfect-classes-small-gluing-core`), 1 of 1 original holes.

New proved declarations:
`AlgebraicGeometry.Scheme.perfectGluing_triangle_presentation`
(node `lem-perfect-gluing-triangle-presentation`) and
`AlgebraicGeometry.Scheme.perfectGluing_endpoints_small`
(node `lem-perfect-gluing-endpoints-small`). All private helpers are fully proved.
All five new definitions are real constructions or explicit existential properties.

Exactly one new sorry remains:
`AlgebraicGeometry.Scheme.perfectRestriction_classes_small`
(node `lem-perfect-restriction-classes-small`, module
`Sheaf.AlgebraicGeometry.PerfectRestrictionClassesSmall`). It concerns the restriction
image on a single open, with no direct images, gluing, triangles, or cone classification.
Its docstring and node give the proof, including transport of all further open-site
localizations, quasi-coherence and strictly perfect local models, and injection into a small
range. It is strictly part of the original argument, rather than that argument renamed.

This is a decomposition: one original hole closed and one lower hole added, net zero direct
holes. The triangle proof also uses the existing named presentation theorem, whose module
has its own sorry. That dependency is retained, not claimed proved here.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle`
(node `lem-pc-derived-mayer-vietoris-triangle`). The proof only needs its K-injective
short-exact presentation, now used directly by the proved localized triangle lemma.
Consequently this route does not require the extra assertions that the direct-image
endpoints are quasi-coherent: `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`
(node `lem-pc-derived-direct-image-preserves-qcoh`) and the private quasi-coherence helpers
of the former triangle module are unnecessary for this proof. Compactness and affine-open
hypotheses in the original signature are preserved, but the categorical gluing argument
and ambient triangle do not use them.

Removed the redundant public import `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
from `PerfectGluingEndpointProperties`; its definitions use no triangle API, and the
required biproduct and derived-category instances are available from the retained imports.

Removed the direct import `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` from the
core; its declaration/node `prop-pur-kinjective-resolutions-exist` remains used through the
new construction modules and the explicit local-smallness proof, so it is not pruned.
The open-restriction maps, scheme/ringed-space derived direct image, K-injective
Mayer--Vietoris presentation, injective restriction surjectivity, K-injective restriction,
and short-exact triangle dependencies remain needed. No claim is made that the removed
modules are globally unreachable through other targets.

## Where the brief, the DAG or earlier work was wrong

The named Mayer--Vietoris and resolution declarations by themselves do not supply smallness
of the restriction families or the passage from small endpoints to small global skeletons.
Those are now explicit, with the categorical passage fully proved. Smallness of Hom in
universe u is available from the source-library `DerivedCategory.locallySmall`, even when
the supplied localization has morphism universe w.

Using a triangle in the ambient derived category avoids the unnecessary quasi-coherence
of its direct-image terms. The localized construction also avoids assuming fresh
derived-category structures on open subschemes in universe w: these are constructed by
transport and morphism shrinking in the triangle proof.

The literature text is not installed in this clone. I read Stacks Tags 08BV and 08DR at
https://stacks.math.columbia.edu/tag/08BV and https://stacks.math.columbia.edu/tag/08DR,
and read the existing DAG source/proof records and Lean signatures. Tag 08BV gives the
ambient triangle for any two-open cover of a ringed space, without qcqs hypotheses.
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable, not as a
negative search. Lean Finder, Loogle and local searches ran; their results are recorded in
the sandbox search log and nodes. Blueprint searches for perfect complexes and
Mayer--Vietoris found no duplicate specialized endpoint or restriction-smallness statement.

Edge cases checked in the reasoning: empty opens, repeated opens, an identity open, and a
large supplied morphism universe w. The generic categorical proof does not assume an
inhabited perfect category; it indexes only the skeleton elements it is given. The endpoint
proof uses the restriction itself as its property witness and transports its actual
isomorphisms. The open-containment hypothesis in the new restriction lemma is essential
and explicitly stated.

## New nodes

`def-perfect-gluing-endpoint-properties`: the constructed localized derived direct-image
functor, its composite with restriction, and the three explicit endpoint properties in
`PerfectGluingEndpointProperties`. The derived right adjoint is determined up to natural
isomorphism by its adjunction; no arbitrary object witness or data sorry is used.

`lem-perfect-restriction-classes-small`: the sole new sorry, a single-open restriction-image
smallness theorem. Its complete proof plan is in the node and docstring, with containment
of that open in the immersion image, all further localized sites, and both geometric
properties addressed.

`lem-perfect-gluing-endpoints-small`: proved. The small source types are respectively a
product of two restriction skeletons and a third restriction skeleton. The private helper
proves smallness of the skeleton of any full subcategory covered by a small ambient family.

`lem-perfect-gluing-triangle-presentation`: proved from the existing short-exact presentation
and source resolution theory. Private helpers explicitly construct transported derived
categories and compare the two derived direct-image functors by their adjunctions.

All nodes are under `dag/nodes/sec-picard-framework/`. No change record is necessary:
no existing definition, statement, public import or visibility changes.

## Second reading by Q3

1. Compared the five delivered modules against the repository: only the core module
   already exists. Its complete theorem signature, visibility and docstring are
   byte-for-byte unchanged; its diff contains proof imports, a proved private helper,
   and replacement of the original sorry. No existing definition is modified and no
   forced adaptation or statement change is present.

2. Read all five files and compiled them in import order with lcompile.py --all:
   all compile without warnings. The only new hole is the named
   AlgebraicGeometry.Scheme.perfectRestriction_classes_small. There is no axiom,
   unsafe, opaque, extern, implemented_by, anonymous sorry or data sorry. The
   direct image uses the actual right adjoint; localization transport uses the
   canonical localization, not arbitrary data from mere existence. The private
   triangle helper injects the perfect skeleton into a small arrow-class range:
   rotate, apply exists_iso_of_arrow_iso, unshift by full faithfulness, and lift
   through the full inclusions. Thus its chosen triangles are proof-local witnesses,
   not definitions based on an unproved arbitrary choice.

3. Read the new declarations, their nodes, PerfectComplexClassesSmallOnOpen,
   IsPerfect, and schemeDerivedQCohProperty. The remaining restriction statement
   has the necessary W ≤ opensRange hypothesis; it reduces to pW on the composite
   open immersion. The supplied localizations must be transported on all further
   opens in the same morphism universe, as its docstring explicitly explains.
   Strictly perfect models restrict by intersecting neighbourhoods and preserving
   finite-free retract equations; exact restriction commutes with homology and
   transports quasi-coherence. A small open-scheme skeleton covers the restriction
   family, yielding the stated injection into its small range. This is a single-open
   subargument, strictly smaller than the gluing target. Empty opens, W equal to
   opensRange, repeated cover opens, and arbitrary w introduce no extra hypothesis.
   Independent LeanFinder search for essential smallness under equivalence and open
   restriction found only generic derived-category representatives, not this result.
   Loogle found Functor.mapSkeleton_injective, already used in the family helper.
   Local rg over lean/Sheaf and lean/WeilConjectures found no duplicate specialized
   restriction-smallness theorem. DerivedPullbackPerfect is still open and would
   also require restriction/pullback and quasi-coherence comparisons; it does not
   close this remaining theorem in a few minutes.

4. Read Stacks Tags 08BV and 08DR online and the unit record
   dag/units/sk-thm-picard-duality.json. 08BV gives the ambient triangle for any
   two-open cover, with no quasi-coherence requirement on direct-image terms;
   08DR is the induction principle, not a restriction transport theorem. The core
   preserves its compact/affine/quasi-separated hypotheses although this reduction
   does not use them. The old proof_deps consist of the Mayer--Vietoris triangle
   (now unnecessary and reported) and K-injective resolutions (still necessary and
   retained). No realized statement or step in the unit is bypassed. The new
   endpoint proof maps three restriction skeletons through actual functors, and
   the triangle proof applies the existing K-injective presentation; neither
   reintroduces the unused quasi-coherence-of-direct-image requirement.

5. Checked every node's proof steps, dependency union and Lean statement against
   the corresponding file. The target's new proof_deps match the endpoint,
   triangle and resolution uses. The triangle node retains the short-exact
   presentation, adjunction/restriction and resolution dependencies. New nodes
   carry source, creation, blueprint, search and Lean records. Corrected the
   definition node's ordinary mathematical composition order: J_W is
   R(G_W) composed with D(L_W), matching Lean's left-to-right functor composition.
   No Lean declaration changed. The decomposition closes one original hole and
   adds one lower hole, net zero; no complete axiom-free proof is claimed.

Second reading changed the definition node's composition notation, removed the
redundant public Pretriangulated import from PerfectGluingEndpointProperties, and
added this review. The other public construction imports are needed by the exposed
body of perfectGluingDirectImage (tested by demotion and restored after Lean rejected
the unavailable construction declarations). The delivery tool's axiom probe and preflight are the final verification.

Final verification: explicit #print axioms on all four public theorems and all
five new definitions compiled in scratchpad/lean/Axioms.lean. The definitions
use only propext, Classical.choice and Quot.sound; the four theorems also use
sorryAx from the named open restriction/presentation dependencies. The delivery
probe checks every declaration, including private helpers. The final dry run
passed compilation and preflight after removing the redundant import.
