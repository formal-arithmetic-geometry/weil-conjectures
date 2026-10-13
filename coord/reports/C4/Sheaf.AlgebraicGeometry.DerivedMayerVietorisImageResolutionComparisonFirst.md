## What changed

Replaced the sorry in AlgebraicGeometry.schemeMV_image_resolution_comparison_first by a
complete proof from ordinary open chain squares. The proof represents the normalized derived
map by a chain map into the fixed K-injective resolution J, using Mathlib
CochainComplex.IsKInjective.Qh_map_bijective and fullness of the homotopy quotient.
It then assembles the middle component using F.mapBiprod and biprod.map, proves both
short-complex squares by the two projections/inclusions (including the minus sign), and
cancels the resolution isomorphisms to prove the required localized first-component equation.
The private resolution_map_surjective helper reuses the argument of the already proved
private derived_map_surjective in DerivedMayerVietorisFunctorial without importing that
upstream module, which would introduce a cycle.

Added the proof-only import Sheaf.AlgebraicGeometry.MayerVietorisDirectImageChainSquares.
That new module isolates the ordinary sectionwise geometry: four unit/restriction squares
for a supplied chain map between arbitrary complexes. It has no derived category,
K-injectivity, resolution, cover, or localization equation. Updated the item's DAG proof,
proof_deps and proof_origin to the implemented route. Existing signatures and visibility
are unchanged. No definitions or other existing modules are adapted.

## Proved and sorry left

Closed: AlgebraicGeometry.schemeMV_image_resolution_comparison_first
(node lem-pc-mayer-vietoris-image-resolution-comparison-first).
The item's module now has zero sorries; its private resolution_map_surjective is proved.

Added: AlgebraicGeometry.schemeMV_directImage_chain_squares
(node lem-pc-mayer-vietoris-direct-image-chain-squares), in the new module
Sheaf.AlgebraicGeometry.MayerVietorisDirectImageChainSquares. Its proof is exactly by sorry;
its docstring and node contain the sectionwise construction and proof of all four equations.
This is a decomposition: one upper hole closed, one strictly simpler ordinary geometric
hole added, net zero holes. It is not a claim of an unconditional sorry-free proof.
The new statement supplies neither a derived representative nor the full short-complex map:
those steps and the normalized equality are proved in the item's module.

## No longer needed

No existing import was removed and no existing planned node was pruned. Both public imports
of the item's original signature remain necessary. The new module uses only the public
KInjectiveMayerVietorisData import, whose public dependency closure supplies ordinary direct
image. No exactness, cover, connecting-map compatibility, or intersection normalization
module is imported for this proof. These were not proof dependencies of the assigned node,
so this delivery claims no global pruning of them.

## Where the brief, the DAG or earlier work was wrong

The assigned node's single proof step cited only the canonical data definition. Those data
do not include the ordinary chain-level open comparison squares needed to extend a supplied
map to a map of short complexes. The missing geometric step is now stated separately; the
chain-map representation and biproduct assembly are actual Lean proofs.

The local literature/stacks-project/cohomology.tex is absent. Read the official Stacks
pages https://stacks.math.columbia.edu/tag/08BV and
https://stacks.math.columbia.edu/tag/08FE. The latter's underived sectionwise identity and the
former's displayed complex justify the ordinary geometric reduction. The new statement
was checked on empty opens, repeated opens, empty schemes, zero complexes, and the zero
chain map: each uses the same natural restrictions, and requires no cover or injectivity.
The given intersection K-injectivity instance is retained unchanged in the original
signature but is not used by this first-component argument.

LeanSearch returned Internal Server Error; this is recorded as unavailable. Loogle found
Qh_map_bijective. LeanFinder returned restriction/gluing lemmas but no exact chain-square
statement. Repository searches located same-scheme concrete_map (private) and the
homotopy-only underived counit square, neither of which gives the required chain squares.
Blueprint searches for Mayer Vietoris and Mayer--Vietoris returned no matches. The ancestor
script returned None for this recently split node; following the recorded canonical-data
blueprint reference identifies lem-pc-rf-perfect-base-change as the existing blueprint
ancestor. The unit record has empty realized statement and step lists; no unit step or
statement is bypassed or modified.

## New nodes

lem-pc-mayer-vietoris-direct-image-chain-squares is the ordinary comparison for the three
open terms and four squares of a supplied chain map. It extracts just the geometric part
of Tags 08BV and 08FE, leaving localization fullness, biproduct construction, both
short-complex identities and resolution cancellation proved above it. Its module imports
no upper Mayer--Vietoris theorem, so it introduces no dependency cycle. The node is in
dag/nodes/sec-picard-framework/lem-pc-mayer-vietoris-direct-image-chain-squares.json.
No change record is needed because every existing signature and definition is unchanged.

## Second reading by C4

1. Interface: compared the complete diff against the read-only repository and separately
   compared the existing theorem signature byte for byte: identical, including all four
   derived-category instance binders, E, the intersection K-injectivity assumption, and
   the normalized first-component conclusion. The only existing-module changes are a
   plain proof import, a private proved helper, and the target proof. There are no
   definition changes or forced adaptations. Verdict: pass.

2. Proof and axioms: compiled both delivered modules in import order with lcompile.py;
   both compile without warnings. Independently compiled scratch copies with explicit
   #print axioms for the target, the private resolution_map_surjective helper, and the
   new chain-square theorem. The helper uses only propext, Classical.choice, Quot.sound;
   the target and new theorem also use sorryAx, as expected from the recorded open
   geometric lemma (and existing open dependencies). Exactly one textual sorry remains,
   the whole proof of schemeMV_directImage_chain_squares. No prohibited declaration,
   hollow definition, or arbitrary witness chosen into a definition occurs. In the helper,
   quotientCompQhIso conjugates the desired morphism before Qh_map_bijective is applied;
   fullness produces f and naturality gives Q(f)=phi. Both short-complex equations were
   read: the second summand's negative restriction follows from congrArg Neg.neg hd,
   Functor.map_neg, comp_neg and neg_comp. The final cancellation has the correct order
   eI.hom;Q(f);eJ.hom. Verdict: pass, conditional decomposition, net zero holes.

3. Split statement: read the new module, its node, KInjectiveMayerVietorisData,
   DerivedOpenRestrictionMaps, and DerivedMayerVietorisOpenCounitModel. Read Stacks
   https://stacks.math.columbia.edu/tag/08BV (displayed ordinary section sequence) and
   https://stacks.math.columbia.edu/tag/08FE (underived restriction identity in its proof).
   The new statement is the ordinary natural comparison for a supplied f, not the
   original resolution/localization existence statement. In degree n on B, its a map is
   f_n evaluated on B intersect U, after identifying inverse-image intersections;
   similarly b and c evaluate on B intersect V and B intersect U intersect V.
   Units are restrictions by Scheme.Modules.restrictAdjunction_unit_app_app; the nested
   restriction mate reduces by restrictAdjunction_counit_app_app and the composition
   comparison. Naturality of f proves each of the four equations, and naturality of
   these comparisons with differentials makes the maps chain maps. Empty U or V makes
   the corresponding open term zero; repeated opens gives identical restrictions;
   full opens gives the ordinary f; zero f gives zero components; disjoint opens gives
   zero intersection. No cover or K-injectivity is needed for any of these cases.
   Its docstring supplies this construction and proof, with source and matching node.
   Independently searched with msearch LeanFinder for pushforward/restriction and unit
   naturality, Loogle for Qh_map_bijective, and grep for pushforward/restrict; read the
   returned Mathlib section formulas. Searched repository open-image comparisons and
   the upstream AlgebraicGeometry/CategoryTheory sources for MayerVietoris names.
   No existing theorem supplies these four chain identities. The existing underived
   counit square is only homotopy-level, and concrete_map is same-scheme and private in
   a module downstream of this item. Closing the new hole requires formalizing the
   transported section identifications, not a short application of a found lemma.
   Verdict: true, strictly smaller, needed; retain the single split-off hole.

4. Route and pruning: the proof starts with Mathlib K-injective localization fullness,
   then uses only the supplied ordinary geometric lemma, biproduct identities and iso
   cancellation. It does not invoke an extra open theorem of exactness or connecting-map
   compatibility. Both old public imports supply signature declarations (canonical data
   and derivedModuleDirectImageKInjectiveIso); the new import is plain because it is
   used only in the proof. The new module's public KInjectiveMayerVietorisData import
   supplies its signature. The old proof_deps contained only the canonical-data node,
   which is still used: no old node is unreported as pruned. Read the unit record
   sk-thm-picard-semicon: its realized statement and step lists are empty; the surrounding
   finite-cover Mayer--Vietoris route is retained. Verdict: pass; pruned none.

5. Nodes: checked the old/new JSON fields; the existing node changes only proof,
   proof_deps and proof_origin. Its three steps follow respectively the resolution
   representative, ordinary chain-square/biproduct assembly, and cancellation. The
   Mathlib leaf lem-sc-kinjective-quasi-iso-comparison states exactly Qh_map_bijective.
   The split-triangle node supplies the named comparison definition used in the
   signature and cancellation, not an application of its larger triangle theorem.
   The new node's statement matches every binder and all four conjuncts of its Lean
   statement; source, complete proof, dependency union, searches, creation, blueprint,
   chapter, unit and verbatim Lean record are present. The open-counit-model dependency
   supplies actual underived isomorphisms, not its still-open counit theorem.
   Verdict: pass.

Second reading changed: added this independent review and recorded additional searches;
no Lean proof, signature, import, or node repair was necessary. Holes closed and added
remain exactly the two declaration names in Proved and sorry left above.
