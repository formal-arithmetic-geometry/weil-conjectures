## What changed

Proved `AlgebraicGeometry.Scheme.fullAffineEtale_cohomology_comparison_data`, the sole
remaining hole in the fetched baseline. Added the proved private theorem
`affineEtale_free_restriction`. The latter identifies the affine free representable
with the restriction of the small-site free representable using the inverse equivalence
adjunction, the existing sections equivalences, and fully faithful coyoneda.

Restriction is additive and an equivalence, hence exact, fully faithful, and injective
preserving. Mathlib's `Functor.mapExt_bijective_of_preservesInjectiveObjects` gives
bijective maps on Ext. Composing with precomposition by the representing-object isomorphism
gives additive equivalences, natural by Ext product associativity. Invert these natural
isomorphisms to obtain the direction in the original statement. Enough injectives is
supplied by Mathlib's existing Grothendieck-abelian instance for the small etale site
and its enough-injectives instance. No new existence obligation or chosen data definition is used.

Added three proof-only imports: Ext.MapBijective, GrothendieckCategory.EnoughInjectives,
and the source's Ext precomposition bridge. The second reader removed the unnecessary
essentially-small sheaf Grothendieck-category bridge import. Existing public imports and all signatures
are unchanged. The unused-variable linter is disabled only for the comparison-data
theorem because its existing signature explicitly binds an existential e followed by True.
Updated that theorem's existing DAG node to describe the direct Ext argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.fullAffineEtale_cohomology_comparison_data`
(node `lem-weil-pbc-affine-etale-cohomology_comparison_data`).
No sorry remains in the item and no holes are added. The private representing-object
helper is fully proved. Net holes closed minus added: 1.
The other declarations had already been proved in the fetched baseline and are preserved.

Edge cases: the empty affine and zero sheaf are handled by the same Hom and Ext
constructions; the section-representing isomorphism requires no nonempty object or
section. Every naturality identity holds for arbitrary sheaf morphisms and every degree,
including zero. HasExt universes remain exactly w on both categories.

## No longer needed

No baseline import is removed. The second reader removed the first worker's added
`WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` import;
existing Mathlib instances suffice. No baseline module is claimed pruned. The original proof's explicit injective-resolution
construction, lifting and homotopy comparison are unnecessary: the corresponding Ext
map is Mathlib's already proved exact-functor map, and its bijectivity is Mathlib's
injective-preservation theorem. Thus the direct dependency
`lem-weil-pbc-equivalence-injective-resolutions` is removed from the comparison-data node.
No unit step or unit statement is bypassed; the proof still transports cohomology along
the restriction equivalence and preserves the source's sections functors.

## Where the brief, the DAG or earlier work was wrong

The initial local clone was stale: it showed ten holes and an incorrect universal
normalization statement for arbitrary comparison isomorphisms. The first dry run fetched
the newer baseline, which had already fixed that statement and proved all declarations
except comparison-data. The sandbox was rebased to this current baseline, preserving
all those proofs, corrected interfaces and private helpers. The tentative initial
assembly from the old false normalization statement is absent from this delivery.

Mathlib search: LeanFinder searched restriction continuity; Loogle found
Functor.mapExt_bijective_of_preservesInjectiveObjects; source grep located the
source's Ext.precompAddEquiv and essentially-small Grothendieck-abelian bridge.
Their signatures were read and used directly. All new imports pass import_direction.py.
The direct proof avoids the unnecessary Ext-versus-resolution bridge suggested in
the old comparison-data docstring; that existing docstring is preserved as API.

## Second reading by A3

1. PASS: compared the sole delivered Lean module against the repository with `diff -u`
   and the stage-3 declaration parser. Every existing signature is byte-for-byte
   unchanged; no declaration, definition, visibility or public import is changed.
   Only the comparison-data proof, its local linter setting, three private imports,
   and the fully proved private representing-object helper are added. Read the landed
   comparison-point change record; its corrected baseline statement is preserved.
2. PASS: compiled the final module through `lcompile.py` without errors or warnings.
   A scratch copy printed axioms for all 27 declarations, including private definitions
   and helpers: only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There is no remaining `sorry`, forbidden declaration, hollow definition or data
   chosen from an unproved existence assertion. The representing-object witness is
   obtained from a fully proved theorem inside a proposition proof.
3. PASS: no split-off statement and no new hole. Read the new private helper top down:
   the inverse adjunction and the sections equivalences produce the correct natural
   Hom isomorphism, coyoneda reverses its direction, and the counit gives the desired
   representing-object isomorphism. It needs neither a nonempty affine nor a nonzero
   sheaf. The Ext argument applies in every degree, including zero, with the original
   HasExt universes. Independent Loogle search confirmed Mathlib's Ext bijectivity
   theorem; source searches found only global-H transport helpers, not a shorter
   objectwise H' comparison that would replace this argument.
4. PASS after simplification: Mathlib already supplies the Grothendieck-abelian
   small-etale-site instance, so enough injectives synthesizes directly. Removed
   `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` and the
   manual affine-site transport. The three remaining added imports each supply a used
   result. Baseline imports remain used. The sole old proof dependency removed is
   `lem-weil-pbc-equivalence-injective-resolutions`, listed above; no baseline module
   is claimed pruned. Read `dag/units/sk-thm-p1.json`: none of its realized statement
   or step nodes is bypassed. This change is below that unit's route.
5. PASS: the sole delivered node differs only in `proof`, `proof_deps`, and
   `proof_origin`. Its steps describe the helper, enough injectives, Ext bijectivity,
   and naturality; `proof_deps` is precisely the union of the steps' `uses`.
   The small-etale-site Grothendieck instance uses the recorded affine-site sheaf
   equivalence internally, so that dependency remains. No new node is needed.

Changed on second reading: removed the unnecessary Grothendieck-category bridge
import, replaced six lines of manual enough-injectives transport with existing instance
synthesis, and corrected the node's proof narrative and this report to match.
