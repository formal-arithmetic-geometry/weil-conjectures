## What changed

Constructed `etaleSectionShortComplex` explicitly from an arbitrary nonnegative complex
of abelian étale sheaves. The construction maps the complex through evaluation, forms
the biproduct restriction pair and difference, and proves their composite is zero
using functoriality and `Scheme.homOfLE_ι`. Its data contain no holes.

Replaced the original hole by a complete Lean assembly on chosen injective resolutions.
The proof obtains exactness degreewise, applies Mathlib's
`HomologicalComplex.shortExact_of_degreewise_shortExact`, proves that the inverse-image
opens cover Y, and obtains the simultaneous homology comparisons on these same fixed
complexes. Existing statements and the target signature are unchanged. The node's
proof and dependencies now describe this assembly.

Separated degreewise injective section exactness and fixed-resolution Ext comparison
into their own modules. Subsequently proved degreewise exactness completely using
sheaf amalgamation and injective extension along the free lifted-Yoneda sheaf mono. This is a decomposition, not a completed
sorry-free proof of the mathematical theorem. The remaining comparison lemma has no cover
hypothesis and asserts no exactness; the exactness lemma involves only one injective
degree and asserts no cohomology comparison or cross-scheme morphism.

## Proved and sorry left

Closed the item's single hole:
`AlgebraicGeometry.Etale.etale_mayerVietoris_section_diagram`.
There are no remaining sorries in the item's module or in the explicit construction module.

Proved `AlgebraicGeometry.Etale.etaleSectionShortComplex_degreewise_shortExact`
with no holes, including all private helpers.

Added exactly one hole:

- `AlgebraicGeometry.Etale.etaleSectionShortComplex_pullback_comparison`, node
  `lem-weil-pbc-etale-mayer-vietoris-section-comparison`, in
  `Sheaf.AlgebraicGeometry.EtaleMayerVietorisSectionComparison`.

The count is one upper hole closed, one strictly smaller hole added: net 0.
The explicit section complex and its injective degreewise exactness are now proved.
All four modules compile locally. The remaining proof obligations are recorded as public
named theorems with their complete natural-language arguments. The edge cases are empty
opens, both opens equal to X, and identity pullback. The degreewise theorem needs only
injectivity of I.X q; other terms can be arbitrary. The comparison theorem is valid
without a cover and for any pair of prescribed injective resolutions: use a comparison
over the augmentations, rather than assuming two unrelated cohomology identifications
are compatible. Preimage of the intersection is identified by preservation of infima.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit`.
- `Sheaf.CategoryTheory.InjectiveSheafCechAcyclic`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.

The first and third now belong to the comparison statement's proof plan and imports.
`Sheaf.CategoryTheory.InjectiveSheafCechAcyclic` is no longer used by this delivery.
The last two already enter through the unchanged public `EtaleOpenCohomologyMaps` import.
No module is claimed to leave the full targets' import closure.

The original fifteen direct proof-dependency edges are replaced by the three explicit
construction/exactness/comparison nodes and the three existing resolution-existence
nodes used in the assembly. The original K-injective, restriction, composition,
and unit dependencies are retained where needed in the one unfinished comparison argument;
they are not advertised as pruned mathematical work. The Cech route is pruned:
`lem-weil-pbc-injective-sheaf-cech-acyclic` and `def-weil-pbc-cech-complex`
are no longer needed by this node's proof. `lem-weil-pbc-open-fibre-product` is
also no longer needed for exactness: Mathlib supplies `isPullback_opens_inf`.
These nodes may remain reached by other users; no global closure removal is claimed. No unit statement or realized
unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned proof has no existing declaration giving the
compatible section diagram in one application. `EtaleMayerVietorisExact` gives derived
evaluation exactness; `EtaleMayerVietorisComparisons` gives isomorphisms without these
six simultaneous Ext map identities. Mathlib's `MayerVietorisSquare.shortComplex_shortExact`
is a short exact sequence of free abelian sheaves; it is not directly the degreewise
section sequence of the prescribed resolution.

Read [Stacks Tag 0A50](https://stacks.math.columbia.edu/tag/0A50), including the injective
section sequence and its passage to complexes. Searched the library and DAG for 0A50,
section complexes, Mayer–Vietoris, and compatible maps; blueprint search returned zero
matching imported nodes. LeanFinder found the generic MayerVietorisSquare results;
Loogle did not recognize `Functor.mapHomologicalComplex` in its remote index, so its
local source definitions were used. LeanSearch returned Internal Server Error and is
recorded unavailable, without a verdict. Grep confirmed the existing generic site and
topological statements but no duplicate of the new fixed-complex declarations.

## New nodes

`def-weil-pbc-etale-mayer-vietoris-section-complex`: actual evaluation complexes and
restriction maps, assembled into the diagonal/difference short complex. Its defining
zero-composite proof is complete Lean. Module:
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisSectionComplex`.

`lem-weil-pbc-etale-mayer-vietoris-injective-sections-exact`: exactness of one degree,
with only that term required to be injective. It separates the sheaf equalizer and injective-extension
surjectivity argument from all cohomology identifications. Its proof and all private
helpers are complete. Module:
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisInjectiveSectionsExact`.

`lem-weil-pbc-etale-mayer-vietoris-section-comparison`: comparison on the explicitly
fixed section complexes of any given injective resolutions. It needs no covering
hypothesis and makes no short exactness assertion. Module:
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisSectionComparison`.

No change record is needed: no existing statement or definition was changed.


## Second reading by Y2

1. Compared the only existing delivered module with the repository by diff and
   separately compared its declaration header byte for byte: unchanged. The diff
   changes proof imports and replaces the proof body only. The other three modules
   are new. No existing definition or target statement changes; no change record
   is required.
2. Compiled all four modules in import order through lcompile.py: clean, no errors
   or warnings. Searched all delivered Lean for forbidden declarations and holes:
   exactly the reported public comparison theorem has sorry. Added a scratch
   #print axioms probe for all three construction declarations, degreewise
   exactness, comparison, and the original theorem. The constructions and exactness
   use only propext, Classical.choice and Quot.sound; comparison and the original
   theorem additionally use sorryAx, as expected. Removed the scratch probe.
   Reviewed the injective extension through the free lifted-Yoneda sheaf mono,
   sheaf amalgamation pullback, signs, and evaluation biproduct isomorphism.
   No arbitrary witness from an unproved existence theorem supplies constructed data.
3. The comparison is a genuine proper part of the argument: its complexes are fixed
   by explicit definitions, it assumes given resolutions, has no cover hypothesis,
   and asserts no short exactness. Exactness is independently proved, not delegated
   to that hole. The docstring explains the augmented comparison, constant-sheaf
   cocycle identifications, and restriction/unit compatibility. Empty opens give
   zero groups; U=V=X gives the diagonal/difference sequence; identity pullback
   between different resolutions uses their comparison, not an assumed identity.
   Degreewise exactness requires injectivity only at q. Checked Stacks Tag 0A50
   directly (https://stacks.math.columbia.edu/tag/0A50). Repeated searches using
   homology of evaluated injective resolutions and Ext from the constant integer
   sheaf. LeanFinder found InjectiveResolution.extAddEquivCohomologyClass, a useful
   component but not these six simultaneous identities. Loogle's index did not
   know InjectiveResolution. Grep and local reading found the proved natural
   EtaleSheafHExtDerivedComparison and the still-open AbelianDerivedGlobalExtPullback;
   neither supplies the fixed complexes and all open/cross-scheme comparisons.
   No duplicate or quick complete proof of the comparison was found.
4. The top proof explicitly chooses resolutions, proves cover preservation and
   degreewise exactness, then combines the comparison; it is a decomposition with
   net zero holes, not a sorry-free proof. Checked sk-thm-p1.json realized: none
   of its statement or realized steps is bypassed. Removed redundant public
   RightDerived from the construction module and placed it in the comparison
   module, whose signature explicitly uses InjectiveResolution. Made
   HomologicalComplexAbelian private in the exactness module and imported it
   privately in the assembly, which uses its degreewise short-exactness lemma.
5. All four node Lean signatures occur verbatim in their files. For each node,
   proof_deps is exactly the union of proof-step uses. Read the construction,
   degreewise, comparison and assembly plans against the code; verdict: agree.
   The new nodes carry sources, search records, creation records, blueprint
   provenance, chapter/unit, and Lean records. The remaining comparison plan
   describes the one open theorem; exactness is fully implemented.

Changes by the second reader: import visibility and placement as above; corrected
an obsolete report reference to two unfinished lower arguments; completed the
explicit accounting below of every removed original dependency. No proof or
statement needed mathematical repair.

Additional accounting for **No longer needed**: the original direct proof edges
removed are lem-weil-pbc-dplus-injective-representative,
lem-weil-pbc-kinjective-hom-derived, def-weil-pbc-inverse-image,
def-weil-pbc-abelian-etale-sheaves, lem-weil-pbc-injective-sheaf-cech-acyclic,
def-weil-pbc-cech-complex, lem-weil-pbc-open-fibre-product,
def-weil-pbc-direct-image, lem-weil-pbc-etale-inverse-image-restriction,
lem-weil-pbc-inverse-image-composition, def-weil-pbc-cohomology-pullback,
and lem-weil-pbc-open-restriction-pullback-unit. The definitions and comparison
facts remain used through the new lower nodes or public statement imports;
only the Cech route and the separately stated open-fibre-product lemma are
mathematically pruned from this proof. Also removed the redundant direct
Mathlib.CategoryTheory.Abelian.RightDerived import from SectionComplex;
it is retained in SectionComparison for its public signature. No whole module
is claimed pruned from the targets' closure.
