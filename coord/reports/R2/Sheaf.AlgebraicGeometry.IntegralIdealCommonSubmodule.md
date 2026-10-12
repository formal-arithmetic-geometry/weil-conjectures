## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.IntegralIdealCommonSubmodule`
with a complete Lean assembly of two strictly smaller intermediate statements:
a rank-one generic ideal inclusion and a common generic lattice of two nonzero ideals.
The original signature and public imports are unchanged. Added only proof imports.
Updated lem-pc-a2-integral-ideal-common-submodule's proof, proof_deps and proof_origin.

The assembly composes the two monomorphisms and their generic isomorphisms, obtains
coherent cokernels from the existing coherent kernel/cokernel interface, derives their
finite presentation from finite affine sections and the affine criterion, and proves
strict support containment by surjectivity of cokernel projections on stalks. The
strictness witness is i(genericPoint W), at which both cokernels vanish. These
cokernel, finiteness and support arguments are complete Lean proofs, including the
private helpers finitePresentation_of_affine_sections and cokernel_support_ssubset.

Two new modules state the remaining generic-inclusion and intersection steps, each
as a public named theorem with proof exactly `by sorry`, a source, a complete proof in
words and a DAG node. No definition or target interface changed, and no data is chosen
from an unproved existence theorem.

Repair of the landing return at head 4448fd361: removed the duplicate private
`finitePresentation_of_coherent` theorem. The matching theorem in
`TwistedSectionsFiniteDimensional` is private, so it cannot be imported and used by
name. Generalized the helper in place to `finitePresentation_of_affine_sections`:
it assumes only quasi-coherence and finitely presented affine sections, with no
Noetherian or coherence hypothesis. This is a genuine generalization applicable
also to non-Noetherian schemes. The two cokernels satisfy its hypotheses by the
existing coherent affine sections theorem and Noetherian finite-presentation result.
All public signatures, imports and the two split-off statements remain unchanged.
The second-reading section below records the earlier reading; the repaired helper
and its applications require the next independent reading.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_integral_ideal_common_submodule`
(lem-pc-a2-integral-ideal-common-submodule).

Added two holes, and these are every sorry in the delivered files:

- `AlgebraicGeometry.Scheme.Modules.rank_one_generic_ideal_inclusion`
  (lem-pc-r2-rank-one-generic-ideal-inclusion).
- `AlgebraicGeometry.Scheme.Modules.integral_ideals_common_generic_lattice`
  (lem-pc-r2-integral-ideals-common-generic-lattice).

This is a decomposition, not a sorry-free proof: one upper hole closed and two
strictly smaller holes added. Existing imported interfaces can still depend on sorry.
Each new theorem is independently useful and only part of the original argument;
neither concludes anything about cokernels or proper support containment. The rank
inclusion assumes no global support or second ideal, and the intersection result
assumes no ambient module G or rank hypothesis. Their combination requires the actual
composition, cokernel, finite-presentation and support proofs written in the item.

## No longer needed

The original module had no proof-dependency imports, so none of its original public
imports was removed. The final proof excludes the exploratory imports of
`WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial`,
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`, and
`Mathlib.CategoryTheory.NatIso`.

The original direct proof-dependency nodes
`lem-weil-pbc-finite-type-module-support-closed`
(`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`) and
`lem-weil-pbc-quasi-coherent-ideal-intersection`
(Mathlib IdealSheafData.inf) are no longer needed in this proof or in the new
intermediate routes. Strictness follows without closedness; the real intersection
module is constructed as the kernel of I -> O_W/J, without the IdealSheafData
intersection bridge. Another target path may still reach these nodes; the maintainer's
closure ledger decides global pruning.

Other original dependencies remain needed mathematically by the new intermediate
nodes or the assembly, but the following cyclic proof imports are absent:
`Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion`,
`Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`, and
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`.
`Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk` also remains a mathematical
dependency of the new intersection and rank arguments, rather than a direct main import.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated a private coherence-to-finite-presentation theorem
already present in `Sheaf.AlgebraicGeometry.TwistedSectionsFiniteDimensional`.
The repair replaces it with the strictly more general affine-section criterion,
rather than renaming the same theorem or changing another module's visibility.


The stated plan's generic inclusion and finite-pushforward coherence interfaces cannot
be imported here in the current source graph. The dry run rejected this cycle:
IntegralIdealCommonSubmodule -> CoherentGenericPointIdealInclusion ->
CoherentGenericPointClosedDescent -> ClosedImmersionPushforwardAnnihilated ->
AffinePushforwardBaseChange -> DirectImage.AffineMorphism ->
DirectImage.FiniteFreeComplex -> IntegralIdealProperCohomology ->
IntegralIdealComparisonFiltrations -> IntegralIdealCommonSubmodule.
The import-direction tool separately rejects FinitePushforwardCoherent and the source
Modules.ClosedImmersion module because they also reach this item. No tool was bypassed
and no unowned module was adapted. The partial delivery isolates the two genuine
mathematical steps so they can be proved through lower-level interfaces without those
cohomological imports.

Before the import-graph dry run, a kernel construction of the intersection and its
maps compiled against the cached library, as did the assembly from a rank-only hole.
That code cannot be delivered with its cyclic imports. The final intersection docstring
and node record its precise kernel construction and exact generic-stalk proof; the
scratchpad retains that exploratory text for the second reader, outside the delivery.
The current proof-support graph is the final route, not that rejected import route.

No mathematical statement error was found. The planned support-closedness step is
stronger than necessary. Mathlib searches found no complete matching scheme-module
theorem. LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable.
The Stacks source was read at https://stacks.math.columbia.edu/tag/01YH,
`lemma-property-irreducible`, the rank-one and intersection paragraphs. The unit
sk-thm-picard-coherence has no realized node among these lemmas, and its route is
unchanged. Checked zero ideals, zero summand count, unit ideals and zero cokernels:
rank one rules out the first two, the lattice theorem excludes zero ideals precisely
by its hypotheses, and unit ideals and zero cokernels require no special treatment.

## New nodes

`lem-pc-r2-rank-one-generic-ideal-inclusion`, in
`Sheaf.AlgebraicGeometry.RankOneGenericIdealInclusion`: only the generic-inclusion
step for a coherent module with maximal-ideal-annihilated compatible rank-one stalk.
It outputs a nonzero ideal J and a mono i_*J -> G invertible at the generic point;
it cannot supply a common submodule with any second ideal or cokernel properties.
Its proof in words follows 01YE and the rank calculation in 01YH, with an explicit
note to avoid the currently cyclic cohomology import route.

`lem-pc-r2-integral-ideals-common-generic-lattice`, in
`Sheaf.AlgebraicGeometry.IntegralIdealsCommonGenericLattice`: the coherent intersection
and its two generic inclusion maps for two nonzero ideals, together with coherence
of i_*I. It knows no G or rank hypothesis and asserts no cokernel property. Its
kernel construction is real and its generic-bijection argument is specified fully.

Both nodes cite Tag 01YH and the original nearest blueprint ancestor
lem-pc-coherent-hi through the comparison and common-submodule nodes. Searches across
the imported blueprint for intersection, intersection ideal and rank one found no
existing blueprint statement of either new lemma. No change record is needed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered common-submodule module with the repository version. The existing theorem signature is unchanged; only its proof and proof imports changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py`. No forbidden declarations remain; the only `sorry`s are the two named split-off theorems, each with a public declaration, source, proof docstring, and DAG node. Verdict: pass.
3. Checked both split-off statements on the documented zero, unit, and generic-stalk edge cases and searched the library and Mathlib for duplicates. Each is a strict intermediate result needed by the assembly and neither weakens the target. Verdict: pass.
4. Reviewed the proof from the target downward. It uses the two split-off interfaces, coherent cokernel closure, affine finite-presentation criteria, and stalk exactness; unused exploratory and cyclic imports are removed and listed above. Verdict: pass.
5. Compared the main node's `proof`, `proof_deps`, and `proof_origin` with the delivered Lean proof, and checked both new nodes' metadata and the unit route. They agree and the unit route is retained. Verdict: pass.

Changed during second reading: added this required review section only; no Lean statements, definitions, proofs, imports, or DAG records were altered.

## Second reading by R2

1. Compared the delivered main module with the repository version. The target theorem signature and all existing declaration signatures are unchanged; the two additional modules contain only the named split-off declarations. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. Compilation succeeds; there are no forbidden declarations, and the only `sorry`s are the two named split-off theorems, each documented and represented by a DAG node. Verdict: pass.
3. Reviewed the two split-off statements and their nodes. They are true intermediate claims, strictly smaller than the target, with the stated edge cases and source/search records; no duplicate declaration was found. Verdict: pass.
4. Traced the target proof downward. It uses the two split-off results, coherent cokernel closure, affine finite-presentation criteria, and stalk-surjectivity support arguments; exploratory and cyclic imports are absent. Verdict: pass.
5. Compared the main node's proof, dependencies, and origin with the Lean proof, and checked the two new node records and the unit route. They agree, and the unit route remains represented. Verdict: pass.

Changed during this second reading: added this section to satisfy the delivery contract; no Lean code or DAG statements were changed.
