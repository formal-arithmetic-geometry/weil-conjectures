## What changed

Proved `CategoryTheory.exists_binaryCoverSitePresentation` by a direct sieve-site comparison,
small finite-limit closure, explicit ring-data inversion, and the specified localized nerves.
The original target-facing structure and theorem signature stay unchanged.

Extracted the two comparison data structures verbatim to BinaryPresentationModuleData,
publicly reexported by the original module. New proved modules establish the actual slice
Hom nerve (BinaryPresentationSliceNerve), ring/module localization with the fixed ring
`ring.over Z` (BinaryPresentationRingedSlices), and assembly plus invertibility of both
actual adjunction mates (BinaryPresentationSlices). No adopted source-tree file changed.

The ringed slices use the explicit product/fibre bijection. Zero, one, addition and
multiplication laws are proved by naturality and conjugation. The induced module direct
image is constructed by the existing ring-data module theorem; its inverse, exactness and
derived equivalence come from the existing ringed module Hom comparison. That existing
lemma remains a valid stated dependency of this stage.

## Proved and sorry left

Closed the item's one textual hole in `CategoryTheory.exists_binaryCoverSitePresentation`.
Added one hole, `CategoryTheory.exists_binaryPresentationRestrictionData`, node
`lem-sp-nerve-module-restriction-coherence`. This is a decomposition, net zero textual holes,
not a claim of a sorry-free proof closure. It states only coherent restriction/further
comparisons for fixed module equivalences on four subterminal slices, assuming the four
ordinary restriction squares which the delivery proves separately. It does not construct
the site, nerve, rings, module equivalences, derived equivalences or mates.

The other new public results, `exists_binaryPresentationSliceNerve`,
`exists_binaryPresentationRingedSlice`, and `exists_binaryPresentationSlices`, have complete
Lean proofs. No sorry is inside a definition or a private helper. All new definitions have
explicit data or use equivalences whose universal properties determine their objects.

Validation: server `lcompile.py --all` compiles the packet; final delivery preflight result
is recorded by deliver3. Each module is below the per-file limit. Edge cases checked in the
proof: arbitrary original sieve site, no original pullbacks, empty slice, repeated four
objects, empty subterminal, zero ring. The coherence lemma uses subterminality essentially
through the coreflective localization universal property.

## No longer needed

Removed private imports Sheaf.TraceFormula.SieveSheavesCoveringSite,
Sheaf.CategoryTheory.SiteOfSheafGenerators, Sheaf.CategoryTheory.RingedPresentationTransport,
WeilConjectures.CategoryTheory.SheafRingObjectReconstruction, and
Mathlib.CategoryTheory.Adjunction.Unique. The original public imports stay unchanged.

The proof no longer uses nodes lem-trf-sieve-sheaves-covering-site,
lem-weil-pbc-site-of-sheaf-generators, lem-weil-pbc-sheaf-ring-object-sectionwise-reconstruction,
lem-weil-pbc-ringed-presentation-transport, det-sp-unique-right-adjoint, or
lem-weil-pbc-conjugate-iso-unit-equation directly. It uses the comparison proof's arbitrary
Grothendieck-topology helpers, the smaller ringed module Hom result, and direct Hom-bijection
proofs for mates. The ring-transport dependency may still import ring reconstruction; this
packet makes no claim to remove that module from the entire target closure.

SmallSetOfCoveringFamilies, LocalizedSheavesOverRepresentable, ring transport and the
ringed sheaf slice adjunction remain used. The new ringed localization module uses proved
private RingedEquivalenceSlices APIs for conjugating ring operations and lifting a
compatible set square to a module square. No upstream declaration is removed or holed.
No globally pruned module is claimed without the maintainer's closure calculation.

## Where the brief, the DAG or earlier work was wrong

The initial plan's covering-site replacement is unnecessary: every construction in the
existing sheaf-subcategory comparison proof already works on an arbitrary sieve topology.
The public covering-family wrapper merely specializes it. I reuse those proved helpers
without changing their original source module or its public statement.

The blanket ringed-presentation transport result contains stronger internal-Hom and
local-test conclusions than this item's fields need. The exact module/derived part follows
from the smaller existing module comparison and Mathlib exact-equivalence machinery.

The previous natural-language claim that arbitrary localized comparison choices automatically
satisfy identity/composition requires a normalization argument. The remaining lemma spells
it out: restriction to a subterminal is a coreflective localization, so precomposition is
fully faithful and uniquely descends the further comparisons from the four given squares.
Its docstring contains that complete argument. The new statement is strictly smaller than
the original existence theorem and includes the actual component HEq equations.

## New nodes

`def-sp-binary-presentation-module-data`: verbatim relocation of the existing module and
adjunction-square comparison structures; no mathematical change.

`lem-sp-nerve-slice-equivalence`: the actual localized equivalence with its Hom formula;
proved using the existing localized-representable equivalence and full faithfulness.

`lem-sp-nerve-ringed-localization`: product/fibre ring transport to the fixed localized ring,
its exact module/derived equivalence and restriction square; complete proof.

`lem-sp-nerve-module-restriction-coherence`: one retained independent restriction-coherence
lemma for given equivalences on subterminal slices. It is the only new sorry.

`lem-sp-nerve-ringed-slice-comparisons`: assemble those results and prove the invertibility
of both actual adjunction mates by Hom bijections; complete proof.

Change record: coord/changes/binary-presentation-module-data.md.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
