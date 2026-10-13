## What changed
Proved `exists_coefficientTarget_tensor_decoder` without changing its signature.
The proof constructs the R-linear support map from `coefficientSupportIso`,
restricts scalars on an affine intersection section model, and composes with
Mathlib's `Algebra.IsPushout.cancelBaseChange`. Its generator equation follows
from the support inverse identity, the section model formula, and Mathlib's
`cancelBaseChange_tmul`.

Added three modules: `CoefficientIntersectionRingData` constructs the restricted
lift and the two structural ring maps explicitly, and proves the open containment;
`CoefficientIntersectionRingPushout` proves the ring pushout and scalar towers
from Mathlib's affine section pushout theorem; `CoefficientIntersectionSectionModel`
states the remaining affine pullback-section transport before ring cancellation.
No data are chosen from an unproved existence theorem.

## Proved and sorry left
Closed: `AlgebraicGeometry.Scheme.Modules.exists_coefficientTarget_tensor_decoder`
(the item's only hole). Also proved the new
`AlgebraicGeometry.Scheme.Modules.coefficientIntersection_le` and
`AlgebraicGeometry.Scheme.Modules.coefficientIntersection_ring_pushout`.

Added and left: `AlgebraicGeometry.Scheme.Modules.exists_coefficientIntersection_section_model`,
node `aux-pc-coefficient-intersection-section-model`. This is a decomposition:
one original hole closed and one smaller geometric hole added. The ring pushout,
scalar towers, support linearity, tensor contraction and final generator calculation
are proved; the pullback-section model remains to be proved.

## No longer needed
Removed direct proof imports `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
and `Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange` from the
item. They remain needed by the new section-model node, so neither module is
claimed as pruned from the targets' full import closure. No whole module is
known to become unreachable. All five old proof dependencies no longer used directly
by the decoder are: `lem-pc-finite-affine-cech-intersection-base-change`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-open-immersion-module-pullback-restriction`, and
`lem-weil-pbc-conjugate-iso-unit-equation`. The first two and the two adjunction
compatibility nodes are used by the section-model argument. The affine tilde/Gamma
node is used transitively by ModulePullbackAffineSections rather than directly.
The coefficient-comparison-map node remains a direct decoder dependency. The explicit affine tilde/Gamma and conjugate-unit
steps are now confined to the section-model proof rather than the final decoder.

## Where the brief, the DAG or earlier work was wrong
The supplied plan was mathematically sound, but did not expose the separation
between the affine ring pushout and the module-section transport. Mathlib already
proves the algebraic cancellation for a ring pushout, so no new balancing lemma
is needed. The unit route is unchanged: this is the affine coefficient computation
in part (a) of Picard coherence. Small cases checked: empty Z or B gives zero
intersection sections; no flatness, cover, or nonemptiness is used. The ring
pushout proof in fact does not require separatedness, though its interface keeps
the original hypothesis. The first exploratory equivalence restatement was
removed; it is not part of this delivery.

The project literature files are absent in this local checkout. The Stacks
sources for Tags 02KG, 01I9 and 01IA were read online, together with the pinned
Mathlib sources. An accidental attempt to invoke lean_file.sh through Python
failed before execution and was not used; all Lean compilation uses lcompile.py.

## New nodes
`def-pc-coefficient-intersection-ring-data`: real restricted lift, coefficient
base ring map, intersection ring map, and proved containment, in
`CoefficientIntersectionRingData.lean`.

`aux-pc-coefficient-intersection-ring-pushout`: the two scalar towers and ring
pushout, proved in `CoefficientIntersectionRingPushout.lean`.

`aux-pc-coefficient-intersection-section-model`: intersection-ring-linear map
into S tensor_D F(Z) and its unit formula, the one remaining hole in
`CoefficientIntersectionSectionModel.lean`. It neither identifies S with
R tensor_A D nor performs the tensor contraction of the original target.

## Second reading by M4

1. Compared every delivered source against the repository. Only the decoder already
   exists; its full declaration signature and docstring are byte for byte unchanged,
   and its only changes are proof imports and the proof body. The three other modules
   are new. No existing definition or target statement changed; no change record needed.
2. Compiled all four modules through lcompile.py. Exactly one named theorem contains
   sorry: `AlgebraicGeometry.Scheme.Modules.exists_coefficientIntersection_section_model`.
   Scratch-copy #print axioms checks show only propext, Classical.choice and Quot.sound
   for all four ring-data declarations and the ring-pushout theorem; the section-model
   theorem and decoder additionally show sorryAx, exactly as expected for the open
   section-model dependency. No other axiom occurs.
   No forbidden declarations, hidden holes, or witness choices in definitions occur.
   The restricted lift is a genuine pullback universal-property construction; ring maps
   are explicit appLE/composition constructions. The existential map is eliminated only
   within the decoder's proposition proof, never used to define public data.
3. Read the remaining theorem and its complete proof docstring against Stacks
   [01I9](https://stacks.math.columbia.edu/tag/01I9) and
   [01IA](https://stacks.math.columbia.edu/tag/01IA). Over affine charts the comparison
   is scalar extension; its inverse carries the pullback-unit section to 1 tensor s.
   The intersection is affine by the existing base-change theorem. For identity maps
   it reduces to D tensor_D N = N; for empty B or Z the intersection sections and
   tensor vanish, and for the zero module both sides vanish. No flatness needed.
   Independent leanfinder, loogle and grep searches using scalar extension,
   adjunction unit, TensorProduct.comm, and restrictFunctorIsoPullback located the
   existing affine-sections and adjunction ingredients, but no duplicate combined
   transport theorem. The new hole omits the ring-pushout identification and final
   A-to-R contraction: it is strictly the geometric section-transport part, not a
   restatement of the decoder. Completing that transport needs a substantial
   adjunction compatibility proof, not a few-minute application of one lemma.
4. Checked the support map's R-linearity, scalar towers and cancellation formula
   from the top down. Mathlib already handles the tensor cancellation, as used.
   No shorter existing decoder was found. All old proof dependencies are accounted
   for in No longer needed. The unit sk-thm-picard-coherence is untouched; its realized
   arrays are empty in the repository, an existing bookkeeping omission, not a route
   change. This split stays inside its existing affine coefficient computation.
5. Checked all four node signatures occur verbatim in their modules, each proof_deps
   equals the union of its proof-step uses, and source, proof_origin, created, blueprint,
   chapter, unit and search fields are present. The nodes describe the actual ring
   construction, pushout proof, section-model plan and decoder composition.

Repairs: removed the coefficient-comparison and IsTensorProduct public imports from
RingData, replacing them with the smaller GammaSpecAdjunction import actually needed
by its construction. Moved IsTensorProduct to RingPushout, whose public statement
needs Algebra.IsPushout. Added an explicit public coefficient-comparison import to
SectionModel, whose signature uses coefficientPullbackGenerator. Pruned the RingData
node's unrelated module/coefficient dependencies to scheme, morphism and pullback
conventions, and completed the old proof-dependency accounting above. No proof or
statement was rewritten. One original hole closed and one new hole added: net zero,
a decomposition, not a completely proved import closure. No whole module pruned.
