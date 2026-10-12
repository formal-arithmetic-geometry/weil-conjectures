## What changed

Replaced the sorry in HigherDirectImageLocalSectionVanishing with a complete Lean proof
using the scheme affine cover, transport through eK/hK/hη, and restriction naturality.
The covering sieve is explicitly Sieve.ofArrows of the affine cover. Every arrow in it
factors through an affine member, whose eventual-zero witness remains valid after restriction.
The original theorem signature and docstring are unchanged; no definitions changed.

Added HigherDirectImageAffineComputationVanishing for the canonical affine calculation.
It has neither the presentation K nor η, eK, hK, hη, nor a colimit of K as parameters.
Its hypotheses only describe the scheme/coefficient system and a canonical section.
Its docstring contains the complete source argument. Updated the parent DAG proof route.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.exists_higherDirectImage_local_section_eq_zero
(node lem-sbc-higher-direct-image-local-section-vanishing), by a proof from the new affine lemma.
No sorry remains in the assigned module.

Added: AlgebraicGeometry.Etale.exists_higherDirectImage_affine_computation_eq_zero
(node lem-sbc-higher-direct-image-affine-computation-vanishing), exactly `:= by sorry`.
This is a decomposition: one upper hole closed, one canonical affine hole added; no net hole
reduction is claimed. Affine-cover assembly, presentation transport, and restriction to every
arrow of the sieve are proved in Lean. Both modules compile without warnings.

Edge cases checked in the mathematical argument: degree zero is ordinary-section continuity;
empty affine objects have only the zero section; a singleton index is the identity comparison;
zero coefficients give zero higher images. No common stage over an infinite cover is assumed.
A finite subcover is used only inside the affine lemma. No arbitrary witness data or hollow
definition is introduced. The unit realized record has no entries for this local node; its
higher-direct-image limit route is retained, including the two original dependencies below
our new affine computation.

## No longer needed

Removed direct proof imports from the assigned module:
Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf and
Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit. They remain proof dependencies/imports
of the new affine computation, so neither module nor its node is transitively pruned.
No transitive nodes/modules pruned. Added the proof import
Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing and the Mathlib
AffineEtale import for the affine-cover infrastructure. Both original public imports stay.

## Where the brief, the DAG or earlier work was wrong

The previously stated cohomology-presheaf comparison only exposes an existential isomorphism;
its comparison maps and naturality are private. Continuity concerns complexes on absolute qcqs
schemes, so applying it here still requires relative affine base change, canonical-map
identification, and local lifting/injectivity. These are contained in the new affine lemma,
rather than claimed to follow by a direct application of the existential isomorphism.

The existing HigherDirectImageAffineSectionVanishing imports this assigned local theorem;
using it here would create an import cycle. Our affine computation is stated directly for
canonical higher images and does not import it. The new node explicitly records finite-cover
assembly as well as the original two mathematical dependencies. No statement is disputed.
Sources checked: Stacks Project [09Z1](https://stacks.math.columbia.edu/tag/09Z1),
[03Q8](https://stacks.math.columbia.edu/tag/03Q8), and
[0EZM](https://stacks.math.columbia.edu/tag/0EZM).

## New nodes

lem-sbc-higher-direct-image-affine-computation-vanishing: canonical section vanishing on an
affine etale object, in lean/Sheaf/AlgebraicGeometry/HigherDirectImageAffineComputationVanishing.lean.
This isolates the affine computation from the arbitrary-object covering-sieve assertion and
removes all auxiliary higher-image presentations from the remaining obligation.
No change records are needed: all existing signatures and definitions are unchanged.

## Second reading by K2

1. Compared the delivered local-section module with the repository version. The theorem
   signature and all existing declarations are unchanged; only proof imports and the proof
   body changed, as reported.
2. Compiled both delivered modules with `lcompile.py --all`; they compile without warnings.
   The local-section theorem has no `sorry`; the affine computation theorem is the one named
   split-off `sorry`, and its node and source docstring are present. No forbidden declarations
   or hollow definitions occur. The closed theorem uses only the permitted standard axioms
   plus the split affine theorem's `sorryAx`.
3. Checked the new affine statement against the Stacks 09Z1/03Q8/0EZM argument and its edge
   cases. It is a strict affine special case of the target, with no presentation or colimit of
   higher images, and is exactly the missing canonical computation needed by the proof.
   Repository and search checks found no duplicate declaration.
4. Read the proof downward: the affine-cover sieve construction, transport through `eK`,
   `hK`, and `hη`, and sieve-factor naturality are all explicit. The two cohomology continuity
   dependencies remain below the split affine node; removed imports are listed above. The unit
   route is retained; no transitive module can be pruned.
5. Checked the new node's Lean record against the declaration and its proof dependencies. The
   parent node now depends on the affine computation node, and the new node records the two
   underlying continuity/presheaf dependencies and the finite-cover assembly step.

No repair was needed in the delivered proofs or statements.
