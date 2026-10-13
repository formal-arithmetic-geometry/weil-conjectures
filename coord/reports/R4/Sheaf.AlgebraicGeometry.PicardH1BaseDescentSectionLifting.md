## What changed

Replaced the sole hole in
`AlgebraicGeometry.Scheme.picard_h1_base_descent_section_lifting` by a complete Lean proof
from a new finite-free cycle presentation and the existing
`Module.finiteFreeMap_residue_localization`. The original signature and public imports
are unchanged. Added proof imports of `PicardH1BaseDescentCyclePresentation` and
`Mathlib.LinearAlgebra.TensorProduct.Pi`; retained the residue-localization import.
The local heartbeat allowance is confined to this declaration; compilation takes about
16 seconds, within the single-file limit.

The proof localizes the joint degree-one map, applies its injectivity to the chain equation,
and computes each differential coefficient by `TensorProduct.piScalarRightHom`.
It represents the prescribed residue coefficient on an open inside the resulting basic
open, maps the localization to that open's section ring, and applies the cycle comparison.
This keeps the displayed canonical adjunction-unit equation and fibre coverage exactly.

## Proved and sorry left

Closed the original direct hole:
`AlgebraicGeometry.Scheme.picard_h1_base_descent_section_lifting`
(node `lem-sc-picard-h1-base-descent-section-lifting`). No direct sorry remains in the item.

Added one direct hole:
`AlgebraicGeometry.Scheme.picard_h1_base_descent_cycle_presentation`
(node `lem-sc-picard-h1-base-descent-cycle-presentation`), in the new module
`Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation`.
Its proof is exactly `by sorry`, with its source and full proof in the docstring.
This is a decomposition: one hole closed, one added, net zero. It is not an axiom-free
proof of the whole geometric argument. The remaining theorem supplies finite-free models
and their restriction-compatible cycle comparison; the item genuinely proves the later
minor-localization, differential-vanishing, and arbitrary residue-scalar lifting steps.
No definitions or axioms were added, and there are no arbitrary-witness definitions.

## No longer needed

Removed direct proof imports of
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` and
`Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel` from the item. They remain needed
by the cycle-presentation module, so this does not prune them from the target closure.
Their nodes `lem-pc-rf-perfect-base-change` and
`lem-sc-perfect-finite-free-residue-model` move to that module's proof dependencies.
The complete list removed from the item's old direct `proof_deps` is
`def-pc-base-change`, `def-pc-module-pullback`, `def-sc-invertible-module`,
`def-amb-finite-locally-free-module`, `lem-pc-rf-perfect-base-change`,
`lem-sc-perfect-finite-free-residue-model`, and `lem-pc-module-pullback-adjunction`.
All seven remain in the cycle-presentation node's dependencies (and the definitions
remain in the item's statement dependencies). No whole module or existing mathematical
node is claimed as pruned.
The original planned degree-zero-map determinant inversion is unnecessary for the
chain-equation step: target differentials are zero, so no invertibility of those chain-map
components is needed to deduce that the joint degree-one map annihilates the source vector.

## Where the brief, the DAG or earlier work was wrong

The original dependencies supply separate perfectness, finite-free models, and rank criteria,
but their interfaces do not supply the comparison between degree-zero cycles and the
specific canonical section-restriction expression. This is stated explicitly in the new node.
Representing arrows between the fixed affine models also needs the existing
`lem-pc-perfect-affine-map-representative`; its module is now imported by the new module.
There is no statement change or forced adaptation.

Read Stacks Tag 0BF2 at https://stacks.math.columbia.edu/tag/0BF2: the finite-free models,
chain maps, degree-one minor, and vanishing-differential argument. The repository's
`literature/stacks-project/more-morphisms.tex` is absent on this machine, so the source
was read from the official Stacks page. The unit's realized arrays are empty; the route
still uses its multiple-Picard-locus perfect-complex argument and bypasses no unit step.

Edge cases: when the source degree-one rank is zero, the tensor-coefficient conclusion is
vacuous and the same localization lemma applies. For an empty family, H1 injectivity forces
that rank to vanish; no target factor is selected. The given w rules out an empty base,
and universal structure pushforward rules out an empty marked source or target fibre.
The zero prescribed section is handled by the same residue/germ argument. Non-affine bases
cause no issue: the cycle presentation may choose an affine U, and germ representation
allows a further arbitrary open V contained in its basic open.

Mathlib searches were run with msearch and are logged in searches.jsonl: LeanSearch was
unavailable (HTTP internal-server error), LeanFinder returned sheaf local-injectivity and
section-extensionality facts but no geometric lifting theorem, Loogle returned the residue
field morphism API, and grep found exists_le_germ_eq and piScalarRightHom_tmul. Local
searches found the downstream Picard statements, which import this item and cannot be used
without a cycle. The new lemma is not a renamed lifting theorem: it only realizes scalars
that satisfy a differential-cycle equation, and asserts neither that the differential is
zero near w nor that all residue coefficients lift.

## New nodes

`lem-sc-picard-h1-base-descent-cycle-presentation` records the finite-free degree-zero
vector, joint degree-one map with injective residue base change, fibre coefficient
equivalence, and cycle-realization comparison on smaller opens. It stops before
localization and scalar lifting. Its module is
`lean/Sheaf/AlgebraicGeometry/PicardH1BaseDescentCyclePresentation.lean`.
The source is Tag 0BF2; the proof uses the existing perfect direct-image, finite-free
residue-model, and affine chain-map representative nodes. There are no change records.

## Second reading by R4

1. Compared the complete existing module with the repository using `diff -u`, then
   compared its theorem signature byte for byte. Verdict: unchanged signature, unchanged
   public imports and visibility; no definition or target statement changes, and no change
   record is needed. The only new declaration is the documented presentation theorem.
2. Compiled both delivered modules in import order using `lcompile.py --all`: clean,
   about 10 and 18 seconds. Reviewed every proof step: injectivity kills the tensor of d,
   coordinate evaluation kills each localized coefficient, the basic-open restriction
   factors through localization, and germ representation gives the required residue
   scalar. The canonical restriction expression is retained. Scratch copies with
   `#print axioms` check both declarations; only the three permitted axioms and `sorryAx`
   occur. The only delivered sorry is the named presentation theorem; there are no
   definitions, prohibited declarations, or arbitrary-witness definitions.
3. Read the new presentation theorem and its docstring against Stacks Tag 0BF2
   (https://stacks.math.columbia.edu/tag/0BF2). Verdict: true and a strictly earlier part
   of the argument. Universal structure pushforward rules out empty residue fibres;
   faithful flatness makes the descended finite locally free modules rank one. Minimal
   residue models have zero negative terms, a rank-one degree-zero term, and zero
   residue differentials. Trivial target sections have nonzero degree-zero coefficient,
   so after shrinking their differential is zero. Different choices of fibre generators
   scale the H1 maps by units and preserve joint injectivity. The chain identity therefore
   gives b d = 0 before any localization of b. Degree-zero cycles restrict naturally on
   arbitrary smaller opens: exact open restriction computes H0 of the direct image,
   and the canonical base-change comparison computes their fibre coefficients.
   The fibre inclusion and pullback-composition isomorphism supply the required j and e.
   Rank-zero and empty-family cases are vacuous in degree one, and zero sections lift.
   No geometric hypotheses were silently added. The remaining theorem cannot be closed
   in a few minutes from the existing derived-category interfaces. Independent searches
   with LeanFinder (perfect direct image and degree-zero cycles), Loogle (evaluation),
   and grep (injective base change and basic-open units), plus local Sheaf/upstream
   searches, found component APIs but no existing presentation theorem. Downstream
   Picard lifting results import this item and cannot supply a shorter route.
4. Verdict: the proof carries out the finite-free residue localization and scalar-germ
   lifting itself, so it is a genuine decomposition, not an application of a renamed
   conclusion. Both added proof imports are private; the new module's public tensor
   and residue imports occur in its signature. The three geometric proof imports in
   that module carry its documented unfinished proof plan. Checked the old and new
   dependency lists and completed `No longer needed` with all seven removed direct
   dependencies. None is pruned from the closure. Read `dag/units/sk-prop-av-cube.json`:
   its realized statement and step arrays are empty; this decomposition retains the
   perfect-complex Picard argument below that unit and changes no unit record or route.
5. Verdict: both node `lean.statement` strings match their declarations exactly;
   the existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   Its three proof dependencies match the actual reduction. The new node has source,
   natural-language proof, dependency union, search records, creation metadata,
   blueprint ancestry, chapter, unit, and the complete Lean record required by the brief.
   The new theorem's docstring explains its construction and compatibility comparisons.

Second reading changed only review documentation: completed the direct-dependency
pruning inventory and recorded these independent checks. No mathematical repair was
needed; the delivered result remains one original hole closed, one hole split off,
net zero, with no whole module pruned.
