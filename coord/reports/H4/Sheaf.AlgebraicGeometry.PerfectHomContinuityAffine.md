## What changed

Replaced the hole in `AlgebraicGeometry.perfect_hom_continuity_affine` by a proof from
`CochainComplex.affine_perfect_hom_colimit`, Mathlib's filtered-set colimit criteria,
and the new affine sheaf/module comparison
`AlgebraicGeometry.exists_affinePerfectHomPresentation`.

The proved private helper handles a fixed perfect pair on an affine scheme. It
sets up directed inhabited tails, obtains bijectivity of the presented Hom-colimit
map, lifts a limit morphism to a representative and moves it above the requested
stage. Injectivity and the filtered-set equality criterion give equality at one
later stage; functoriality propagates it to every later stage. The public theorem
identifies every open-immersion presentation of the affine open with that open and
applies the helper. Existing public signatures and public imports are unchanged.

The comparison theorem supplies bounded finite-projective module models, a
module-derived Hom functor and cocone, and sheaf Hom equivalences commuting with
the specified finite-stage and limit maps. It asserts no colimit property or
descent. Its source and detailed proof in words are in its docstring and new node.
The existing node now records the implemented reduction.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.perfect_hom_continuity_affine`
(node `lem-pc-perfect-hom-continuity-affine`) by decomposition. The item's module
contains no remaining `sorry`.

Added exactly one hole:
`AlgebraicGeometry.exists_affinePerfectHomPresentation`
(node `lem-pc-affine-perfect-hom-presentation`, new module
`Sheaf.AlgebraicGeometry.AffinePerfectHomPresentation`). This is steps 1 and 2 of
the original argument, not its continuity conclusion. The actual Hom-colimit
argument uses the existing proved theorem and the two continuity clauses are
proved in Lean. Thus this is a decomposition, not a net reduction of holes.
No definitions, axioms, targets or existing statements were changed.

Validation: `lcompile.py --all` compiled the affine comparison and the complete
continuity proof. A temporary byte-identical copy of the missing dependency
`PerfectHomContinuityOn` was removed from the sandbox before the final delivery
validation; it is not an adaptation or part of the delivery. The final
`deliver3.py H4 Sheaf.AlgebraicGeometry.PerfectHomContinuityAffine --no-push`
printed OK for commit `8af294863a`, compiling the intended delivery and passing
preflight except for the second reading, which the second reader supplies.
Nothing was pushed. The earlier missing-artifact failure no longer blocks this
dry run.

## No longer needed

Removed these direct proof imports from the item, relocating their planned use
to the comparison module:

- `Sheaf.AlgebraicGeometry.PerfectImpliesQCoh` /
  `lem-sc-perfect-qcoherent`.
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` /
  `lem-pc-affine-derived-pullback-tensor-tilde`.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` /
  `lem-pc-affine-qcoh-derived-equivalence`.
- `Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective` /
  `lem-pc-perfect-affine-bounded-projective`.

The item also no longer uses the composition-coherence theorem directly:
`lem-pc-ringed-spaces-derived-pullback-composition` and
`lem-pc-perfect-hom-transport` are used in the comparison theorem's plan. The
parent proof propagates equality by functoriality of the presented Hom functor.
These dependencies are relocated, not globally pruned. No module or node can be
claimed to leave the targets' closure. The ring Hom-colimit theorem remains used.

## Where the brief, the DAG or earlier work was wrong

The original affine model, pullback, and derived-equivalence signatures do not by
themselves expose a compatible sheaf/module Hom system on the actual tail, with
its canonical finite-stage and limit transports. This comparison was implicit in
steps 1 and 2 of the plan; the new theorem states precisely the missing part.
It does not replace the ring Hom-colimit theorem or assert either descent clause.

Mathlib searches were run through `msearch.py`: LeanFinder found affine scheme
section and morphism descent, not the sheaf-derived Hom comparison; Loogle's
namespace query had no hits; grep had no matching perfect Hom comparison.
LeanSearch was unavailable (Internal Server Error), which is recorded without a
mathematical absence verdict. Local searches found the affine models, equivalence,
pullback comparisons and the already proved ring Hom-colimit theorem.
The blueprint search found no matching imported node. The scheme-isomorphism derived equivalence, its preservation of quasi-coherence
and perfectness, and transport of open-site localizations are generic tools in
the comparison plan; they do not replace any unit step. The unit record
`sk-thm-picard-semicon` has empty realized lists, so no realized unit step is bypassed.

Sources checked online: Stacks Tags [09RE](https://stacks.math.columbia.edu/tag/09RE),
[08EB](https://stacks.math.columbia.edu/tag/08EB), and
[08DW](https://stacks.math.columbia.edu/tag/08DW). WANTED: the local copy of
`literature/stacks-project/perfect.tex`, these tags, for
`lem-pc-affine-perfect-hom-presentation`; the repository has no copy on this machine.
The formal packaging and glue are marked as written by an agent.

Edge cases checked: the tail and its second tail contain the base index; no
nonempty scheme or nonzero ring assumption is used. The zero object and zero ring
produce singleton Hom sets. A constant diagram recovers identity scalar extension.
Preorders need not be antisymmetric: proof irrelevance and subsingleton arrows,
not equality of indices, identify the arrows to the common later stage. Arbitrary
sheaf-derived Hom universe `w` is retained; module-derived categories are supplied
at the standard universe `u + 1`, and equivalences can compare different universes.
Existential presentation data are unpacked only in a proposition proof; no
public object is chosen from an unproved mere-existence theorem.

## New nodes

`lem-pc-affine-perfect-hom-presentation` records
`AlgebraicGeometry.exists_affinePerfectHomPresentation` in
`lean/Sheaf/AlgebraicGeometry/AffinePerfectHomPresentation.lean`. It isolates the
bounded-projective affine models and natural sheaf/module Hom comparison, retaining
all specified transport maps. Its three proof steps and docstring explain the
construction and compatibility, with no continuity assumption. No change record
is needed because every existing public interface is preserved.

## Second reading by H4

1. Compared the delivered target module with the repository version. The existing theorem statement and all existing declaration signatures are unchanged; the only interface addition is the separately documented split-off theorem and node.

2. Compiled both delivered modules with `lcompile.py --all`. The target has no remaining `sorry`; the sole remaining `sorry` is the named theorem `AlgebraicGeometry.exists_affinePerfectHomPresentation`, with its node and proof docstring. No forbidden declarations or hollow definitions were introduced.

3. Checked the split-off statement against its uses and edge cases. It supplies only the affine presentation data needed by the continuity proof and does not assert continuity or descent. The theorem is strictly smaller than the target and is not a restatement; its source, node, and detailed proof sketch are present.

4. Read the proof from the target downward. The main proof uses the existing affine Hom-colimit theorem and filtered-colimit criteria; the comparison theorem contains the previously implicit affine sheaf/module transport work. Removed direct imports are recorded under `## No longer needed`; the unit route remains unchanged and no realized unit step is bypassed.

5. Checked the DAG records against the Lean declarations. The target node records the implemented reduction and the new node records the exact split-off declaration, dependencies, source, and proof route. No statement or definition change record is required.

Changed in this second reading: appended this review section only; no Lean declarations or imports were changed.
